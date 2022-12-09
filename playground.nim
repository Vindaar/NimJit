## This is the first example from the `libgccjit` documentation here:
## https://gcc.gnu.org/onlinedocs/jit/intro/tutorial01.html

import libgccjit
import typetraits


import std / [macros, genasts, sets, tables, options]
import system / ansi_c


from std/sequtils import concat
proc flatten[T: not seq](a: seq[T]): seq[T] = a
proc flatten[T: seq](a: seq[T]): auto =  a.concat.flatten

type
  FnParams = seq[(string, NimNode)]

  ## A type storing the symbols for a given type
  JitType = ref object
    name: string # the name as a string of this type
    typ: ptr gcc_jit_type
    struct: ptr gcc_jit_struct # if it corresponds to a struct
    `fields`: Table[string, ptr gcc_jit_field]

  JitContext = ref object # ref object as it stores pointers, so copying by value doesn't make a lot of sense
    ctx: ptr gcc_jit_context
    # and further fields for the storage of information that stores
    # things like `gcc_jit_struct` and `gcc_jit_fields` associated.
    types: Table[string, JitType]

  Context = ref object
    fn: NimNode # the current function
    varCount: int # counter of variables for a custom gensym of sorts
    params: FnParams # the JIT paramaters associated with the function arguments
    blckStack: seq[NimNode] # stack of the current blocks
    nextCallRvalue: bool # determines if the next `nnkCall` encountered must be generated
                         # as an RValue, instead of discarded (add `*_add_eval` or not)
    seenFns: HashSet[string] ## set of symbols that were already jit'ed
    hasExplicitReturn: bool ## marks a return statement to know if we still need to terminate


proc initJitType(name: string): JitType =
  result = JitType(name: name,
                   typ: nil,
                   struct: nil,
                   `fields`: initTable[string, ptr gcc_jit_field]())

proc head[T](s: seq[T]): T =
  ## Returns the `head` of the sequence, if `s` is a stack like structure, where
  ## the `head` refers to the *last* element (for efficient adding & popping)
  result = s[^1]

proc push[T](s: var seq[T], el: T) =
  ## pushes the element `el` to the stack
  s.add el

proc high(n: NimNode): int = n.len - 1

## can we create a Nim macro that generates JIT code?
proc toJitType(s: string): gcc_jit_types =
  case s
  of "void": result = GCC_JIT_TYPE_VOID
  of "pointer": result = GCC_JIT_TYPE_VOID_PTR
  of "bool": result = GCC_JIT_TYPE_BOOL
  of "char", "cchar": result = GCC_JIT_TYPE_CHAR
  of "uchar" : result = GCC_JIT_TYPE_UNSIGNED_CHAR
  of "cschar" : result = GCC_JIT_TYPE_SIGNED_CHAR
  of "int16", "cshort": result = GCC_JIT_TYPE_SHORT
  of "uint16", "cushort": result = GCC_JIT_TYPE_UNSIGNED_SHORT
  of "int32", "cint": result = GCC_JIT_TYPE_INT
  of "uint32", "cuint": result = GCC_JIT_TYPE_UNSIGNED_INT
  of "clong": result = GCC_JIT_TYPE_LONG
  of "culong" : result = GCC_JIT_TYPE_UNSIGNED_LONG
  of "int", "int64", "clonglong": result = GCC_JIT_TYPE_LONG_LONG ## only int if sizeof(int) == 8
  of "uint64", "culonglong": result = GCC_JIT_TYPE_UNSIGNED_LONG_LONG
  of "float32": result = GCC_JIT_TYPE_FLOAT
  of "float64": result = GCC_JIT_TYPE_DOUBLE
  # of "float64" : result = GCC_JIT_TYPE_LONG_DOUBLE
  of "string", "cstring", "ptr char", "cstringArray": result = GCC_JIT_TYPE_CONST_CHAR_PTR ## XXX: probably not?
  of "csize_t": result = GCC_JIT_TYPE_SIZE_T
  of "File" : result = GCC_JIT_TYPE_FILE_PTR
  of "Complex[float32]": result = GCC_JIT_TYPE_COMPLEX_FLOAT
  of "Complex[float]", "Complex[float64]": result = GCC_JIT_TYPE_COMPLEX_DOUBLE
  #of "Complex[float64]": result = JIT_TYPE_COMPLEX_LONG_DOUBLE
  of "varargs[typed]": result = GCC_JIT_TYPE_CONST_CHAR_PTR ## XXX: HACK!!!
  else:
    doAssert false, "Not supported yet! " & $s
    result = GCC_JIT_TYPE_VOID

proc toJitInfix[T](s: string, typ: typedesc[T]): gcc_jit_binary_op =
  when T is SomeInteger:
    let s = if s in ["and", "or"]: s & "I"
            else: s
  case s
  of "+": result = GCC_JIT_BINARY_OP_PLUS
  of "-": result = GCC_JIT_BINARY_OP_MINUS
  of "*": result = GCC_JIT_BINARY_OP_MULT
  of "/": result = GCC_JIT_BINARY_OP_DIVIDE
  of "mod": result = GCC_JIT_BINARY_OP_MODULO
  of "and": result = GCC_JIT_BINARY_OP_BITWISE_AND ## XXX: how to differentiate? Needs to be done via types
  of "xor": result = GCC_JIT_BINARY_OP_BITWISE_XOR
  of "or": result = GCC_JIT_BINARY_OP_BITWISE_OR
  of "andI": result = GCC_JIT_BINARY_OP_LOGICAL_AND
  of "orI": result = GCC_JIT_BINARY_OP_LOGICAL_OR
  of "shl": result = GCC_JIT_BINARY_OP_LSHIFT
  of "shr": result = GCC_JIT_BINARY_OP_RSHIFT
  else:
    doAssert false, "not supported yet " & $s
    result = GCC_JIT_BINARY_OP_PLUS

proc toJitInfixBool(s: string): gcc_jit_comparison =
  case s
  of "==": result = GCC_JIT_COMPARISON_EQ
  of "!=": result = GCC_JIT_COMPARISON_NE # XXX: does this remain in typed AST?
  of "<":  result = GCC_JIT_COMPARISON_LT
  of "<=": result = GCC_JIT_COMPARISON_LE
  of ">":  result = GCC_JIT_COMPARISON_GT
  of ">=": result = GCC_JIT_COMPARISON_GE
  else:
    doAssert false, "Not supported yet " & $s
    result = GCC_JIT_COMPARISON_EQ

proc toJitInfix(n: NimNode): NimNode =
  ## Given a typed infix node, return the correct JIT infix node, taking into account
  ## duplicate names, by appending a suffix for integers
  doAssert n.kind == nnkInfix
  let op = n[0].strVal
  if op in ["==", "!=", "<", "<=", ">", ">="]:
    result = genAst(op = newLit(op)):
      toJitInfixBool(op)
  else:
    let typ = n[1].getType
    result = genAst(op = newLit(op), typ):
      toJitInfix(op, type(typ))

template toJitType(typ: typed): gcc_jit_types =
  astToStr(typ).toJitType()

proc toJitType[T](jitCtx: JitContext, typ: typedesc[T]): ptr gcc_jit_type =
  when T is object:
    # generatet the correct struct
    ## XXX: handle variant types using tagged union! See my notes!
    var jitFields = newSeq[ptr gcc_jit_field]()
    # I fear we have to return the `gcc_jit_field` as well for use later.
    ## NOTE: libgccjit of later versions have a function to retrieve a struct field
    ## by index! However this is not available on version 10 yet.
    ## So what is the solution? In addition we may need the struct information. So better
    ## split objects and types.
    ## But then how to deal with `toJitType` calls returning different things? Same for
    ## `toParam`.
    ## Difficult, but there's probably a neat solution out there in the ether...
    ## The Emacs JIT compiler handles it by having a global `comp` object, which stores the
    ## fields for all the relevant Emacs objects. Of course the same isn't possible for our
    ## code, but proves we need to keep the fields around.
    ## Imo that means the `Context` field must be extended to store this information for us.
    let typName = $T
    if typName in jitCtx.types:
      result = jitCtx.types[typName].typ
    else:
      ## Generate the JitType that stores all the pointers for later lookup and construct
      ## the `struct`. Note that currently only flat objects of basic types are supported!
      var jitType = initJitType(typName)

      for field, val in fieldPairs(default(T)):
        let jitField = jitCtx.ctx.gcc_jit_context_new_field(
          nil,
          jitCtx.toJitType(type(val)),
          field
        )
        jitType.`fields`[field] = jitField
        jitFields.add jitField

      let struct = jitCtx.ctx.gcc_jit_context_new_struct_type(
        nil,
        typName,
        jitFields.len.cint,
        jitFields[0].addr
      )
      jitType.struct = struct
      result = gcc_jit_struct_as_type(struct)
      jitType.typ = result
      jitCtx.types[typName] = jitType
  else:
    jitCtx.ctx.gcc_jit_context_get_type(toJitType($T))

#proc toJitType[T](jitCtx: JitContext, typ: typedesc[T]): (Table[string, ptr gcc_jit_field], ptr gcc_jit_type) =
#  jitCtx.ctx.gcc_jit_context_get_type(toJitType($T))

proc toParam[T](jitCtx: JitContext, typ: typedesc[T], name: string): ptr gcc_jit_param =
  jitCtx.ctx.gcc_jit_context_new_param(nil, jitCtx.toJitType(typ), name)

proc toRValue(jitCtx: JitContext, val: string{lit}): ptr gcc_jit_rvalue =
  jitCtx.ctx.gcc_jit_context_new_string_literal(val)

proc toRValue(jitCtx: JitContext, val: cstring): ptr gcc_jit_rvalue =
  jitCtx.ctx.gcc_jit_context_new_string_literal(val)

proc toRValue(val: ptr gcc_jit_param): ptr gcc_jit_rvalue =
  gcc_jit_param_as_rvalue(val)

proc toRValue(jitCtx: JitContext, val: ptr gcc_jit_param): ptr gcc_jit_rvalue =
  # version ignoring context
  gcc_jit_param_as_rvalue(val)

proc toRValue(val: ptr gcc_jit_lvalue): ptr gcc_jit_rvalue =
  gcc_jit_lvalue_as_rvalue(val)

proc toRValue(jitCtx: JitContext, val: ptr gcc_jit_lvalue): ptr gcc_jit_rvalue =
  # version ignoring the context
  gcc_jit_lvalue_as_rvalue(val)

# no-op
proc toRValue(jitCtx: JitContext, val: ptr gcc_jit_rvalue): ptr gcc_jit_rvalue = val

proc toRValue[T: not openArray](jitCtx: JitContext, val: T): ptr gcc_jit_rvalue =
  when T is SomeInteger:
    when sizeof(T) <= 4:
      jitCtx.ctx.gcc_jit_context_new_rvalue_from_int(jitCtx.toJitType(typeof(val)), val.cint)
    else:
      jitCtx.ctx.gcc_jit_context_new_rvalue_from_long(jitCtx.toJitType(typeof(val)), val.clonglong)
  elif T is SomeFloat:
    jitCtx.ctx.gcc_jit_context_new_rvalue_from_double(jitCtx.toJitType(typeof(val)), val.cdouble)
  elif T is bool:
    jitCtx.ctx.gcc_jit_context_new_rvalue_from_int(jitCtx.toJitType(typeof(val)), if val: 1.cint else: 0.cint)
  elif T is ptr gcc_jit_rvalue:
    val # no-op
  #elif T is string:
  #  ctx.
  #elif T is openArray:
  #  doAssert val.len == 1
  #  ctx.toRValue(val[0])
  else:
    doAssert false, "Type " & $T & " is not supported yet."

#proc toRValue[N: static int; T](jitCtx: JitContext, val: array[N, T]): array[N, ptr gcc_jit_rvalue] =
#  result = default(array[N, ptr gcc_jit_rvalue])
#  for i, ch in val:
#    result[i] = ctx.toRValue(ch)

proc toRValue[T: string](jitCtx: JitContext, val: openArray[T]): seq[ptr gcc_jit_rvalue] =
  result = newSeq[ptr gcc_jit_rvalue](val.len)
  for i, ch in val:
    result[i] = jitCtx.toRValue(ch)

#proc toRValue[T](jitCtx: JitContext, val: T): ptr gcc_jit_rvalue =

#proc toRValue[T](jitCtx: JitContext, val: T): ptr gcc_jit_rvalue =

proc getFieldAsRValue[T](jitCtx: JitContext, obj: ptr gcc_jit_rvalue, typ: typedesc[T], field: string): ptr gcc_jit_rvalue =
  ## returns the field `field` of the given `obj`, assuming it's of type `typ`.
  doAssert $T in jitCtx.types, "The type " & $T & " does not exist in the JitContext types!"
  let jitTyp = jitCtx.types[$T]
  let fld = jitTyp.`fields`[field]
  result = gcc_jit_rvalue_access_field(obj, nil, fld)

proc addReturn(blck: ptr gcc_jit_block) =
  gcc_jit_block_end_with_void_return(blck, nil)

proc addReturn[T](jitCtx: JitContext, blck: ptr gcc_jit_block, res: T) =
  gcc_jit_block_end_with_return(blck, nil, jitCtx.toRValue(res))

proc addReturn(ctx: Context, res: NimNode): NimNode =
  let blck = ctx.blckStack.head()
  if res.kind == nnkEmpty:
    result = genAst(blck):
      addReturn(blck)
  else:
    result = genAst(blck, res):
      JitCtx.addReturn(blck, res)

proc newFunction[T](jitCtx: JitContext, name: string,
                    retType: typedesc[T],
                    params: seq[ptr gcc_jit_param],
                    functionKind: gcc_jit_function_kind,
                    isVariadic = false): ptr gcc_jit_function =
  #var params = newSeq[ptr gcc_jit_param]()
  #for f, v in fields(params):
  #  params.add ctx.toParam(typeof(v), f)
  let variadic = if isVariadic: 1.cint else: 0.cint
  let paramsAddr = if params.len == 0: nil else: params[0].addr
  jitCtx.ctx.gcc_jit_context_new_function(nil,
                                   functionKind,
                                   jitCtx.toJitType(retType), # return type
                                   name,
                                   params.len.cint, paramsAddr,
                                   variadic)

proc newContextCall(jitCtx: JitContext, fn: ptr gcc_jit_function,
                    args: seq[ptr gcc_jit_rvalue]): ptr gcc_jit_rvalue =
  let numArgs = args.len
  jitCtx.ctx.gcc_jit_context_new_call(nil,
                                      fn,
                                      numArgs.cint, args[0].addr)

proc addEval(blck: ptr gcc_jit_block, contextCall: ptr gcc_jit_rvalue) =
  ## Adds an evaluation to the given `blck` with the given `contextCall`, which
  ## should be the result of a call to `newContextCall`
  gcc_jit_block_add_eval(blck, nil, contextCall)

proc newBinaryOp[T; U; V; W](jitCtx: JitContext,
                             op: T,
                             resType: typedesc[U],
                             aJ: V, bJ: W): ptr gcc_jit_rvalue =
  when T is gcc_jit_comparison:
    jitCtx.ctx.gcc_jit_context_new_comparison(nil, op, jitCtx.toRValue(aJ), jitCtx.toRValue(bJ))
  elif T is gcc_jit_binary_op:
    jitCtx.ctx.gcc_jit_context_new_binary_op(nil, op, jitCtx.toJitType(type(resType)),
                                      jitCtx.toRValue(aJ),
                                      jitCtx.toRValue(bJ))
  else:
    doAssert false, "not supported and does not make sense " & $T

template setupContext(): untyped {.dirty.} =
  var JitCtx = JitContext()
  var res: ptr gcc_jit_result

  # Get a "context" object for working with the library.  */
  JitCtx.ctx = gcc_jit_context_acquire()
  if JitCtx.ctx.isNil:
    echo "nil JitCtx"
    return 1

  # Set some options on the context.
  #  Let's see the code being generated, in assembler form.  */
  gcc_jit_context_set_bool_option(
    JitCtx.ctx,
    GCC_JIT_BOOL_OPTION_DUMP_GENERATED_CODE,
    0)


template withRValue(ctx: Context, body: untyped): untyped {.dirty.} =
  ctx.nextCallRvalue = true
  body
  ctx.nextCallRvalue = false

proc toImpl(fn: NimNode): NimNode =
  case fn.kind
  of nnkSym: result = fn.getImpl
  of nnkProcDef: result = fn
  else: doAssert false, "not supported yet " & $fn.kind

macro fnName(t: typed): untyped =
  ## Returns the name of the given function
  let fnImp = t.toImpl
  result = fnImp.name

macro fnRetType(t: typed): untyped =
  ## Returns the name of the given function
  let fnImp = t.toImpl
  result = fnImp.params[0]

#macro fnParams(t: typed): untyped =
#  ## Returns the name of the given function
#  let fnImp = t.toImpl
#  let params = fnImp.params
#  for i in 1 ..< params.len:
#    echo params[i].treerepr

#template toJitFn[T: proc](ctx: JitContext, fn: T, functionKind: gcc_jit_function_kind): ptr gcc_jit_function =
#  fnParams(fn)
#  ctx.newFunction(astToStr(fn), fnRetType(fn),
#  5
#  #result = ctx.newFunction(fnName(fn), fnRetType(fn), @jitBr, fnKind, isVariadic = variadic)

proc greet2(name: cstring): void = # {.jit.} =
  let x = "cant believe".cstring
  c_printf("hello freaking wowza %s %s\n", x, name)

proc createCode(jitCtx: JitContext) =
  #[ Let's try to inject the equivalent of:
     void
     greet (const char *name)
     {
        printf ("hello %s\n", name);
     }
  ]#
  #let voidType = gcc_jit_context_get_type(ctx, toJitType(void))
  #let const_char_ptr_type = gcc_jit_context_get_type(ctx, toJitType(ptr char))
  let param_name = jitCtx.toParam(ptr char, "name")
  let fn = jitCtx.newFunction("greet", void, @[param_name], GCC_JIT_FUNCTION_EXPORTED)
  #let fn = ctx.toJitFn(greet2, GCC_JIT_FUNCTION_EXPORTED)

  let param_format = jitCtx.toParam(ptr char, "format")
  let printf_func = jitCtx.newFunction("printf", int32, @[param_format],
                                       GCC_JIT_FUNCTION_IMPORTED,
                                       isVariadic = true)
  let args = [jitCtx.toRValue("hello %s\n"), gcc_jit_param_as_rvalue(param_name)]

  ## Add the body to the function
  let blck = gcc_jit_function_new_block(fn, nil)
  ## evaluate the body
  gcc_jit_block_add_eval(
    blck, nil,
    gcc_jit_context_new_call(jitCtx.ctx,
                             nil,
                             printf_func,
                             2, args[0].addr))
  ## define the end of the block
  gcc_jit_block_end_with_void_return(blck, nil)

proc genParam(n, name, typ: NimNode): NimNode =
  result = genAst(name = name, n = n.strVal, typ = typ):
    let name = JitCtx.toParam(type(typ), n)

proc genParamName(n: NimNode): NimNode =
  result = ident(n.strVal & "_PARAM")

# {.experimental: "dynamicBindSym".}
proc isParam(n: NimNode, jitParams: seq[(string, NimNode)]): bool =
  case n.kind
  of nnkSym, nnkIdent:
    for (name, p) in jitParams:
      if name == n.strVal: return true
  else:
    result = false
proc getParam(n: NimNode, jitParams: seq[(string, NimNode)]): NimNode =
  case n.kind
  of nnkSym, nnkIdent:
    for (name, p) in jitParams:
      if name == n.strVal: return p
  else:
    doAssert false, "Cannot happen"

proc getParamOpt(n: NimNode, jitParams: seq[(string, NimNode)]): Option[NimNode] =
  case n.kind
  of nnkSym, nnkIdent:
    for (name, p) in jitParams:
      if name == n.strVal: return some(p)
  else:
    result = none(NimNode)

proc generateBody(ctx: Context, body: NimNode): NimNode
proc buildArgs(ctx: Context, n: NimNode): NimNode =
  result = nnkBracket.newTree()
  for i in 1 ..< n.len: # skip 0, the call itself
    # if something is an argument of the function, need to convert
    var rval: NimNode
    let paramOpt = getParamOpt(n[i], ctx.params)
    if paramOpt.isSome:
      let param = paramOpt.get
      rval = genAst(p = param):
        toRValue(p)
      result.add rval
    else:
      let argCall = ctx.generateBody(n[i]) # getVarName(n[i])
      ## Might return a `nnkBracket`, but that should be fine!
      rval = genAst(arg = argCall):
        JitCtx.toRValue(arg)
      result.add rval

proc newLocal(ctx: Context, ident: NimNode): NimNode =
  let name = ident[0].strVal
  let lval = ctx.generateBody(ident[0])
  let typ  = ident[2].getType
  ## `rval` has to be "treated" (might be a call for example)
  withRValue(ctx):
    let rval = ctx.generateBody(ident[2])
  result = genAst(lval, fn = ctx.fn, typ, name, rval, blck = ctx.blckStack.head):
    let lval = gcc_jit_function_new_local(fn, nil, JitCtx.toJitType(type(typ)), name)
    # now assign rval to lval
    gcc_jit_block_add_assignment(blck, nil,
                                 lval,
                                 JitCtx.toRValue(rval))

proc newBlock(ctx: Context, name: string, fn: NimNode): NimNode =
  let varBlockName = ident(name)
  ctx.blckStack.push varBlockName
  result = genAst(blck = varBlockName, fn = fn, name = name):
    let blck = gcc_jit_function_new_block(fn, name.cstring)

proc generateBody(ctx: Context, body: NimNode): NimNode =
  ## XXX: would have to generate blocks before hand so we can actually jump!
  case body.kind
  of nnkIdent, nnkSym:
    let paramOpt = getParamOpt(body, ctx.params)
    if paramOpt.isSome:
      result = ident(body.strVal & "_PARAM")
    elif body.strVal in ["true", "false"]:
      result = body
    else:
      result = ident(body.strVal & "_LVALUE")
  of nnkLiterals, nnkConv: result = body # `literals` will be wrapped by `toRValue`, which makes it safe
  of nnkHiddenStdConv:
    ## XXX: in case of `nnkBracket` stored, refers to a `varargs`, need to be flattened
    ## and returned as N arguments. Likely function already indicated as variadic?
    case body[1].kind
    of nnkLiterals: result = body
    of nnkIdent, nnkSym: result = ctx.generateBody(body[1])
    of nnkBracket:
      result = nnkBracket.newTree() #newStmtList()
      for ch in body[1]:
        result.add ctx.generateBody(ch)
    of nnkDotExpr: result = ctx.generateBody(body[1])
    else: doAssert false, "not supported " & $body.treerepr
  of nnkCommand, nnkCall:
    # perform a call
    # Note: this implies it is of `void` return type, otherwise we
    # would have seen let / var / asgn
    # 1. first a new block
    let fnCall = ident(body[0].strVal & "_SYMBOL")
    let args = ctx.buildArgs(body)
    ## XXX: thanks to discardable we can't use `geType` to determine if we need `add_eval`
    if not ctx.nextCallRvalue:
      result = genAst(args, fnCall, blck = ctx.blckStack.head):
        addEval(blck, JitCtx.newContextCall(fnCall, flatten(@args)))
    else:
      result = genAst(args, fnCall, blck = ctx.blckStack.head):
        JitCtx.newContextCall(fnCall, flatten(@args))
  of nnkStmtListExpr, nnkStmtList:
    ## XXX: if `expr` need to return something in theory!! only `printf` returns int that is discardable
    result = newStmtList()
    for stmt in body:
      result.add ctx.generateBody(stmt)
  of nnkLetSection:
    result = newStmtList()
    for ident in body:
      result.add ctx.newLocal(ident)
  of nnkReturnStmt:
    # return the given value
    doAssert body[0].kind == nnkAsgn, "Weird, return isn't asgn ? " & $body.treerepr
    ctx.hasExplicitReturn = true
    # return the child [1]
    let resVar = body[0][1]
    let resJitVal = ctx.generateBody(resVar)
    result.add ctx.addReturn(resJitVal)
  of nnkInfix:
    ## generate an infix RVALUE
    let op = toJitInfix(body)
    let resType = getType(body)
    let aJ = ctx.generateBody(body[1])
    let bJ = ctx.generateBody(body[2])
    result = genAst(op, resType, aJ, bJ):
      JitCtx.newBinaryOp(op, type(resType), aJ, bJ)
  of nnkDiscardStmt: ## This would imply throwing away the `rvalue` of this expression
    result = ctx.generateBody(body[0]) ## XXX: what should this really do? for now just ignore
  of nnkEmpty:
    result = body
  of nnkIfStmt, nnkIfExpr: ## XXX: same distinction as stmtListExpr and stmtList!
    result = newStmtList()
    proc jumpDown(ctx: Context): NimNode =
      let down = ctx.blckStack.pop() # current
      let head = ctx.blckStack.head() # target
      result = genAst(head, down):
        gcc_jit_block_end_with_jump(head, nil, down)

    proc jumpTo(ctx: Context, to: NimNode): NimNode =
      let this = ctx.blckStack.head()
      result = genAst(this, to):
        gcc_jit_block_end_with_jump(this, nil, to)

    proc jump(ctx: Context, frm, to: NimNode): NimNode =
      result = genAst(frm, to):
        gcc_jit_block_end_with_jump(frm, nil, to)

    proc jumpWithCond(ctx: Context, condNode: NimNode): NimNode = #ifStmt, cond, ifTrue, ifFalse: NimNode) =
      let ifFalse = ctx.blckStack.pop()
      let ifTrue = ctx.blckStack.pop()
      # head is now `ifStmt` condition, so generate the code
      let cond = ctx.generateBody(condNode)
      let ifStmt = ctx.blckStack.head()
      result = genAst(cond, ifStmt, ifTrue, ifFalse):
          gcc_jit_block_end_with_conditional(ifStmt, nil,
                                             JitCtx.toRValue(cond),
                                             ifTrue, # if true, jump to body
                                             ifFalse)

    ## Note: The idea to generate the correct jumps for an if are as follows:
    ## We start with the block in which the `if` resides as head of the block stack.
    ## Generate the block for *after* the if, pop it and store it in a variable.
    ## Then:
    ## 1. walk all if statements and generate:
    ##   - blocks for if condition (unless `else`), if body, adding to block stack
    ##   - generate code for the if body
    ##   - generate jump from if body to after the block
    ## 2. add the after if block back to the block stack. This makes sure the block
    ##     stack is in reverse order of: (`ifFalse, ifTrue, ifCond`) blocks.
    ## 3. now need to generate correct jumps for conditionals. Walk if statements
    ##     in reverse order and:
    ##   - if an `else` branch (seen first), pop the `afterIf` block, as the
    ##      `ifFalse` for the if condition must jump to `else`
    ##   - if an `elif` branch, generate the conditional jump by popping from the
    ##      block stack, yielding (`ifFalse, ifTrue, ifCond`) jumps
    ## 4. after loop, finaly generate the initial jump from the current block to the
    ##     first if condition.
    ## 5. block stack now only contains previous state as before loop. Pop the
    ##     head & add the `afterIf` to continue from there.

    # generate the after if block and pop it (needs to be at head of block stack later)
    result.add ctx.newBlock("afterIf_" & ctx.fn.strVal, ctx.fn)
    let afterIfBlck = ctx.blckStack.pop()
    var idx = 0
    # now walk if statements & generate blocks and body code (but not condidion code!)
    for ifBr in body:
      if ifBr.kind == nnkElifBranch:
        result.add ctx.newBlock("ifCond_" & $idx & "_" & ctx.fn.strVal, ctx.fn)
      let blckName = if ifBr.kind == nnkElifBranch: "ifBody_" else: "elseBody_"
      result.add ctx.newBlock(blckName & $idx & "_" & ctx.fn.strVal, ctx.fn)
      # generate the corresponding code for the body
      result.add ctx.generateBody(ifBr[ifBr.high]) # last child contains body
      # add the jump to after the block
      result.add ctx.jumpTo(afterIfBlck)
    # add after block again so it's the head of the block stack
    ctx.blckStack.add afterIfBlck
    # walk in reverse order and generate the correct conditional jumps
    for i in countdown(body.len-1, 0):
      let ifBr = body[i]
      case ifBr.kind
      of nnkElifBranch: result.add ctx.jumpWithCond(ifBr[0])
      of nnkElse:
        # else branch implies need to pop `afterIf` so that `ifFalse` of the
        # previous if condition jumps to `else` instead of `after`
        discard ctx.blckStack.pop()
      else: doAssert false, $ifBr.kind
    # finally generate the jump call to from the `currentBlck` to the first if condition
    result.add ctx.jumpDown()
    doAssert ctx.blckStack.len == 1
    discard ctx.blckStack.pop() # pop the initial current block
    ctx.blckStack.add afterIfBlck # add the after block as the new base block
  of nnkDotExpr:
    ## XXX: need to know if this is an lvalue or an rvalue!
    let xS = ctx.generateBody(body[0])
    result = genAst(x = xS, sym = body[0], fieldName = body[1].strVal):
      JitCtx.getFieldAsRValue(JitCtx.toRValue(x), type(sym), fieldName)
  #of nnkForStmt:
  #  echo body.treerepr
  #
  #  doAssert false
  of nnkCommentStmt: result = body ## just keep them as is
  else:
    doAssert false, "notsupported yet " & $body.kind

proc jitFn*(fn: NimNode, functionKind: gcc_jit_function_kind, setupContext = false): NimNode

## XXX: implement `echo` by importing `echoBinSafe`, which has signature
## `proc echoBinSafe(x: array[string], numArgs: int)`
## or something like that
#proc echoJit(): NimNode =
#  let params = @[JitCtx.toParam(type(ptr cstring), "x"),
#                 JitCtx.toParam(type(cint), "num")] # number of elements in array
#  let fnS = JitCtx.newFunction("echoBinSafe", type(void), params, GCC_JIT_FUNCTION_IMPORTED, isVariadic = false)


proc jitCalledFns(ctx: Context, n: NimNode): NimNode =
  ## NOTE: This could become a pre pass that also registers the kind of returns
  ## as well as checks for what kind of code flow we have?
  result = newStmtList()
  if n.kind in {nnkCall, nnkCommand}:
    let nStr = n[0].strVal
    if nStr notin ctx.seenFns:
      if n[0].strVal in ["foo"]: ## XXX: DETERMINE BASED ON IMPORTC?
        result.add jitFn(toImpl(n[0]), GCC_JIT_FUNCTION_EXPORTED)
      else:
        result.add jitFn(toImpl(n[0]), GCC_JIT_FUNCTION_IMPORTED)
      ctx.seenFns.incl nStr
    # else nothing to do
  for stmt in n:
    let res = ctx.jitCalledFns(stmt)
    if res.len > 0:
      result.add res

proc hasPragma(fn: NimNode, pragma: string): bool =
  let pragmas = fn[4]
  for p in pragmas:
    var pName = ""
    case p.kind
    of nnkExprColonExpr: pName = p[0].strVal
    of nnkIdent: pName = p.strVal
    else: doAssert false, "not possible"
    if pName == pragma: return true

proc getPragmaValue(fn: NimNode, pragma: string): NimNode =
  let pragmas = fn[4]
  for p in pragmas:
    case p.kind
    of nnkExprColonExpr:
      if p[0].strVal == pragma: return p[1]
    of nnkIdent: doAssert false, "Ident pragmas have no value!"
    else: doAssert false, "not possible"

proc getName(fn: NimNode): string =
  ## Returns the name of the function, possibly taking into account and `importc` pragma
  if fn.hasPragma("importc"):
    result = fn.getPragmaValue("importc").strVal
  else:
    result = fn.name.strVal

proc jitFn*(fn: NimNode, functionKind: gcc_jit_function_kind, setupContext = false): NimNode =
  let params = fn.params
  echo "============================== ", fn.treerepr
  # 1. generate params
  result = newStmtList()
  var ctx = Context()
  if setupContext:
    result.add getAst(setupContext())
  let retParam = if params[0].kind == nnkEmpty: ident("void") else: params[0]
  var jitParams = newSeq[(string, NimNode)]()
  var anyArgumentVarargs = false
  for i in 1 ..< params.len: # skip 0, return, will be used later
    let p = params[i]
    let pType = p[params.len - 1] # second to last is return type
    ## XXX: handle `varargs` and conversions of the types used by `echo`, `varargs[typed, $]`
    ## where the latter argument implies the actual type via a call
    if pType.kind == nnkBracketExpr and pType[0].strVal == "varargs":
      anyArgumentVarargs = true
    for j in 0 ..< p.len - 2: # get all parameter names
      let paramName = genParamName(p[j])
      jitParams.add (p[j].strVal, paramName)
      result.add genParam(p[j], paramName, pType)
  ctx.params = jitParams
  # 2. generate the function
  let fnName = fn.getName()
  let fnSymbolName = fn.name.strVal
  let fnS = ident(fnSymbolName & "_SYMBOL")
  ctx.fn = fnS
  var jitBr = nnkBracket.newTree()
  for p in jitParams:
    jitBr.add p[1]
  let isVariadic = fn.hasPragma("varargs") or anyArgumentVarargs
  let fnDef = genAst(fnS, fnName, retParam, jitBr, fnKind = functionKind, variadic = isVariadic):
    let fnS = JitCtx.newFunction(fnName, type(retParam), @jitBr, fnKind, isVariadic = variadic)
  result.add fnDef
  if functionKind == GCC_JIT_FUNCTION_IMPORTED: # return early if import
    return
  # 3. for any function in body, get the body
  #    and recurse
  ## XXX: not only AST top level of course!
  let body = fn.body
  result.add ctx.jitCalledFns(body)
  # 4. generate body of this procedure to be evaluated
  # 4a. generate the block of code for the body
  ## Generate the block for the body & add it to our stack of blocks
  result.add ctx.newBlock("blck_body_" & fnSymbolName, fnS)
  # result.add varBlock
  result.add ctx.generateBody(body)
  if not ctx.hasExplicitReturn:
    ## XXX: change this to automatically return `result` varialbe instead of void!
    result.add ctx.addReturn(newEmptyNode())

  let dump = genAst(fnS, fnName):
    gcc_jit_function_dump_to_dot(fnS, "/tmp/test.dot")
  #result.add dump
  echo "============================== JIT FN", result.repr

macro jit*(fn: typed): untyped =
  echo "--------------------------------------------------------"
  echo fn.treerepr, "^^^^^^^^^^^"
  result = jitFn(toImpl(fn), GCC_JIT_FUNCTION_EXPORTED, setupContext = true)

proc greet(name: cstring): void =
  let x = "cant believe".cstring
  let y = 5
  c_printf("hello freaking wowza %s %s %i\n", x, name, y)

proc foo(a, b: int): int = return a + b

#proc print
template print(args: varargs[untyped]): untyped = c_printf(args)

type
  Bar = object
    x: int
    y: int
    s: cstring

proc greetInt(name: cstring): int = # {.jit.} =
  # Note: types like `string` work due to auto conversion of string->cstring?
  let x = "cant believe" #.cstring
  let y = 5
  let a = true
  let b = 8 >= y
  if b:
    print "hello freaking wowza %s %s %i and 5>y? %i \n", x, name, y, b
  else:
    #discard c_printf("unfortunately not allowed to print, condition 5>y not held\n")
    #discard # 5
    let w = 1

  ## XXX: this gives redefiniton errors currently! Gensym our variables!
  ## One issue: mapping later symbols to earlier ones! If we gensym naively
  ## we will generate the wrong symbols in later usages!
  ## Currently mainly the generated `args` are affected. Do we even need to
  ## generate them?
  print "hello\n"

  #for i in 0 ..< 3:
  # let els = [1, 2, 3]
  #for i in els:
  #  print("%i ", i)

  let z = foo(1, y + 2)
  let z2 = 2 * z
  return z

proc handBar(b: Bar) =
  print("%i and %i with the name: %s\n", b.x, b.y, b.s)

proc test(): int =
  echo("hello", " world")

import std/syncio
proc main(): int =

  #setupContext()
  #
  ## Populate the context.  */
  #create_code(ctx)
  #jit(greetInt)
  #jit(test)
  jit(handBar)

  # Compile the code.  */
  res = gcc_jit_context_compile(JitCtx.ctx)
  if res.isNil:
    echo "nil result"
    return 1
  # Extract the generated code from "result".
  type
    fnType = proc(c: cstring) {.nimcall.}
    fnTypeNone = proc(): clonglong {.nimcall.}
    fnTypeInt = proc(c: cstring): clonglong {.nimcall.}
    fnTypeBar = proc(c: Bar) {.nimcall.}
  when false:
    var greet = cast[fnType](gcc_jit_result_get_code(res, "greet"))
    if greet.isNil:
      echo "nil greet"
      return 1
    # Now call the generated function: */
    greet("world")
  elif false:
    var greetInt = cast[fnTypeInt](gcc_jit_result_get_code(res, "greetInt"))
    if greetInt.isNil:
      echo "nil greetInt"
      return 1
    # Now call the generated function: */
    echo "Funtion returns: ", greetInt("world")
  elif true:
    var handBar = cast[fnTypeBar](gcc_jit_result_get_code(res, "handBar"))
    if handBar.isNil:
      echo "nil handBar"
      return 1
    # Now call the generated function: */
    let bar = Bar(x: 5, y: 10, s: "world")
    handBar(bar)
  else:
    var test = cast[fnTypeNone](gcc_jit_result_get_code(res, "test"))
    if test.isNil:
      echo "nil test"
      return 1
    # Now call the generated function: */
    echo "Funtion returns: ", test()
  stdout.flushFile()

  gcc_jit_context_release(JitCtx.ctx)
  gcc_jit_result_release(res)

when isMainModule:
  echo main()
