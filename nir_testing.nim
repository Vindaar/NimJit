## Nir Compiler.

import compiler / nir / [nirinsts, nirtypes, nirlineinfos, nirfiles, cir]
import compiler / ic / [bitabs, rodfiles]

import std / [tables, strutils, os, intsets]
import libgccjit

import ./jit_types

proc head[T](s: seq[T]): T =
  ## Returns the `head` of the sequence, if `s` is a stack like structure, where
  ## the `head` refers to the *last* element (for efficient adding & popping)
  result = s[^1]

proc head[T](s: var seq[T]): var T =
  ## Returns the `head` of the sequence, if `s` is a stack like structure, where
  ## the `head` refers to the *last* element (for efficient adding & popping)
  result = s[^1]

proc push[T](s: var seq[T], el: T) =
  ## pushes the element `el` to the stack
  s.add el

proc push(s: var seq[ptr gcc_jit_block], el: JitNode) =
  ## pushes the element `el` to the stack
  doAssert el.kind == jtBlock
  s.add el.blck

type
  FnParams = seq[(string, JitNode)]
  #               ^--- name of parameter
  #                       ^--- ptr gcc_jit_param
  #                                ^--- PNode of the type used to construct the param
  #                                       ^--- PNode of the parameter itself

  Function = ref object
    fnSym: string # the name of the symbol (may be different for imported functions)
    isVariadic: bool
    functionKind: gcc_jit_function_kind
    fn: JitNode # node representing a `ptr gcc_jit_function`
    retType: JitNode # return type of the function
    params: FnParams # arguments and their types

  JittedCode = object
    m: NirModule # The current module we compile
    main: NirModule # The main module we compile (might not be the current)
    mods: Table[string, NirModule] # other modules we may look into
    path: string ## Path to the directory of the input file
    ctx: ptr gcc_jit_context
    #types: Table[TypeId, JitType]
    types: Table[string, JitType] ## XXX: I'd like to use a `TypeId` as key, but the same type appears with different ids?
    globals: Table[SymId, JitNode]
    locals: Table[SymId, JitNode] ## XXX: Locals should be (per block or) per function!
    blckStack: seq[JitNode]
    fnTab: Table[SymId, Function] ## maps each function by string name to its JitNode (from `jitFn`)
    stack: seq[Function] ## current function stack. Head points at function being processed atm
    generatedTypes: IntSet ## Keeps track of which types have been generated yet

proc setupContext(): JittedCode =
  result = JittedCode()
  # Get a "context" object for working with the library.  */
  result.ctx = gcc_jit_context_acquire()
  if result.ctx.isNil:
    doAssert false, "nil JitCtx"

  # Set some options on the context.
  #  Let's see the code being generated, in assembler form.  */
  gcc_jit_context_set_bool_option(
    result.ctx,
    GCC_JIT_BOOL_OPTION_DUMP_GENERATED_CODE,
    0)

proc initJittedCode(file: string): JittedCode =
  result = setupContext()
  result.path = file.parentDir ## We need the parent dir to load data from other `.nir` files `ModuleSymUse`!
  result.m = load(file)
  result.main = result.m

proc view(filename: string) =
  ## From `nirc.nim`
  let m = load(filename)
  var res = ""
  allTreesToString m.code, m.lit.strings, m.lit.numbers, m.symnames, res
  res.add "\n# TYPES\n"
  nirtypes.toString res, m.types
  echo res

proc debug(c: JittedCode; t: TypeId) =
  var buf = ""
  toString buf, c.m.types, t
  echo buf

proc debug(c: JittedCode, t: Tree, n: NodePos) =
  var buf = ""
  toString(t, n, c.m.lit.strings, c.m.lit.numbers, c.m.symnames, buf)
  echo buf

proc newFunction(fnSym: string,
                 retType: JitNode,
                 functionKind: gcc_jit_function_kind): Function =
  result = Function(fnSym: fnSym,
                    retType: retType,
                    functionKind: functionKind,
                    params: @[], #initFnParams(),
                    fn: initJitNode(jtEmpty))

proc newFunction(c: JittedCode,
                 fn: Function): JitNode =
  let variadic = if fn.isVariadic: 1.cint else: 0.cint
  var jitParams = newSeq[ptr gcc_jit_param]()
  for p in fn.params:
    jitParams.add p[1].param
  let paramsAddr = if jitParams.len == 0: nil else: jitParams[0].addr
  #debug "Generating new function with arguments: ", fn.params.repr
  result = toJitNode(
    c.ctx.gcc_jit_context_new_function(
      nil,
      fn.functionKind,
      toPtrType(fn.retType), # return type
      fn.fnSym,
      jitParams.len.cint, paramsAddr,
      variadic)
  )

proc newArrayType(c: JittedCode, typ: JitNode, num: int): JitNode =
  result = toJitNode(
      c.ctx.gcc_jit_context_new_array_type(
        nil,
        toPtrType(typ),
        num.cint),
      ""
    )

proc newType(c: JittedCode, typ: gcc_jit_types): JitNode =
  echo "WITH::::: ", typ
  result = toJitNode gcc_jit_context_get_type(c.ctx, typ)

proc newPointer(typ: JitNode): JitNode =
  result = toJitNode gcc_jit_type_get_pointer(toPtrType typ)

proc newBlock(c: var JittedCode, name: string, fn: JitNode): JitNode =
  ## XXX: turn into runtime version returning the code!
  doAssert fn.kind == jtFunction
  result = toJitNode(gcc_jit_function_new_block(toPtrFunction(fn), name.cstring), name)
  c.blckStack.push result

proc toJitInfix(s: OpCode): gcc_jit_binary_op =
  case s
  of Add, CheckedAdd:    result = GCC_JIT_BINARY_OP_PLUS
  of Sub, CheckedSub:    result = GCC_JIT_BINARY_OP_MINUS
  of Mul, CheckedMul:    result = GCC_JIT_BINARY_OP_MULT
  of Div, CheckedDiv:    result = GCC_JIT_BINARY_OP_DIVIDE
  of Mod, CheckedMod:    result = GCC_JIT_BINARY_OP_MODULO
  of BitAnd: result = GCC_JIT_BINARY_OP_BITWISE_AND
  of BitXor: result = GCC_JIT_BINARY_OP_BITWISE_XOR
  of BitOr:  result = GCC_JIT_BINARY_OP_BITWISE_OR
  of BitShl: result = GCC_JIT_BINARY_OP_LSHIFT
  of BitShr: result = GCC_JIT_BINARY_OP_RSHIFT
  else: raiseAssert "UNSPPORTED " & $s
  #of "andI": result = GCC_JIT_BINARY_OP_LOGICAL_AND
  #of "orI":  result = GCC_JIT_BINARY_OP_LOGICAL_OR

#  of BitNot: binaryop " ~ "
#  of BoolNot: binaryop " !"
#  of Eq: cmpop " == "
#  of Le: cmpop " <= "
#  of Lt: cmpop " < "
#  of Cast: binaryop ""
#

proc toJitType[T: SomeNumber](c: JittedCode, val: T): JitNode =
  when T is SomeUnsignedInt:
    when sizeof(T) == 1:  result = newType(c, GCC_JIT_TYPE_UNSIGNED_CHAR)
    elif sizeof(T) == 2: result = newType(c, GCC_JIT_TYPE_UNSIGNED_SHORT)
    elif sizeof(T) == 4: result = newType(c, GCC_JIT_TYPE_UNSIGNED_INT)
    elif sizeof(T) == 8: result = newType(c, GCC_JIT_TYPE_UNSIGNED_LONG_LONG)
    else: raiseAssert "unreachable"
  elif T is SomeInteger:
    when sizeof(T) == 1:  result = newType(c, GCC_JIT_TYPE_SIGNED_CHAR)
    elif sizeof(T) == 2: result = newType(c, GCC_JIT_TYPE_SHORT)
    elif sizeof(T) == 4: result = newType(c, GCC_JIT_TYPE_INT)
    elif sizeof(T) == 8: result = newType(c, GCC_JIT_TYPE_LONG_LONG)
    else: raiseAssert "unreachable"
  else:
    when sizeof(T) == 4:  result = newType(c, GCC_JIT_TYPE_FLOAT)
    elif sizeof(T) == 8:  result = newType(c, GCC_JIT_TYPE_DOUBLE)
    elif sizeof(T) == 16: result = newType(c, GCC_JIT_TYPE_LONG_DOUBLE)
    else: raiseAssert "unreachable"

proc toRValue[T: SomeNumber](c: JittedCode, typ: JitNode, val: T): ptr gcc_jit_rvalue =
  when T is SomeInteger:
    when sizeof(T) <= 4:
      result = c.ctx.gcc_jit_context_new_rvalue_from_int(typ, val.cint)
    else:
      result = c.ctx.gcc_jit_context_new_rvalue_from_long(
        toPtrType(typ), val.clonglong
      )
  else:
    result = c.ctx.gcc_jit_context_new_rvalue_from_double(
      toPtrType(typ), val.cdouble
    )

proc toRValue[T: SomeNumber](c: JittedCode, val: T): ptr gcc_jit_rvalue =
  result = c.toRValue(c.toJitType(val), val)

proc toRValue(val: ptr gcc_jit_param): ptr gcc_jit_rvalue =
  gcc_jit_param_as_rvalue(val)

proc toRValue(c: JittedCode, val: ptr gcc_jit_param): ptr gcc_jit_rvalue =
  # version ignoring context
  gcc_jit_param_as_rvalue(val)

proc toRValue(val: ptr gcc_jit_lvalue): ptr gcc_jit_rvalue =
  gcc_jit_lvalue_as_rvalue(val)

proc toRValue(c: JittedCode, val: ptr gcc_jit_lvalue): ptr gcc_jit_rvalue =
  # version ignoring the context
  gcc_jit_lvalue_as_rvalue(val)

proc toRValue*(c: JittedCode, val: JitNode): ptr gcc_jit_rvalue =
  case val.kind
  of jtLValue: result = c.toRValue(val.lval)
  of jtRValue: result = val.rval
  of jtParam:  result = toRValue(val.param)
  else: doAssert false, "Node of kind " & $val.kind & " cannot be turned into an RValue"

#proc toRValue*[T: string](c: JittedCode, val: openArray[T]): seq[ptr gcc_jit_rvalue] =
#  result = newSeq[ptr gcc_jit_rvalue](val.len)
#  for i, ch in val:
#    result[i] = c.toRValue(ch)

proc toLValue*(val: JitNode): ptr gcc_jit_lvalue =
  case val.kind
  of jtLValue: result = val.lval
  of jtParam: result = gcc_jit_param_as_lvalue(val.param)
  else: doAssert false, "Node of kind " & $val.kind & " cannot be turned into an LValue"

proc toParam(c: JittedCode, typ: ptr gcc_jit_type, name: string): ptr gcc_jit_param =
  c.ctx.gcc_jit_context_new_param(nil, typ, name)

proc toParam(c: JittedCode, typ: JitNode, name: string): JitNode =
  result = toJitNode(c.ctx.gcc_jit_context_new_param(nil, toPtrType(typ), name), name)

proc newField(c: JittedCode, val: JitNode, field: string): JitNode =
  let ptrTyp = toPtrType(val)
  result = toJitNode(
    c.ctx.gcc_jit_context_new_field(
      nil,
      ptrTyp,
      field),
    $field
  )

proc newStruct(c: JittedCode, typName: string, jitFields: seq[ptr gcc_jit_field]): JitNode =
  doAssert jitFields.len > 0, "cannot be empty"
  result = toJitNode(
    c.ctx.gcc_jit_context_new_struct_type(
        nil,
        typName,
        jitFields.len.cint,
        jitFields[0].addr
      )
  )


proc mapObjectToType(c: JittedCode, types: TypeGraph, t: TypeId): JitNode =
  ## Maps the given `TypeId` to the correct libgccjit pointer type.
  ## NOTE: This means the type must have been generated previously!
  debug c, t
  echo "with id: ", t.int
  #if t notin c.types:
  #  for k, v in c.types:
  #    echo k.int
  #    debug c, k

  #let name = if types[t].kind == ArrayTy: arrayName(types, t) else: t.firstSon
  let litId = types[t].litId
  #let symId = c.m.code[].symId
  #let name = c.m.symnames[SymId t.int]
  #echo "NAME:::: ", name, " = ", c.m.lit.strings[name]
  let s {.cursor.} = c.m.lit.strings[litId]

  if s notin c.types:
    for k, v in c.types:
      echo "KEYYYYYYYYYY ", k, " checking? ", s
      #debug c, k

  doAssert s in c.types
  result = toJitNode c.types[s].typ

proc genType(c: JittedCode; types: TypeGraph; lit: Literals; t: TypeId; name = ""): JitNode =
  case types[t].kind
  of VoidTy: result = newType(c, GCC_JIT_TYPE_VOID)
  of IntTy:
    case types[t].integralBits
    of 8:  result = newType(c, GCC_JIT_TYPE_SIGNED_CHAR)
    of 16: result = newType(c, GCC_JIT_TYPE_SHORT)
    of 32: result = newType(c, GCC_JIT_TYPE_INT)
    of 64: result = newType(c, GCC_JIT_TYPE_LONG_LONG)
    else: raiseAssert "unreachable"
  of UintTy:
    case types[t].integralBits
    of 8:  result = newType(c, GCC_JIT_TYPE_UNSIGNED_CHAR)
    of 16: result = newType(c, GCC_JIT_TYPE_UNSIGNED_SHORT)
    of 32: result = newType(c, GCC_JIT_TYPE_UNSIGNED_INT)
    of 64: result = newType(c, GCC_JIT_TYPE_UNSIGNED_LONG_LONG)
    else: raiseAssert "unreachable"
  of FloatTy:
    case types[t].integralBits
    of 32:  result = newType(c, GCC_JIT_TYPE_FLOAT)
    of 64:  result = newType(c, GCC_JIT_TYPE_DOUBLE)
    of 128: result = newType(c, GCC_JIT_TYPE_LONG_DOUBLE)
    else: raiseAssert "unreachable"
  of BoolTy: result = newType(c, GCC_JIT_TYPE_BOOL)
  of CharTy: result = newType(c, GCC_JIT_TYPE_CHAR)
  of ObjectTy, UnionTy, NameVal, AnnotationVal:    ## XXX: What are `NameVal` and `AnnotationVal`?
    result = mapObjectToType(c, types, t)
  of APtrTy, UPtrTy, AArrayPtrTy, UArrayPtrTy:
    let e = genType(c, types, lit, elementType(types, t)) # element type
    result = newPointer e
  of ArrayTy:
    let e = genType(c, types, lit, arrayName(types, t))
    let n = arrayLen(types, t)
    result = newArrayType(c, e, n)
  of LastArrayTy:
    let e = genType(c, types, lit, elementType(types, t))
    result = newArrayType(c, e, 0)
  of ProcTy:
    let (retType, callConv) = returnType(types, t)
    let rt = genType(c, types, lit, retType)
    #genType c, types, lit, callConv
    #g.add Star # "(*fn)"
    #maybeAddName()
    #var i = 0
    #for ch in params(types, t):
    #  if i > 0: g.add Comma
    #  genType c, types, lit, ch
    #  inc i
  #of "csize_t": result = newType(c.ctx, GCC_JIT_TYPE_SIZE_T)
  #of "file" : result = newType(c.ctx, GCC_JIT_TYPE_FILE_PTR)
  #of "Complex[float32]": result = newType(c.ctx, GCC_JIT_TYPE_COMPLEX_FLOAT)
  #of "Complex[float]", "Complex[float64]": result = newType(c.ctx, GCC_JIT_TYPE_COMPLEX_DOUBLE)
  #of "Complex[float64]": result = newType(c.ctx, JIT_TYPE_COMPLEX_LONG_DOUBLE)
  #of "varargs[typed]": result = newType(c.ctx, GCC_JIT_TYPE_CONST_CHAR_PTR) ## XXX: HACK!!!
  else:
    doAssert false, "Not supported yet! " & $types[t].kind
    #result = GCC_JIT_TYPE_VOID
  # Set the name if given
  if name.len > 0:
    result.name = name

#proc genType(g: var JittedCode; types: TypeGraph; lit: Literals; t: TypeId; name = "") =
#  template maybeAddName =
#    if name != "":
#      g.add Space
#      g.add name
#
#  template atom(s: string) =
#    g.add s
#    maybeAddName()
#  case types[t].kind
#  of VoidTy: atom "void"
#  of IntTy: atom "NI" & $types[t].integralBits
#  of UIntTy: atom "NU" & $types[t].integralBits
#  of FloatTy: atom "NF" & $types[t].integralBits
#  of BoolTy: atom "NB" & $types[t].integralBits
#  of CharTy: atom "NC" & $types[t].integralBits
#  of ObjectTy, UnionTy, NameVal, AnnotationVal:
#    atom lit.strings[types[t].litId]
#  of VarargsTy:
#    g.add "..."
#  of APtrTy, UPtrTy, AArrayPtrTy, UArrayPtrTy:
#    genType g, types, lit, elementType(types, t)
#    g.add Star
#    maybeAddName()
#  of ArrayTy:
#    genType g, types, lit, arrayName(types, t)
#    maybeAddName()
#  of LastArrayTy:
#    genType g, types, lit, elementType(types, t)
#    maybeAddName()
#    g.add BracketLe
#    g.add BracketRi
#  of ProcTy:
#    let (retType, callConv) = returnType(types, t)
#    genType g, types, lit, retType
#    g.add Space
#    g.add ParLe
#    genType g, types, lit, callConv
#    g.add Star # "(*fn)"
#    maybeAddName()
#    g.add ParRi
#    g.add ParLe
#    var i = 0
#    for ch in params(types, t):
#      if i > 0: g.add Comma
#      genType g, types, lit, ch
#      inc i
#    g.add ParRi
#  of ObjectDecl, UnionDecl:
#    atom lit.strings[types[t.firstSon].litId]
#  of IntVal, SizeVal, AlignVal, OffsetVal, FieldDecl:
#    #raiseAssert "did not expect: " & $types[t].kind
#    g.add "BUG "
#    atom $types[t].kind

#proc genSymDef(c: var JittedCode; t: Tree; n: NodePos) =
#  if t[n].kind == SymDef:
#    let symId = t[n].symId
#    c.needsPrefix.incl symId.int
#    genDisplayName c, symId
#  gen c, t, n
#
proc gen(c: var JittedCode, t: Tree, n: NodePos): JitNode

proc genDisplayName(c: JittedCode; symId: SymId): string =
  let displayName = c.m.symnames[symId]
  if displayName != LitId(0):
    result = c.m.lit.strings[displayName]

proc genGlobal(c: var JittedCode; t: Tree; name, typ: NodePos; annotation: string): JitNode =
  var kind: gcc_jit_global_kind
  #if sfImportc in n.sym.flags:
  #  kind = GCC_JIT_GLOBAL_IMPORTED
  #else:
  #  kind = GCC_JIT_GLOBAL_EXPORTED
  kind = GCC_JIT_GLOBAL_EXPORTED ## XXX: IMPORTED == `ModuleSymUse`?
  doASsert t[name].kind == SymDef, "IS: " & $t[name].kind
  let symId = t[name].symId
  let symName = genDisplayName(c, symId) ## XXX: SHOULD be `m`?
  let jt = c.genType(c.m.types, c.m.lit, t[typ].typeId, symName)
  result = toJitNode(
    c.ctx.gcc_jit_context_new_global(
      nil,
      kind,
      toPtrType jt,
      symName)
  )
  c.globals[symId] = result

proc genNumberConv(c: var JittedCode; t: Tree; n: NodePos): JitNode =
  let (typ, arg) = sons2(t, n)
  if t[arg].kind == IntVal:
    let litId = t[arg].litId
    let jt = gen(c, t, typ)
    case c.m.types[t[typ].typeId].kind
    of UIntTy:
      let x = cast[uint64](c.m.lit.numbers[litId])
      result = toJitNode c.toRValue(jt, x)
    of FloatTy:
      let x = cast[float64](c.m.lit.numbers[litId])
      result = toJitNode c.toRValue(jt, x)
    else:
      result = gen(c, t, arg)
  else:
    raiseAssert "Unsupported"
    #binaryop ""

proc assign(c: JittedCode, lvalue, rvalue: JitNode) =
  ## Performs assignment of an `rvalue` to an `lvalue`
  ##
  ## `lvalue = rvalue`
  case rvalue.kind
  of jtSeq: ## trying to assign an array, do element by element
    ## This code branch is for what normally should be handling of `nkBracket`
    raiseAssert "Unsupported"

    # what we will do instead, as we don't have that yet:
    # 1. use array access to set each element from `ar` in a loop
    # 3. return rvalue of the local array
    # we could optimize the case where this appears in an assignment and just
    # use the lvalue instead of a temp variable. for now easier this way
    #for i, el in pairs(rvalue.sons):
    #  c.assign(c.access(lvalue, i), el)
  else:
    gcc_jit_block_add_assignment(toPtrBlock(c.blckStack.head()), nil,
                                 lvalue.toLValue(),
                                 c.toRValue(rvalue))

proc newLocal(c: JittedCode, typ: JitNode, name: string): JitNode =
  ## Generates a new local variable of the given type from the identifier `ident`
  echo "type ? ", typ
  let local = gcc_jit_function_new_local(toPtrFunction(c.stack.head.fn), nil, toPtrType typ, name)
  result = toJitNode(local)

#proc newLocalAsgn(c: JittedCode, ident: PNode): JitNode =
#  # generate a new local variable of the nodes type
#  let typ = if ident[2].kind != nkEmpty: ident[2]
#            else: ident[0] # instead use type of symbol
#  result = c.newLocal(c.toJitType(typ), ident[0].getName())
#  ## `rval` has to be "treated" (might be a call for example)
#  if ident[2].kind != nkEmpty:
#    withRValue(c):
#      let rval = c.genNode(ident[2])
#    # now assign rval to lval
#    echo "RVAL: ", rval
#    c.assign(result, rval)
#  # else this was a `var` section *without* an initialization

proc genLocal(c: var JittedCode; t: Tree; name, typ: NodePos; annotation: string): JitNode =
  assert t[name].kind == SymDef
  let symId = t[name].symId
  let jt = genType(c, c.m.types, c.m.lit, t[typ].typeId, "q" & $symId)
  let n = genDisplayName(c, symId)
  result = c.newLocal(jt, n)
  c.locals[symId] = result

proc newBinaryOp[T](c: JittedCode,
                    op: T, resTyp, aJ, bJ: JitNode): JitNode =
  when T is gcc_jit_comparison:
    toJitNode(c.ctx.gcc_jit_context_new_comparison(nil, op, c.toRValue(aJ), c.toRValue(bJ)))
  elif T is gcc_jit_binary_op:
    toJitNode(
      c.ctx.gcc_jit_context_new_binary_op(nil, op, toPtrType(resTyp),
                                          c.toRValue(aJ),
                                          c.toRValue(bJ))
    )
  else:
    doAssert false, "not supported and does not make sense " & $T

proc newContextCall(c: JittedCode, fn: JitNode,
                    args: seq[JitNode]): JitNode =
  let numArgs = args.len
  let rawArgs = args.toRaw()
  doAssert fn.kind == jtFunction, "Argument must be a function. " & $fn
  let argPtr = if rawArgs.len == 0: nil else: rawArgs[0].addr
  result = toJitNode(c.ctx.gcc_jit_context_new_call(nil,
                                                    toPtrFunction(fn),
                                                    numArgs.cint, argPtr))

proc addReturn(blck: ptr gcc_jit_block) =
  gcc_jit_block_end_with_void_return(blck, nil)

proc addReturn(c: JittedCode, blck: ptr gcc_jit_block, res: JitNode) =
  gcc_jit_block_end_with_return(blck, nil, c.toRValue(res))

proc addReturn(c: var JittedCode, res: JitNode) =
  let blck = c.blckStack.pop() # pop the block, as we're leaving the scope anyway!
  ## XXX: do not use strings for the types, but if possible the `GCC_JIT` type?
  if res.kind == jtEmpty: # or res.kind == jtType and res.name == "void":
    addReturn(toPtrBlock(blck))
  elif res.kind == jtType:
    ## in this case return the local `result` variable, which must exist
    #doAssert "result" in c.locals
    #let res = c.locals["result"]
    c.addReturn(toPtrBlock(blck), res)
  else:
    c.addReturn(toPtrBlock(blck), res)

template binaryOp(opr) =
  let jop = toJitInfix(opr)
  let (typ, a, b) = sons3(t, n)
  let jt = gen(c, t, typ)
  let ja = gen(c, t, a)
  let jb = gen(c, t, b)
  result = c.newBinaryOp(jop, jt, ja, jb)

template checkedBinaryOp(opr) =
  let jop = toJitInfix(opr)
  let (typ, labIdx, a, b) = sons4(t, n)
  ## XXX: use??
  #let bits = integralBits(c.m.types[t[typ].typeId])
  let lab = t[labIdx].label

  let jt = gen(c, t, typ)
  let ja = gen(c, t, a)
  let jb = gen(c, t, b)
  result = c.newBinaryOp(jop, jt, ja, jb)

#proc genParam(c: JittedCode, fn: string, n: PNode, typ: PNode): JitNode =
#  ## XXX: Allow return type to be jtSeq so that e.g. ~openArray~ can be mapped
#  ## to `ptr T, len` pairs.
#  ## This means we need to reunify this with `genParamName`
#  let name = n.getName()
#  case typ.typ.kind
#  of tyOpenArray:
#    # handle openArray separately as we split it and then reify in body
#    result = initJitNode(jtSeq)
#    let oaTypes = c.toSeparateOpenArray(typ.typ)
#    for t in oaTypes.sons:
#      let typName = t.name
#      let paramNode = c.toParam(t, name & "_" & $typName)
#      result.add paramNode
#      c.stack.head().params.add (name, paramNode, typ, n)
#  else:
#    let paramType = c.toJitType(typ)
#    let typName = paramType.name
#    let paramNode = c.toParam(paramType, name)
#    result = paramNode
#    c.stack.head().params.add (name, paramNode, typ, n)

proc genProcDecl(c: var JittedCode, t: Tree, n: NodePos, isExtern: bool): JitNode =
  #let signatureBegin = c.code.len
  let name = n.firstSon
  var prc = n.firstSon
  next t, prc

  # Handle potential proc pragmas
  var headerImport = false
  while true:
    case t[prc].kind
    of PragmaPair:
      let (x, y) = sons2(t, prc)
      let key = cast[PragmaKey](t[x].rawOperand)
      case key
      of HeaderImport:
        ## XXX: Means we need to compile that file next / now!
        let lit = t[y].litId
        let headerAsStr {.cursor.} = c.m.lit.strings[lit]
        #let header = c.tokens.getOrIncl(headerAsStr)
        echo "HEADER IMPORT FOR: ", headerAsStr
        headerImport = true
        ## headerAsStr can be empty, this has the semantics of the `nodecl` pragma:
        #if headerAsStr.len > 0 and not c.includedHeaders.containsOrIncl(int header):
        #  if headerAsStr[0] == '#':
        #    discard "skip the #include"
        #  else:
        #    c.includes.add Token(IncludeKeyword)
        #  c.includes.add header
        #  c.includes.add Token NewLine
        # do not generate code for importc'ed procs:
        #return
        ##XXX: break and return after function added to table
        break
      of DllImport:
        let lit = t[y].litId
        raiseAssert "cannot eval: " & c.m.lit.strings[lit]
      else: discard
    of PragmaId: discard
    else: break
    next t, prc

  var resultDeclPos = NodePos(-1)
  var retType: JitNode
  # Get the result type
  if t[prc].kind == SummonResult:
    resultDeclPos = prc
    retType = gen(c, t, prc.firstSon)
    next t, prc
  else:
    retType = c.newType(GCC_JIT_TYPE_VOID)
  ## XXX: Need `genSymDef`?
  #genSymDef c, t, name

  ## XXX: CLEAN THIS UP!!!

  let symId = t[name].symId
  let fnName = genDisplayName(c, symId)

  let fnKind = if isExtern or headerImport: GCC_JIT_FUNCTION_IMPORTED else: GCC_JIT_FUNCTION_EXPORTED
  let fnObj = newFunction(fnName,
                          retType,
                          fnKind)

  # Assemble the function parameters
  var params: FnParams
  while t[prc].kind == SummonParam:
    let (typ, sym) = sons2(t, prc)
    let jt = gen(c, t, typ)
    let symId = t[sym].symId
    let symName = genDisplayName(c, symId)
    let jp = c.toParam(jt, symName)
    params.add (symName, jp)

    next t, prc

  # Produce the libgccjit function
  #for i in signatureBegin ..< c.code.len:
  #  c.protos.add c.code[i]
  #c.protos.add Token Semicolon
  fnObj.params = params
  fnObj.fn = c.newFunction(fnObj)
  c.stack.push fnObj
  # add for later lookup to table
  c.fnTab[symId] = fnObj ## Using name of the symbol to store it! this is what will be used to

  # generate body
  if isExtern or headerImport:
    #c.code.setLen signatureBegin
    discard
  else:
    # Add a new block for the function body
    discard c.newBlock("blck_body_" & $fnName, fnObj.fn)
    if resultDeclPos.int >= 0:
      discard gen(c, t, resultDeclPos)
    for ch in sonsRest(t, n, prc):
      discard gen(c, t, ch)

proc gen(c: var JittedCode, t: Tree, n: NodePos): JitNode =
  debug c, t, n
  case t[n].kind
  of Nop:
    discard "nothing to emit"
    result = initJitNode(jtEmpty) # be explicit about it
  #of ImmediateVal:
  #  c.add $t[n].immediateVal
  of IntVal:
    result = toJitNode c.toRValue(c.m.lit.numbers[t[n].litId])
  #of StrVal:
  #  c.code.add genStrLit(c, c.m.lit, t[n].litId)
  of Typed:
    result = genType(c, c.m.types, c.m.lit, t[n].typeId)
  of SymDef, SymUse:
    let s = t[n].symId ## XXX: FIX ME
    if s in c.locals:
      result = c.locals[s]
    elif s in c.globals:
      result = c.globals[s]
    elif s in c.fnTab:
      result = c.fnTab[s].fn
    #if c.needsPrefix.contains(s.int):
    #  c.code.add mangleModuleName(c, c.m.namespace)
    #  c.add "__"
    #  c.add $s
    #else:
    #  # XXX Use proper names here
    #  c.add "q"
    #  c.add $s

  of ModuleSymUse:
    let (x, y) = sons2(t, n)
    let u {.cursor.} = c.m.lit.strings[t[x].litId]
    echo "U : ", u
    # Load the target module of the symbol
    let nmp = c.path / u.extractFilename.replace(".nim", ".nir")
    c.mods[nmp] = load(nmp)
    # set it as the current module to process
    c.m = c.mods[nmp]
    var i = NodePos(0)
    # Process the file
    while i.int < c.m.code.len:
      discard gen(c, c.m.code, NodePos(i))
      next c.m.code, i
    # The function to load should now be known in `fnTab`
    let fnName {.cursor.} = c.m.lit.strings[t[y].litId]
    let symId = t[y].symId
    echo "Has fn : ", fnName, " ? ", symId in c.fnTab
    # reset the current module to main
    c.m = c.main

    #let u = mangleModuleName(c, t[x].litId)
    #let s = t[y].immediateVal
    #c.code.add u
    #c.add "__"
    #c.add $s
  #of NilVal:
  #  c.add NullPtr
  #of LoopLabel:
  #  c.add WhileKeyword
  #  c.add ParLe
  #  c.add "1"
  #  c.add ParRi
  #  c.add CurlyLe
  #of GotoLoop:
  #  c.add CurlyRi
  of Label: ## XXX: Maybe produce a block so that we can jump to it?
    let lab = t[n].label
    echo "IGNORING LABEL ", $lab.int
    #c.add "L"
    #c.add $lab.int
    #c.add Colon
    #c.add Semicolon
  #of Goto:
  #  let lab = t[n].label
  #  c.add "goto L"
  #  c.add $lab.int
  #  c.add Semicolon
  of CheckedGoto:
    #echo t[n].label
    discard "XXX todo"
  #of ArrayConstr:
  #  c.add CurlyLe
  #  c.add ".a = "
  #  c.add CurlyLe
  #  var i = 0
  #  for ch in sonsFrom1(t, n):
  #    if i > 0: c.add Comma
  #    c.gen t, ch
  #    inc i
  #  c.add CurlyRi
  #  c.add CurlyRi
  #of ObjConstr:
  #  c.add CurlyLe
  #  var i = 0
  #  for ch in sonsFrom1(t, n):
  #    if i mod 2 == 0:
  #      if i > 0: c.add Comma
  #      c.add ".F" & $t[ch].immediateVal
  #      c.add AsgnOpr
  #    else:
  #      c.gen t, ch
  #    inc i
  #  c.add CurlyRi
  of Ret:
    let val = c.gen(t, n.firstSon)
    c.addReturn(val)
  #of Select:
  #  c.add SwitchKeyword
  #  c.add ParLe
  #  let (_, selector) = sons2(t, n)
  #  c.gen t, selector
  #  c.add ParRi
  #  c.add CurlyLe
  #  for ch in sonsFromN(t, n, 2):
  #    c.gen t, ch
  #  c.add CurlyRi
  #of SelectPair:
  #  let (le, ri) = sons2(t, n)
  #  c.gen t, le
  #  c.gen t, ri
  #of SelectList:
  #  for ch in sons(t, n):
  #    c.gen t, ch
  #of SelectValue:
  #  c.add CaseKeyword
  #  c.gen t, n.firstSon
  #  c.add Colon
  #of SelectRange:
  #  let (le, ri) = sons2(t, n)
  #  c.add CaseKeyword
  #  c.gen t, le
  #  c.add " ... "
  #  c.gen t, ri
  #  c.add Colon
  #of ForeignDecl:
  #  c.data.add LitId(ExternKeyword)
  #  c.gen t, n.firstSon
  of SummonGlobal:
    let (typ, sym) = sons2(t, n)
    ## XXX: for now discard
    result = c.genGlobal(t, sym, typ, "")
  #of SummonThreadLocal:
  #  moveToDataSection:
  #    let (typ, sym) = sons2(t, n)
  #    c.genGlobal t, sym, typ, "__thread "
  #    c.add Semicolon
  #of SummonConst:
  #  moveToDataSection:
  #    let (typ, sym, val) = sons3(t, n)
  #    c.genGlobal t, sym, typ, "const "
  #    c.add AsgnOpr
  #    c.gen t, val
  #    c.add Semicolon
  of Summon, SummonResult:
    let (typ, sym) = sons2(t, n)
    result = c.genLocal(t, sym, typ, "")
  #of SummonParam:
  #  raiseAssert "SummonParam should have been handled in genProc"
  #of Kill:
  #  discard "we don't care about Kill instructions"
  #of AddrOf:
  #  let (_, arg) = sons2(t, n)
  #  c.add "&"
  #  gen c, t, arg
  #of DerefArrayAt:
  #  let (_, a, i) = sons3(t, n)
  #  gen c, t, a
  #  c.add BracketLe
  #  gen c, t, i
  #  c.add BracketRi
  #of ArrayAt:
  #  let (_, a, i) = sons3(t, n)
  #  gen c, t, a
  #  c.add Dot
  #  c.add "a"
  #  c.add BracketLe
  #  gen c, t, i
  #  c.add BracketRi
  #of FieldAt:
  #  let (_, a, b) = sons3(t, n)
  #  gen c, t, a
  #  let field = t[b].immediateVal
  #  c.add Dot
  #  c.add "F" & $field
  #of DerefFieldAt:
  #  let (_, a, b) = sons3(t, n)
  #  gen c, t, a
  #  let field = t[b].immediateVal
  #  c.add Arrow
  #  c.add "F" & $field
  #of Load:
  #  let (_, arg) = sons2(t, n)
  #  c.add ParLe
  #  c.add "*"
  #  gen c, t, arg
  #  c.add ParRi
  #of Store:
  #  raiseAssert "Assumption was that Store is unused!"
  of Asgn:
    let (_, dest, src) = sons3(t, n)
    let dn = gen(c, t, dest)
    let ds = gen(c, t, src)
    c.assign(dn, ds)
  #of CheckedRange:
  #  c.add "nimCheckRange"
  #  c.add ParLe
  #  let (_, gotoInstr, x, a, b) = sons5(t, n)
  #  gen c, t, x
  #  c.add Comma
  #  gen c, t, a
  #  c.add Comma
  #  gen c, t, b
  #  c.add Comma
  #  c.add "L" & $t[gotoInstr].label.int
  #  c.add ParRi
  #of CheckedIndex:
  #  c.add "nimCheckIndex"
  #  c.add ParLe
  #  let (gotoInstr, x, a) = sons3(t, n)
  #  gen c, t, x
  #  c.add Comma
  #  gen c, t, a
  #  c.add Comma
  #  c.add "L" & $t[gotoInstr].label.int
  #  c.add ParRi
  of Call, IndirectCall:
    let (typ, fn) = sons2(t, n)
    let fnSym = gen(c, t, fn)
    var params = newSeq[JitNode]()
    for ch in sonsFromN(t, n, 2):
      params.add gen(c, t, ch)
    result = c.newContextCall(fnSym, params)
    ## XXX: What does the Semicolon do here?
    #if c.m.types[t[typ].typeId].kind == VoidTy:
    #  c.add Semicolon
  of CheckedCall, CheckedIndirectCall:
    let (typ, gotoInstr, fn) = sons3(t, n)
    let fnSym = gen(c, t, fn)
    var params = newSeq[JitNode]()
    for ch in sonsFromN(t, n, 3):
      params.add gen(c, t, ch)
    result = c.newContextCall(fnSym, params)
    ## XXX: What does the Semicolon do here?
    #if c.m.types[t[typ].typeId].kind == VoidTy:
    #  c.add Semicolon
  #of CheckedAdd: checkedBinaryop "nimAddInt"
  #of CheckedSub: checkedBinaryop "nimSubInt"
  #of CheckedMul: checkedBinaryop "nimMulInt"
  #of CheckedDiv: checkedBinaryop "nimDivInt"
  #of CheckedMod: checkedBinaryop "nimModInt"
  #of Add: binaryOp " + "
  of Add, Sub, Mul, Div, Mod, BitShl, BitShr, BitAnd, BitOr, BitXor:
    binaryOp t[n].kind ## XXX: ignoring the Checked part for now!
  of CheckedAdd, CheckedSub, CheckedMul, CheckedDiv, CheckedMod:
    checkedBinaryOp t[n].kind
  #of BitNot: binaryop " ~ "
  #of BoolNot: binaryop " !"
  #of Eq: cmpop " == "
  #of Le: cmpop " <= "
  #of Lt: cmpop " < "
  #of Cast: binaryop ""
  of NumberConv: result = genNumberConv(c, t, n)
  #of CheckedObjConv: binaryop ""
  #of ObjConv: binaryop ""
  #of Emit: raiseAssert "cannot interpret: Emit"
  of ProcDecl: result = genProcDecl(c, t, n, false)
  of ForeignProcDecl: result = genProcDecl(c, t, n, true)
  #of PragmaPair, PragmaId, TestOf, Yld, SetExc, TestExc:
  #  c.add "cannot interpret: " & $t[n].kind
  else:
    echo "IGNORING::::::::: ", t[n].kind
    discard

proc traverseCode(c: var JittedCode) =
  ## From `cir.nim`
  const AllowedInToplevelC = {SummonConst, SummonGlobal, SummonThreadLocal,
                              ProcDecl, ForeignDecl, ForeignProcDecl}
  var i = NodePos(0)

  # produce an `init` function for all global code
  let fnInit = newFunction(fnSym = "init", retType = newType(c, GCC_JIT_TYPE_VOID),
                           GCC_JIT_FUNCTION_INTERNAL)
  let fnDef = c.newFunction(fnInit)
  c.stack.push fnInit
  # add for later lookup to table
  #c.fnTab["init"] = fnInit ## Using name of the symbol to store it! this is what will be used to
  discard c.newBlock("blck_body_init", fnDef)

  while i.int < c.m.code.len:
    #let oldLen = c.code.len
    let moveToInitSection = c.m.code[NodePos(i)].kind notin AllowedInToplevelC

    discard gen(c, c.m.code, NodePos(i))
    next c.m.code, i

    #if moveToInitSection:
    #  for i in oldLen ..< c.code.len:
    #    c.init.add c.code[i]
    #  setLen c.code, oldLen

when false:
  # generatet the correct struct
  ## XXX: handle variant types using tagged union! See my notes!
  var jitFields = newSeq[ptr gcc_jit_field]()
  # I fear we have to return the `gcc_jit_field` as well for use later.
  ## XXX: check for magic `importc` types!
  let typName = typ.typeToString()
  if typName in jitCtx.types:
    result = toJitNode(jitCtx.types[typName].typ, typName)
  else:
    ## Generate the JitType that stores all the pointers for later lookup and construct
    ## the `struct`. Note that currently only flat objects of basic types are supported!
    var jitType = initJitType(typName)
    echo jitCtx.intr.performTransformation(typ.sym).ast.renderTree()
    for field, val in fieldTypes(typ):
      let jitField = jitCtx.newField(val, field)
      jitType.`fields`[field] = jitField
      jitFields.add toPtrField(jitField)


import ./type_graph_helpers
proc generateTypes(g: var JittedCode; types: TypeGraph; lit: Literals; c: TypeOrder) =
  for (t, declKeyword) in c.forwardedDecls.s:
    let name = if types[t].kind == ArrayTy: arrayName(types, t) else: t.firstSon
    let s {.cursor.} = lit.strings[types[name].litId]
    echo "Declaring::: ", s
    #g.add declKeyword
    #g.add s
    #g.add Space
    #g.add s
    #g.add Semicolon

  for (t, declKeyword) in c.ordered.s:
    let name = if types[t].kind == ArrayTy: arrayName(types, t) else: t.firstSon
    let litId = types[name].litId
    if not g.generatedTypes.containsOrIncl(litId.int):
      let s {.cursor.} = lit.strings[litId]
      echo "Looking at::: ", s, " decl : ", declKeyword
      debug g, t
      echo "----------------------------"
      #g.add declKeyword
      #g.add CurlyLe
      var jitFields = newSeq[ptr gcc_jit_field]()
      var jitType = initJitType(s)
      if types[t].kind == ArrayTy:
        echo "WHAT IS TYPE KIND?? ", types[t].kind
        discard
        #genType g, types, lit, elementType(types, t), "a"
        #g.add BracketLe
        #g.add $arrayLen(types, t)
        #g.add BracketRi
        #g.add Semicolon
      else:
        var i = 0
        for x in sons(types, t):
          var jt: JitNode
          case types[x].kind
          of FieldDecl:
            debug g, x
            jt = genType(g, types, lit, x.firstSon, "F" & $i)
          of ObjectTy: ## NOTE: At this point the `ObjectTy` part of another type must have already been
                       ## generated. Therefore we can look it up using `genType`
            jt = genType(g, types, lit, x, "P" & $i)
          else:
            echo "WHATDDD ", types[x].kind
          if jt.kind != jtEmpty:
            let jitField = g.newField(jt, jt.name)
            jitType.`fields`[jt.name] = jitField
            jitFields.add toPtrField(jitField)
          inc i
      # produce the full struct
      if jitFields.len > 0:
        let struct = g.newStruct(s, jitFields)
        jitType.struct = toPtrStruct(struct)
        echo "GENERATING TYPE: ", s, " at id ", t.int
        let jtn = toJitNode(gcc_jit_struct_as_type(toPtrStruct(struct)), s)
        jitType.typ = toPtrType(jtn)
        g.types[s] = jitType
        ## XXX: I want the following:
        #g.types[t] = jitType
      else:
        echo "GOT EMPTY::::::: ", s


proc main(file: string) =
  view file
  var c = initJittedCode(file)

  var co = TypeOrder()
  traverseTypes(c.m.types, c.m.lit, co)

  generateTypes(c, c.m.types, c.m.lit, co)
  #let typeDecls = move c.code

  traverseCode c


when isMainModule:
  import cligen
  dispatch main
