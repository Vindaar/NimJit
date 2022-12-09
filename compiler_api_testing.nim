import compiler/[nimeval, llstream, renderer, magicsys,
                 transf, # for code transformation (for -> while etc)
                 injectdestructors] # destructor injection


# probably need to import `pragmas` and `wordrecg` to get
# `hasPragma` working

import hnimast
import libgccjit
import typetraits


import std / [macros, genasts, sets, tables, options]
import system / ansi_c


from std/sequtils import concat
proc flatten[T: not seq](a: seq[T]): seq[T] = a
proc flatten[T: seq](a: seq[T]): auto =  a.concat.flatten

const Debug = false

template debug(args: varargs[typed]): untyped =
  when Debug:
    echo(args)

type
  FnParams = seq[(string, JitNode, PNode)]
  #               ^--- name of parameter
  #                       ^--- ptr gcc_jit_param
  #                                ^--- PNode of the type used to construct the param

  ## A type storing the symbols for a given type
  JitType = ref object
    name: string # the name as a string of this type
    typ: ptr gcc_jit_type
    struct: ptr gcc_jit_struct # if it corresponds to a struct
    `fields`: Table[string, JitNode]

  Function = ref object
    name: string
    fnSym: string # the name of the symbol (may be different for imported functions)
    isVariadic: bool
    functionKind: gcc_jit_function_kind
    fn: JitNode # node representing a `ptr gcc_jit_function`
    retType: JitNode # return type of the function
    params: FnParams # arguments and their types
    node: PNode # the corresponding AST

  JitContext = ref object # ref object as it stores pointers, so copying by value doesn't make a lot of sense
    ctx: ptr gcc_jit_context
    res: ptr gcc_jit_result # stores the result of different operations e.g. compilation
    # and further fields for the storage of information that stores
    # things like `gcc_jit_struct` and `gcc_jit_fields` associated.
    types: Table[string, JitType]
    fnTab: Table[string, Function] ## maps each function by string name to its JitNode (from `jitFn`)
    stack: seq[Function] ## current function stack. Head points at function being processed atm
    varCount: int # counter of variables for a custom gensym of sorts
    locals: Table[string, JitNode] ## maps a variable name to a generated JitNode (of kind lvalue)
    blckStack: seq[JitNode] # stack of the current blocks
    nextCallRvalue: bool # determines if the next `nnkCall` encountered must be generated
                         # as an RValue, instead of discarded (add `*_add_eval` or not)
    seenFns: HashSet[string] ## set of symbols that were already jit'ed
    hasExplicitReturn: bool ## marks a return statement to know if we still need to terminate
    intr: Interpreter ## The Nim compiler (currently using the `Interpreter` from `nimeval.nim`)

  # XXX: Idea: Maybe instead of `PNode` we could return a `JitNode`, which
  # would be a variant object that can contain all possible libgccjit types? Then
  # The caller of `genNode`, given the context can just hand the return types
  # to the appropriate calls where the nodes would be consumed?
  # This is mainly of importance to have a recursive implementation where we are
  # allowed to recurse into "leaf" nodes, i.e. LHS & RHS of an infix expression.
  # If we *only* want to "execute" libgccjit functions from here, we would not
  # be returning anything, meaning we *cannot* recurse into leaf nodes.
  #
  # Related, but I'm not sure if it is an "alternative" is having the `JitContext`
  # contain e.g. a `locals` table, which maps nim symbols to libgccjit variables.
  # Then, a call into a leaf node might just update some field of the `JitContext`
  # and in the caller we could then look up a potentially new variable or
  # an already generated one?
  JitTypes = enum
    # jtContext, jtResult ## These two are not relevant to return as a node I think
    jtEmpty, # default is empty node
    jtObject,
    jtLocation,
    jtType,
    jtField,
    jtStruct,
    jtFunction,
    jtBlock,
    jtRValue,
    jtLValue,
    jtParam,
    jtCase,
    jtSeq # special case containing multiple elements
  ## A node that represents any of the generated `libgccjit` objects. Returned from
  ## `genNode`
  JitNode = object
    name: string # optional name field
    case kind: JitTypes
    of jtEmpty: discard
    of jtObject: obj*: ptr gcc_jit_object
    of jtLocation: loc*: ptr gcc_jit_location
    of jtType: typ*: ptr gcc_jit_type
    of jtField: field*: ptr gcc_jit_field
    of jtStruct: struct*: ptr gcc_jit_struct
    of jtFunction: fn*: ptr gcc_jit_function
    of jtBlock: blck*: ptr gcc_jit_block
    of jtRValue: rval*: ptr gcc_jit_rvalue
    of jtLValue: lval*: ptr gcc_jit_lvalue
    of jtParam: param*: ptr gcc_jit_param
    of jtCase: cas*: ptr gcc_jit_case
    of jtSeq: sons: seq[JitNode]
  ## XXX: implement usage of `lineInfo` for `gcc_jit_location` arguments for proper debugging!

proc toJitNode(x: ptr gcc_jit_object  , name = ""): JitNode = JitNode(name: name, kind: jtObject, obj: x)
proc toJitNode(x: ptr gcc_jit_location, name = ""): JitNode = JitNode(name: name, kind: jtLocation, loc: x)
proc toJitNode(x: ptr gcc_jit_type    , name = ""): JitNode = JitNode(name: name, kind: jtType, typ: x)
proc toJitNode(x: ptr gcc_jit_field   , name = ""): JitNode = JitNode(name: name, kind: jtField, field: x)
proc toJitNode(x: ptr gcc_jit_struct  , name = ""): JitNode = JitNode(name: name, kind: jtStruct, struct: x)
proc toJitNode(x: ptr gcc_jit_function, name = ""): JitNode = JitNode(name: name, kind: jtFunction, fn: x)
proc toJitNode(x: ptr gcc_jit_block   , name = ""): JitNode = JitNode(name: name, kind: jtBlock, blck: x)
proc toJitNode(x: ptr gcc_jit_rvalue  , name = ""): JitNode = JitNode(name: name, kind: jtRValue, rval: x)
proc toJitNode(x: ptr gcc_jit_lvalue  , name = ""): JitNode = JitNode(name: name, kind: jtLValue, lval: x)
proc toJitNode(x: ptr gcc_jit_param   , name = ""): JitNode = JitNode(name: name, kind: jtParam, param: x)
proc toJitNode(x: ptr gcc_jit_case    , name = ""): JitNode = JitNode(name: name, kind: jtCase, cas: x)

proc toPtrObj(n: JitNode      ): ptr gcc_jit_object   = n.obj
proc toPtrLoc(n: JitNode      ): ptr gcc_jit_location = n.loc
proc toPtrType(n: JitNode     ): ptr gcc_jit_type     = n.typ
proc toPtrField(n: JitNode    ): ptr gcc_jit_field    = n.field
proc toPtrStruct(n: JitNode   ): ptr gcc_jit_struct   = n.struct
proc toPtrFunction(n: JitNode ): ptr gcc_jit_function = n.fn
proc toPtrBlock(n: JitNode    ): ptr gcc_jit_block    = n.blck
proc toPtrRValue(n: JitNode   ): ptr gcc_jit_rvalue   = n.rval
proc toPtrLValue(n: JitNode   ): ptr gcc_jit_lvalue   = n.lval
proc toPtrParam(n: JitNode    ): ptr gcc_jit_param    = n.param
proc toPtrCase(n: JitNode     ): ptr gcc_jit_case     = n.cas


# forward declares
proc performTransformation(intr: Interpreter, p: PSym): PSym


# inverse converters
#converter toJitBlock(x: JitNode): ptr gcc_jit_block =
#  doAssert x.kind == jtBlock
#  result = x.blck

# inverse converters
#converter jitTypeToGccJit(x: JitNode): ptr gcc_jit_type =
#  doAssert x.kind == jtType
#  result = x.typ

#proc toJitNode(name: string, x: ptr gcc_jit_block): JitNode =
#  JitNode(name: name, kind: jtBlock, blck: x)
#
#proc toJitNode(name: string, x: ptr gcc_jit_type): JitNode =
#  JitNode(name: name, kind: jtType, typ: x)

proc `$`(n: JitNode): string =
  result = "JitNode(kind: " & $n.kind & ", name: " & n.name & ")"

proc add(a: var JitNode, b: JitNode) =
  ## Add the given node `b` to the sons of `a`.
  doAssert a.kind == jtSeq
  a.sons.add b

proc len(n: JitNode): int =
  doAssert n.kind == jtSeq
  result = n.sons.len

proc initJitNode(kind: JitTypes): JitNode =
  result = JitNode(kind: kind)

proc initJitType(name: string): JitType =
  result = JitType(name: name,
                   typ: nil,
                   struct: nil,
                   `fields`: initTable[string, JitNode]())

proc initFnParams(): FnParams = FnParams(newSeq[(string, JitNode, PNode)]())

proc newFunction(name: string,
                 fnSym: string,
                 node: PNode,
                 retType: JitNode,
                 functionKind: gcc_jit_function_kind): Function =
  result = Function(name: name,
                    node: node,
                    retType: retType,
                    functionKind: functionKind,
                    params: initFnParams(),
                    fn: initJitNode(jtEmpty))

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

proc high(n: PNode): int = n.len - 1

proc `[]`(n: JitNode, idx: int): JitNode =
  doAssert n.kind == jtSeq
  result = n.sons[idx]

proc toRaw(n: JitNode): seq[ptr gcc_jit_rvalue] =
  doAssert n.kind == jtSeq
  result = newSeq[ptr gcc_jit_rvalue](n.len)
  for i in 0 ..< n.len:
    doAssert n[i].kind == jtRValue
    result[i] = n[i].rval

proc getType(n: PNode): string =
  result = n.typ.sym.name.s

proc getTypeKind(n: PNode): TTypeKind =
  result = n.typ.sym.typ.kind

proc getTypeImpl(n: PNode): PNode =
  result = n.typ.sym.ast

proc getImpl(n: PNode): PNode =
  result = n.sym.ast

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
  of "float", "float64": result = GCC_JIT_TYPE_DOUBLE
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

proc toJitType(t: TTypeKind): gcc_jit_types =
  ## XXX: NOT ACTUALLY USED!!
  doAssert false, "NOT USED"
  case t
  of tyVoid: result = GCC_JIT_TYPE_VOID
  of tyPointer: result = GCC_JIT_TYPE_VOID_PTR
  of tyBool: result = GCC_JIT_TYPE_BOOL
  of tyChar: result = GCC_JIT_TYPE_CHAR
  # of "uchar" : result = GCC_JIT_TYPE_UNSIGNED_CHAR
  #of "cschar" : result = GCC_JIT_TYPE_SIGNED_CHAR
  of tyInt16: result = GCC_JIT_TYPE_SHORT
  of tyUint16: result = GCC_JIT_TYPE_UNSIGNED_SHORT
  of tyInt32: result = GCC_JIT_TYPE_INT
  of tyUint32: result = GCC_JIT_TYPE_UNSIGNED_INT
  #of tyInt32: result = GCC_JIT_TYPE_LONG
  #of tyUInt32: : result = GCC_JIT_TYPE_UNSIGNED_LONG
  of tyInt, tyInt64: result = GCC_JIT_TYPE_LONG_LONG ## only int if sizeof(int) == 8
  of tyUint, tyUint64: result = GCC_JIT_TYPE_UNSIGNED_LONG_LONG
  of tyFloat32: result = GCC_JIT_TYPE_FLOAT
  of tyFloat, tyFloat64: result = GCC_JIT_TYPE_DOUBLE
  # of "float64" : result = GCC_JIT_TYPE_LONG_DOUBLE
  of tyString, tyCString: result = GCC_JIT_TYPE_CONST_CHAR_PTR ## XXX: probably not?
  #of "csize_t": result = GCC_JIT_TYPE_SIZE_T
  #of "File" : result = GCC_JIT_TYPE_FILE_PTR
  #of "Complex[float32]": result = GCC_JIT_TYPE_COMPLEX_FLOAT
  #of "Complex[float]", "Complex[float64]": result = GCC_JIT_TYPE_COMPLEX_DOUBLE
  #of "Complex[float64]": result = JIT_TYPE_COMPLEX_LONG_DOUBLE
  #of "varargs[typed]": result = GCC_JIT_TYPE_CONST_CHAR_PTR ## XXX: HACK!!!
  else:
    doAssert false, "Not supported yet! " & $t
    result = GCC_JIT_TYPE_VOID


#proc toJitInfix[T](s: string, typ: typedesc[T]): gcc_jit_binary_op =
#  when T is SomeInteger:
proc toJitInfix(s: string, typ: TTypeKind): gcc_jit_binary_op =
  var s = s
  if typ in {tyInt .. tyInt64} + {tyUint .. tyUint64}:
    s = if s in ["and", "or"]: s & "I"
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

type
  JitInfixKind = enum infixMath, infixCompare

proc getName(n: PNode): string =
  doAssert n.kind in {nkIdent, nkSym, nkStrLit, nkProcDef, nkFuncDef}, "Unsupported kind " & $n.kind
  case n.kind
  of nkIdent:
    result = n.ident.s
  of nkSym:
    result = n.sym.name.s
  of nkStrLit:
    result = n.strVal
  of nkProcDef, nkFuncDef:
    result = n[0].getName()
  else:
    doAssert false, "Not supported"

proc jitInfixKind(n: PNode): JitInfixKind =
  ## Given a typed infix node, return the correct JIT infix node, taking into account
  ## duplicate names, by appending a suffix for integers
  doAssert n.kind == nkInfix
  let op = n[0].getName()
  if op in ["==", "!=", "<", "<=", ">", ">="]:
    result = infixCompare
  else:
    result = infixMath

template toJitType(typ: typed): gcc_jit_types =
  astToStr(typ).toJitType()

iterator fieldTypes(n: PNode): (string, PNode) =
  ## yields the name of each object field and the type as a string
  doAssert n.kind == nkTypeDef
  let rec = n[2][2]
  for i in 0 ..< rec.len:
    let ch = rec[i]
    doAssert ch.kind == nkIdentDefs
    ## We yield the node so that we can later extract the type as we please from the `PNode`
    yield (ch[0].getName(), ch[1])

proc toJitType(jitCtx: JitContext, n: PNode): JitNode

proc newField(jitCtx: JitContext, val: PNode, field: string): JitNode =
  result = toJitNode(
    jitCtx.ctx.gcc_jit_context_new_field(
      nil,
      toPtrType(jitCtx.toJitType(val)),
      field),
    $field
  )

proc newStruct(jitCtx: JitContext, typName: string, jitFields: seq[ptr gcc_jit_field]): JitNode =
  result = toJitNode(
    jitCtx.ctx.gcc_jit_context_new_struct_type(
        nil,
        typName,
        jitFields.len.cint,
        jitFields[0].addr
      )
  )

proc newArrayType(jitCtx: JitContext, typ: JitNode, name: string, num: int): JitNode =
  result = toJitNode(
      jitCtx.ctx.gcc_jit_context_new_array_type(
        nil,
        toPtrType(typ),
        num.cint),
      name
    )

proc newPointer(jitCtx: JitContext, n: PNode): JitNode =
  let typ = n.getType()
  result = toJitNode(
      gcc_jit_type_get_pointer(
        jitCtx.ctx.gcc_jit_context_get_type(
          toJitType(typ)
        )
      ),
      "ptr " & $typ,
    )

proc newVoidType(jitCtx: JitContext): JitNode =
  result = toJitNode(jitCtx.ctx.gcc_jit_context_get_type(toJitType("void")),
                     "void")

proc newType(jitCtx: JitContext, typ: string): JitNode =
  result = toJitNode(
    jitCtx.ctx.gcc_jit_context_get_type(toJitType(typ)),
    typ,
  )

proc toJitType(jitCtx: JitContext, n: PNode): JitNode = # ptr gcc_jit_type =
  debug "--> ", n.treerepr, "|", " of kind ", n.kind, " |||"

  ## XXX: special case `string` and `seq`.
  ## These are simple and allow us to then define the magics acting on
  ## them that are not defined as `compilerproc`. E.g. `len` for either
  ## then is just a `.len` field access!
  ## Similar to `lookupMagic` we can have a `lookupMagicType` or something that
  ## returns the libgccjit representation of the implementation details so that
  ## we can properly generate the type for it.
  ## type
  ##  NimStrPayloadBase = object
  ##    cap: int
  ##
  ##  NimStrPayload {.core.} = object
  ##    cap: int
  ##    data: UncheckedArray[char]
  ##
  ##  NimStringV2 {.core.} = object
  ##    len: int
  ##    p: ptr NimStrPayload ## can be nil if len == 0.
  ##
  ## Default seq implementation used by Nim's core.
  ## type
  ##   NimSeqPayloadBase = object
  ##     cap: int
  ##
  ##   NimSeqPayload[T] = object
  ##     cap: int
  ##     data: UncheckedArray[T]
  ##
  ##   NimSeqV2*[T] = object # \
  ##     # if you change this implementation, also change seqs_v2_reimpl.nim!
  ##     len: int
  ##     p: ptr NimSeqPayload[T]
  ##
  if n.kind == nkEmpty:
    result = jitCtx.newVoidType()
  elif n.typ.kind == tyObject:
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
    let typName = n.getType()
    if typName in jitCtx.types:
      result = toJitNode(jitCtx.types[typName].typ, typName)
    else:
      ## Generate the JitType that stores all the pointers for later lookup and construct
      ## the `struct`. Note that currently only flat objects of basic types are supported!
      var jitType = initJitType(typName)

      for field, val in fieldTypes(n.getTypeImpl()):
        let jitField = jitCtx.newField(val, field)
        jitType.`fields`[field] = jitField
        jitFields.add toPtrField(jitField)

      let struct = jitCtx.newStruct(typName, jitFields)
      jitType.struct = toPtrStruct(struct)
      result = toJitNode(gcc_jit_struct_as_type(toPtrStruct(struct)), typName)
      jitType.typ = toPtrType(result)
      jitCtx.types[typName] = jitType
  elif n.typ.kind == tyArray:
    ## construct a fixed size array
    ## XXX: for now use element 0 for the type, but maybe we can get i
    ## from the bracket itself?
    let typ = jitCtx.toJitType(n[0])
    let name = n[0].getType()
    result = jitCtx.newArrayType(typ, name, n.len)
  elif n.typ.kind == tyVar:
    ## type is pointer to n[0]
    result = jitCtx.newPointer(n[0])
  else:
    let typ = n.getType()
    result = jitCtx.newType(typ)

proc toJitType(n: JitNode): ptr gcc_jit_type =
  case n.kind
  of jtType: result = n.typ
  of jtStruct: result = gcc_jit_struct_as_type(n.struct)
  else: doAssert false, "Cannot convert the given node " & $n.repr & " to a jit type!"

proc toJitType[T](jitCtx: JitContext, typ: typedesc[T]): ptr gcc_jit_type =
  jitCtx.ctx.gcc_jit_context_get_type(toJitType($T))

proc toParam(jitCtx: JitContext, typ: PNode, name: string): ptr gcc_jit_param =
  jitCtx.ctx.gcc_jit_context_new_param(nil, toPtrType(jitCtx.toJitType(typ)), name)

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

proc toRValue[T](jitCtx: JitContext, val: typedesc[T]): ptr gcc_jit_rvalue =
  var tmp = default(T)
  result = jitCtx.toRValueu(tmp)

proc toRValue(jitCtx: JitContext, val: PNode): ptr gcc_jit_rvalue =
  doAssert val.kind in nkLiterals
  case val.kind
  of nkCharLit .. nkUInt64Lit:
    when sizeof(int) <= 4:
      result = jitCtx.ctx.gcc_jit_context_new_rvalue_from_int(jitCtx.toJitType(val), val.intVal.cint)
    else:
      result = jitCtx.ctx.gcc_jit_context_new_rvalue_from_long(
        toPtrType(jitCtx.toJitType(val)), val.intVal.clonglong
      )
  of nkFloatLit..nkFloat128Lit:
    result = jitCtx.ctx.gcc_jit_context_new_rvalue_from_double(
      toPtrType(jitCtx.toJitType(val)), val.floatVal.cdouble
    )
  of nkStrLit..nkTripleStrLit:
    ## XXX: is it sensible to check here for `true` and `false`? What happens if input
    ## is a string of that value?
    if val.getName() == "true":
      doAssert val.typ.kind == tyBool, "Handle string!"
      result = jitCtx.ctx.gcc_jit_context_new_rvalue_from_int(
        toPtrType(jitCtx.toJitType(val)), 1.cint
      )
    elif val.getName() == "false":
      doAssert val.typ.kind == tyBool, "Handle string!"
      result = jitCtx.ctx.gcc_jit_context_new_rvalue_from_int(
        toPtrType(jitCtx.toJitType(val)), 0.cint
      )
    else:
      result = jitCtx.ctx.gcc_jit_context_new_string_literal(val.getName().cstring)
  #elif T is string:
  #  ctx.
  #elif T is openArray:
  #  doAssert val.len == 1
  #  ctx.toRValue(val[0])
  else:
    doAssert false, "Kind " & $val.kind & " is not supported yet."


proc toRValue(jitCtx: JitContext, val: JitNode): ptr gcc_jit_rvalue =
  case val.kind
  of jtLValue: result = jitCtx.toRValue(val.lval)
  of jtRValue: result = val.rval
  of jtParam:  result = toRValue(val.param)
  else: doAssert false, "Node of kind " & $val.kind & " cannot be turned into an RValue"

proc toLValue(val: JitNode): ptr gcc_jit_lvalue =
  case val.kind
  of jtLValue: result = val.lval
  else: doAssert false, "Node of kind " & $val.kind & " cannot be turned into an LValue"

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

proc getBlockName(ctx: JitContext, n: PNode): string =
  doAssert n.kind == nkBlockStmt
  if n[0].kind == nkEmpty:
    result = "tmp_" & $ctx.varCount
  else:
    result = n[0].getName() & "_" & $ctx.varCount
  inc ctx.varCount

proc getFieldAsRValue(jitCtx: JitContext, obj: ptr gcc_jit_rvalue, typ: PNode, field: string): JitNode =
  ## returns the field `field` of the given `obj`, assuming it's of type `typ`.
  let typName = typ.getType()
  doAssert $typName in jitCtx.types, "The type " & $typName & " does not exist in the JitContext types!"
  let jitTyp = jitCtx.types[typName]
  let fld = jitTyp.`fields`[field]
  result = toJitNode(gcc_jit_rvalue_access_field(obj, nil, toPtrField(fld)))

proc addReturn(blck: ptr gcc_jit_block) =
  gcc_jit_block_end_with_void_return(blck, nil)

proc addReturn(jitCtx: JitContext, blck: ptr gcc_jit_block, res: JitNode) =
  gcc_jit_block_end_with_return(blck, nil, jitCtx.toRValue(res))

proc addReturn(ctx: JitContext, res: JitNode) =
  let blck = ctx.blckStack.pop() # pop the block, as we're leaving the scope anyway!
  ## XXX: do not use strings for the types, but if possible the `GCC_JIT` type?
  if res.kind == jtEmpty or res.kind == jtType and res.name == "void":
    addReturn(toPtrBlock(blck))
  elif res.kind == jtType:
    ## in this case return the local `result` variable, which must exist
    doAssert "result" in ctx.locals
    let res = ctx.locals["result"]
    ctx.addReturn(toPtrBlock(blck), res)
  else:
    ctx.addReturn(toPtrBlock(blck), res)

proc newFunction(jitCtx: JitContext,
                 fn: Function): JitNode =
  #var params = newSeq[ptr gcc_jit_param]()
  #for f, v in fields(params):
  #  params.add ctx.toParam(typeof(v), f)
  let variadic = if fn.isVariadic: 1.cint else: 0.cint
  var jitParams = newSeq[ptr gcc_jit_param]()
  for p in fn.params:
    jitParams.add p[1].param
  let paramsAddr = if jitParams.len == 0: nil else: jitParams[0].addr
  debug "Generating new function with arguments: ", fn.params.repr
  result = toJitNode(
    jitCtx.ctx.gcc_jit_context_new_function(
      nil,
      fn.functionKind,
      toPtrType(fn.retType), # return type
      fn.name,
      jitParams.len.cint, paramsAddr,
      variadic)
  )

proc newContextCall(jitCtx: JitContext, fn: JitNode,
                    args: seq[ptr gcc_jit_rvalue]): JitNode =
  let numArgs = args.len
  doAssert fn.kind == jtFunction, "Argument must be a function"
  result = toJitNode(jitCtx.ctx.gcc_jit_context_new_call(nil,
                                                         toPtrFunction(fn),
                                                         numArgs.cint, args[0].addr))

proc addEval(blck: JitNode, contextCall: JitNode) =
  ## Adds an evaluation to the given `blck` with the given `contextCall`, which
  ## should be the result of a call to `newContextCall`
  doAssert contextCall.kind == jtRValue
  gcc_jit_block_add_eval(toPtrBlock blck, nil, contextCall.rval)

proc newBinaryOp[T; V; W](jitCtx: JitContext,
                          op: T,
                          resType: PNode,
                          aJ: V, bJ: W): JitNode =
  when T is gcc_jit_comparison:
    toJitNode(jitCtx.ctx.gcc_jit_context_new_comparison(nil, op, jitCtx.toRValue(aJ), jitCtx.toRValue(bJ)))
  elif T is gcc_jit_binary_op:
    toJitNode(
      jitCtx.ctx.gcc_jit_context_new_binary_op(nil, op, toPtrType(jitCtx.toJitType(resType)),
                                               jitCtx.toRValue(aJ),
                                               jitCtx.toRValue(bJ))
    )
  else:
    doAssert false, "not supported and does not make sense " & $T

proc setupContext(): JitContext =
  result = JitContext()
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

proc initJitContext(intr: Interpreter, setupContext: bool): JitContext =
  ## Isn't the better option to have the JitContext as an argument to all procedures?
  ## Then we don't have the trouble of being able to access the `libgccjit` context
  ## when `jitFn` is being called from within `jitFn`.
  if setupContext:
    result = setupContext()
  else:
    result = JitContext()
  result.intr = intr

template withRValue(ctx: JitContext, body: untyped): untyped {.dirty.} =
  ## XXX: this is currently broken in context of nested calls. If a nested call
  ## uses `netxCallRValue` it will reset the value causing an initial call rvalue
  ## to not be one.
  let current = ctx.nextCallRvalue
  ctx.nextCallRValue = true
  body
  ctx.nextCallRValue = current

proc toImpl(fn: PNode): PNode =
  case fn.kind
  of nkSym: result = fn.getImpl # XXX: need to lookup implementation of this symbol! .sym.getImpl
  of nkProcDef: result = fn
  else: doAssert false, "not supported yet " & $fn.kind

proc genParam(jitCtx: JitContext, fn, n: string, typ: PNode): JitNode =
  result = toJitNode(jitCtx.toParam(typ, n), typ.renderTree)
  jitCtx.stack.head().params.add (n, result, typ)

proc genParamName(n: PNode): string =
  result = n.getName()

proc getParamOpt(n: PNode, function: Function): Option[JitNode] =
  case n.kind
  of nkSym, nkIdent:
    for (name, p, node) in function.params:
      if name == n.getName(): return some(p)
  else:
    result = none(JitNode)

proc isLocal(ctx: JitContext, n: PNode): bool =
  doAssert n.kind in {nkIdent, nkSym}
  result = n.getName() in ctx.locals

proc isHiddenPointer(n: PNode): bool =
  result = n.typ.kind == tyVar

proc genNode(ctx: JitContext, body: PNode): JitNode
proc buildArray(ctx: JitContext, n: PNode): JitNode =
  result = initJitNode(jtSeq)
  for i in 0 ..< n.len:
    result.add toJitNode(ctx.toRValue(n[i]), n[i].renderTree)

#proc gcc_jit_context_new_array_access*(ctxt: ptr gcc_jit_context;
#                                      loc: ptr gcc_jit_location;
#                                      `ptr`: ptr gcc_jit_rvalue;
#                                      index: ptr gcc_jit_rvalue): ptr gcc_jit_lvalue {.

proc access(jitCtx: JitContext, n: JitNode, idx: int | JitNode): JitNode =
  ## Accesses the array node. Returns an LValue wrapped in a `JitNode`.
  result = toJitNode(
    jitCtx.ctx.gcc_jit_context_new_array_access(nil,
                                                jitCtx.toRValue(n),
                                                jitCtx.toRValue(idx))
  )

proc assign(ctx: JitContext, lvalue, rvalue: JitNode) =
  ## Performs assignment of an `rvalue` to an `lvalue`
  ##
  ## `lvalue = rvalue`
  case rvalue.kind
  of jtSeq: ## trying to assign an array, do element by element
    ## This code branch is for what normally should be handling of `nkBracket`
    # what we will do instead, as we don't have that yet:
    # 1. use array access to set each element from `ar` in a loop
    # 3. return rvalue of the local array
    # we could optimize the case where this appears in an assignment and just
    # use the lvalue instead of a temp variable. for now easier this way
    for i, el in pairs(rvalue.sons):
      ctx.assign(ctx.access(lvalue, i), el)
  else:
    gcc_jit_block_add_assignment(toPtrBlock(ctx.blckStack.head()), nil,
                                 lvalue.toLValue(),
                                 ctx.toRValue(rvalue))

proc newLocal(ctx: JitContext, typ: JitNode, name: string): JitNode =
  ## Generates a new local variable of the given type from the identifier `ident`
  let local = gcc_jit_function_new_local(toPtrFunction(ctx.stack.head.fn), nil, toJitType(typ), name)
  result = toJitNode(local)
  ctx.locals[name] = result

proc newLocalAsgn(ctx: JitContext, ident: PNode): JitNode =
  # generate a new local variable of the nodes type
  let typ = if ident[2].kind != nkEmpty: ident[2]
            else: ident[0] # instead use type of symbol
  result = ctx.newLocal(ctx.toJitType(typ), ident[0].getName())
  ## `rval` has to be "treated" (might be a call for example)
  if ident[2].kind != nkEmpty:
    withRValue(ctx):
      let rval = ctx.genNode(ident[2])
    # now assign rval to lval
    ctx.assign(result, rval)
  # else this was a `var` section *without* an initialization

proc newBlock(ctx: JitContext, name: string, fn: JitNode): JitNode =
  ## XXX: turn into runtime version returning the code!
  doAssert fn.kind == jtFunction
  result = toJitNode(gcc_jit_function_new_block(toPtrFunction(fn), name.cstring), name)
  ctx.blckStack.push result

proc getVariable(ctx: JitContext, n: PNode): JitNode =
  let paramOpt = getParamOpt(n, ctx.stack.head())
  if paramOpt.isSome:
    result = paramOpt.get
  elif ctx.isLocal(n):
    result = ctx.locals[n.getName()]
  elif n.getName() == "result": # magic result variable if not found here (i.e. not a local of that name)
    # generate result variable using this functions return type and return it
    result = ctx.newLocal(ctx.stack.head.retType, n.getName())
  else:
    doAssert n.kind in {nkIdent, nkSym} and n.getName() in ["true", "false"], "Was instead " & $n.renderTree()
    result = toJitNode(ctx.toRValue(toJitType("bool")))

#proc jitFn(jitCtx: JitContext, fn: PNode, functionKind: gcc_jit_function_kind): JitNode
proc jitFn(jitCtx: JitContext, fn: PNode): JitNode

proc getFunction(ctx: JitContext, n: PNode): JitNode =
  doAssert n.kind in {nkIdent, nkSym}
  #doAssert n.getName() in ctx.fnTab, "Function " & $n.getName() & " not jit'd yet."
  if n.getName() in ctx.fnTab:
    result = ctx.fnTab[n.getName()].fn
  else:
    ## XXX: think about whether this function doesn't motvate that `jitFn` simply
    ## returns the `JitNode` of the `ptr gcc_jit_function` generated by `newFunction`!
    # hmm, `c_printf` needs to be imported still?
    let fn = ctx.jitFn(toImpl(n)) # , GCC_JIT_FUNCTION_EXPORTED)
    #result.add ctx.jitFn(toImpl(n[0]), GCC_JIT_FUNCTION_IMPORTED)
    result = ctx.fnTab[n.getName()].fn

proc jumpDown(ctx: JitContext) =
  let down = ctx.blckStack.pop() # current
  let head = ctx.blckStack.head() # target
  echo "jumping down from ", head, " to ", down
  gcc_jit_block_end_with_jump(toPtrBlock head, nil, toPtrBlock down)

proc jumpTo(ctx: JitContext, to: JitNode) =
  let this = ctx.blckStack.head()
  echo "jumping from ", this, " to ", to
  gcc_jit_block_end_with_jump(toPtrBlock this, nil, toPtrBlock to)

#proc jump(ctx: JitContext, frm, to: PNode): PNode =
#  result = pquote:
#    gcc_jit_block_end_with_jump(@@@!(frm), nil, @@@!(to))

proc jumpWithCond(ctx: JitContext, condNode: PNode) = #ifStmt, cond, ifTrue, ifFalse: PNode) =
  let ifFalse = ctx.blckStack.pop()
  let ifTrue = ctx.blckStack.pop()
  # head is now `ifStmt` condition, so generate the code
  let cond = ctx.genNode(condNode)
  let ifStmt = ctx.blckStack.head()
  echo "jumping if true to ", ifTrue, " else to ", ifFalse, " in cond ", ifStmt
  gcc_jit_block_end_with_conditional(toPtrBlock ifStmt, nil,
                                     ctx.toRValue(cond),
                                     toPtrBlock ifTrue, # if true, jump to body
                                     toPtrBlock ifFalse)

proc deref(ctx: JitContext, n: PNode): JitNode =
  ## Dereferences `n` (an rvalue) and returns the dereferenced value as an
  ## `lvalue`.
  let jitNode = ctx.genNode(n[0])
  result = toJitNode(gcc_jit_rvalue_dereference(ctx.toRValue(jitNode), nil))

proc address(n: JitNode): JitNode =
  ## Get the address of `n`
  result = toJitNode(
    gcc_jit_lvalue_get_address(
      toLValue(n), nil
    ),
    "ptr " & n.name
  )


proc buildArgs(ctx: JitContext, fnName: string, n: PNode): JitNode =
  result = initJitNode(jtSeq)
  ## XXX: use the information we have about the function we call and what types
  ## it needs to possibly hand a reference instead of value!
  let fn = ctx.fnTab[fnName]
  let fnParams = fn.params
  for i in 1 ..< n.len: # skip 0, the call itself
    # if something is an argument of the function, need to convert
    if fnParams.high < i-1:
      doAssert fn.isVariadic, "Number of arguments mismatch despite function not being variadic!"
    ## XXX: fix the next line, if variadic the two indices might not match anymore!
    let param = fnParams[min(i-1, fnParams.high)]
    withRValue(ctx):
      let arg = ctx.genNode(n[i])
    if param[2].isHiddenPointer:
      # get the address of the argument & turn it back into RValue
      result.add toJitNode(ctx.toRValue(address(arg)), n[i].renderTree())
    else:
      result.add toJitNode(ctx.toRValue(arg), n[i].renderTree())

proc genNode(ctx: JitContext, body: PNode): JitNode =
  ## XXX: would have to generate blocks before hand so we can actually jump!
  ## execute the real code (and partially store in the JitContext!)
  #echo body.treerepr, " ============= ", body.renderTree()
  case body.kind
  of nkIdent, nkSym:
    ## XXX: here we don't need to *generate* a JitNode, but rather return it, no?
    ## Given that variables are scoped, maybe associate generated variables by
    ## block (using the name of the blocks)?
    ## i.e. to do: `result = jitCtx.getVar(body.getName())`
    ## which internally checks the current `blckStack` head and returns the
    ## correct one?
    result = ctx.getVariable(body)
  of nkLiterals:
    result = toJitNode(ctx.toRValue(body)) # `literals` will be wrapped by `toRValue`, which makes it safe
  #of nkConv:
  #  result = body
  of nkHiddenStdConv:
    ## XXX: in case of `nkBracket` stored, refers to a `varargs`, need to be flattened
    ## and returned as N arguments. Likely function already indicated as variadic?
    case body[1].kind
    of nkLiterals: result = ctx.genNode(body[1]) ## XXX: use conversion!
    of nkIdent, nkSym: result = ctx.genNode(body[1])
    of nkBracket:
      result = initJitNode(jtSeq)
      for ch in body[1]:
        result.add ctx.genNode(ch)
    of nkDotExpr: result = ctx.genNode(body[1])
    else: doAssert false, "not supported " & $body.treerepr
  of nkCommand, nkCall:
    # perform a call
    # Note: this implies it is of `void` return type, otherwise we
    # would have seen let / var / asgn
    # 1. first a new block
    let fnName = body[0].getName()
    let fnCall = ctx.getFunction(body[0])
    let args = ctx.buildArgs(fnName, body)
    ## XXX: thanks to discardable we can't use `geType` to determine if we need `add_eval`
    #echo "Constructing call: ", fnName, " with RValue? ", ctx.nextCallRValue
    if not ctx.nextCallRvalue:
      addEval(ctx.blckStack.head(), ctx.newContextCall(fnCall, toRaw(args)))
    else:
      result = ctx.newContextCall(fnCall, toRaw(args))
  of nkStmtListExpr, nkStmtList:
    ## XXX: if `expr` need to return something in theory!! only `printf` returns int that is discardable
    result = initJitNode(jtSeq)
    for stmt in body:
      result.add ctx.genNode(stmt)
  of nkLetSection, nkConstSection, nkVarSection:
    ## XXX: differentiate between var and let. Var might not have an rvalue!
    result = initJitNode(jtSeq)
    for ident in body:
      result.add ctx.newLocalAsgn(ident)
  of nkReturnStmt:
    # return the given value
    doAssert body[0].kind == nkAsgn, "Weird, return isn't asgn ? " & $body.treerepr
    ctx.hasExplicitReturn = true
    # return the child [1]
    let resVar = body[0][1]
    let resJitVal = ctx.genNode(resVar)
    ctx.addReturn(resJitVal)
  of nkInfix:
    ## generate an infix RVALUE
    ## Determine whether bool or math first, then call correct function as we get
    ## a different return type?
    let opNode = body[0]
    let kind = jitInfixKind(body)
    let resType = body # result type will be extracted from the type of the full node in `toJitType`
                       # called by `newBinaryOp`!
    let aJ = ctx.genNode(body[1])
    let bJ = ctx.genNode(body[2])
    ## XXX: check the implementation of the infix symbol. If the arguments are not
    ## basic types, then this in fact is actually a call to a procedure with that
    ## infix symbol, which would need to be called instead!
    case kind
    of infixCompare:
      let gccOp = toJitInfixBool(opNode.getName())
      result = ctx.newBinaryOp(gccOp, resType, aJ, bJ)
    of infixMath:
      let typ = body[1].getTypeKind # use type kind of any argument, assuming infix has same types on each side
      let gccOp = toJitInfix(opNode.getName(), typ)
      result = ctx.newBinaryOp(gccOp, resType, aJ, bJ)
  of nkDiscardStmt: ## This would imply throwing away the `rvalue` of this expression
    result = ctx.genNode(body[0]) ## XXX: what should this really do? for now just ignore
  of nkEmpty:
    result = initJitNode(jtEmpty)
  of nkIfStmt, nkIfExpr: ## XXX: same distinction as stmtListExpr and stmtList!
    result = initJitNode(jtSeq)
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

    let numBlocks = ctx.blckStack.len
    # generate the after if block and pop it (needs to be at head of block stack later)
    result.add ctx.newBlock("afterIf_" & ctx.stack.head.node.getName(), ctx.stack.head.fn)
    let afterIfBlck = ctx.blckStack.pop()
    var idx = 0
    # now walk if statements & generate blocks and body code (but not condidion code!)
    for ifBr in body:
      if ifBr.kind == nkElifBranch:
        result.add ctx.newBlock("ifCond_" & $idx & "_" & ctx.stack.head.node.getName(), ctx.stack.head.fn)
      let blckName = if ifBr.kind == nkElifBranch: "ifBody_" else: "elseBody_"
      result.add ctx.newBlock(blckName & $idx & "_" & ctx.stack.head.node.getName(), ctx.stack.head.fn)
      # generate the corresponding code for the body
      result.add ctx.genNode(ifBr[ifBr.high]) # last child contains body
      # add the jump to after the block
      ctx.jumpTo(afterIfBlck)
    # add after block again so it's the head of the block stack
    ctx.blckStack.add afterIfBlck
    # walk in reverse order and generate the correct conditional jumps
    for i in countdown(body.len-1, 0):
      let ifBr = body[i]
      case ifBr.kind
      of nkElifBranch: ctx.jumpWithCond(ifBr[0])
      of nkElse:
        # else branch implies need to pop `afterIf` so that `ifFalse` of the
        # previous if condition jumps to `else` instead of `after`
        discard ctx.blckStack.pop()
      else: doAssert false, $ifBr.kind
    # finally generate the jump call to from the `currentBlck` to the first if condition
    while ctx.blckStack.len > 1:
      ctx.jumpDown()
    discard ctx.blckStack.pop() # remove current block (last one left)
    doAssert ctx.blckStack.len == 0 # no blocks left, down consumed block from before
    ctx.blckStack.add afterIfBlck # add the after block as the new base block
    #doAssert ctx.blckStack.len == numBlocks - 1 # no blocks left, down consumed block from before
    #ctx.blckStack.add afterIfBlck # add the after block as the new base block
  of nkDotExpr:
    ## XXX: need to know if this is an lvalue or an rvalue!
    let xS = ctx.genNode(body[0])
    result = ctx.getFieldAsRValue(ctx.toRValue(xS), body[0], body[1].getName())
  of nkCommentStmt: result = initJitNode(jtEmpty) # ignore
  of nkFastAsgn:
    # handle as `nkAsgn`?
    ## XXX: for now this seems to me to happen in cases like:
    ## FastAsgn
    ## 0/1  Symi sk:ForVar ty:Int flags:{sfUsed, sfCursor} ty:Int sk:Type
    ## 1/1  Symi sk:Var ty:Int flags:{sfUsed, sfFromGeneric} ty:Int sk:Type
    ## where it maps a for var to a regular var. We'll try to just ignore those.
    discard
  of nkAsgn:
    # perform assignment
    let lval = ctx.genNode(body[0])
    let rval = ctx.genNode(body[1])
    ctx.assign(lval, rval)
  of nkBracket:
    ## NOTE: libgccjit from ABI 19 onwards has a constructor for arrays from a
    ## ptr to rvalues!
    ## https://gcc.gnu.org/onlinedocs/jit/topics/expressions.html#c.gcc_jit_context_new_array_constructor
    ##
    result = ctx.buildArray(body)
    #doAssert false, "Cannot create a JitNode from an `nkBracket` without a direct consumer. " &
    #  "libgccjit (for some reason) doesn't allow `lvalue = rvalue` if both are constant size arrays"
  of nkBracketExpr: ## accessor for arrays / seqs etc. *Not* used in case a user defined
                    ## type overloads the `[]` operator though! Those are turned into nkCall
    result = ctx.access(ctx.genNode(body[0]),
                        ctx.genNode(body[1]))
  of nkBlockStmt:
    # 0. get name of the block
    echo "BLOCK STACK BEFORE ", ctx.blckStack
    let numBlocks = ctx.blckStack.len
    let blockName = ctx.getBlockName(body)
    # 1. new block for after
    result = initJitNode(jtSeq)
    result.add ctx.newBlock("afterBlock_" & blockName, ctx.stack.head.fn)
    let afterBlck = ctx.blckStack.pop()
    # 2. new block for block body
    result.add ctx.newBlock(blockName, ctx.stack.head.fn)
    # 3. generate body for block
    result.add ctx.genNode(body[1])
    # 4. add jump from block body to after block
    ctx.jumpTo(afterBlck)
    # 5. jump to block beginning & generate the full chain of jumps
    while ctx.blckStack.len > 1: # numBlocks:
      ctx.jumpDown()
    discard ctx.blckStack.pop() # remove current block (last one left)
    doAssert ctx.blckStack.len == 0 # no blocks left, down consumed block from before
    ctx.blckStack.add afterBlck # add the after block as the new base block
    echo "BLOCK STACK AFTER ", ctx.blckStack
  of nkWhileStmt:
    # similar to `if` and `block`
    # 1. new block for after
    let numBlocks = ctx.blckStack.len
    result = initJitNode(jtSeq)
    result.add ctx.newBlock("afterWhileBlock_" & ctx.stack.head.node.getName(), ctx.stack.head.fn)
    let afterBlck = ctx.blckStack.pop()
    # 2. add block for condition
    result.add ctx.newBlock("whileCond_" & ctx.stack.head.node.getName(), ctx.stack.head.fn)
    let condBlck = ctx.blckStack.head()
    # 3. add block for while body
    result.add ctx.newBlock("whileBody_" & ctx.stack.head.node.getName(), ctx.stack.head.fn)
    # 4. generate body of while
    result.add ctx.genNode(body[1])
    # 5. add jump back to condition
    ctx.jumpTo(condBlck)
    # 6. add after block to stack again (to have stack in order `ifFalse, ifTrue, condition`
    ctx.blckStack.push afterBlck
    # 7. generate while jump with condition
    ctx.jumpWithCond(body[0])
    doAssert ctx.blckStack.len == numBlocks + 1 # while condition & current
    # 8. jump down from current block to while condition
    while ctx.blckStack.len > 1: # numBlocks:
      ctx.jumpDown()
    discard ctx.blckStack.pop() # remove current block (last one left)
    doAssert ctx.blckStack.len == 0 # no blocks left, down consumed block from before
    ctx.blckStack.add afterBlck # add the after block as the new base block
  of nkMixinStmt: discard # nothing to do
  of nkHiddenDeref:
    ## deference the given symbol
    result = ctx.deref(body)
  #of nkForStmt:
  #  echo body.treerepr
  #
  #  doAssert false
  # -> if the following are implemented we're pretty far in functionality already I believe
  # of nkTryStmt: just open a new block
  #   of nkExcept: is a jump target, how to know when? no idea yet
  #   of nkFinally: jump target after last `try`. i.e. pop last block (must have been a `try` and jump here)
  # of nkWhile: condition, goto condition at end of loop if true, else goto after loop
  # of nkPragma: not sure, for now I would just ignore it
  # of nkCaseStmt: similar to if
  #   of nkOfBranch: handled in `nkCaseStmt` same as `elifBranch` and `ofBranch` there
  # of nkTypeDef: define a struct of given body. But in principle this can even be ignored, as it's
  #   irrelevant for us. If we see a variable of some type we don't know, we generate it then and there.
  # left:
  # -> pointer types
  # -> function pointes
  # -> array access (via nkHiddenAddr + nkBracketExpr)
  # implement `cast` using `gcc_jit_context_new_cast`
  # of nkCast
  else:
    debug body.treerepr
    doAssert false, "notsupported yet " & $body.kind

## XXX: implement `echo` by importing `echoBinSafe`, which has signature
## `proc echoBinSafe(x: array[string], numArgs: int)`
## or something like that
#proc echoJit(): PNode =
#  let params = @[JitCtx.toParam(type(ptr cstring), "x"),
#                 JitCtx.toParam(type(cint), "num")] # number of elements in array
#  let fnS = JitCtx.newFunction("echoBinSafe", type(void), params, GCC_JIT_FUNCTION_IMPORTED, isVariadic = false)


#proc jitCalledFns(ctx: JitContext, n: PNode): JitNode =
#  ## NOTE: This could become a pre pass that also registers the kind of returns
#  ## as well as checks for what kind of code flow we have?
#  result = initJitNode(jtSeq)
#  if n.kind in {nkCall, nkCommand}:
#    let nStr = n[0].getName()
#    if nStr notin ctx.seenFns:
#      if n[0].getName() in ["foo"]: ## XXX: DETERMINE BASED ON IMPORTC?
#        result.add ctx.jitFn(toImpl(n[0]), GCC_JIT_FUNCTION_EXPORTED)
#      else:
#        result.add ctx.jitFn(toImpl(n[0]), GCC_JIT_FUNCTION_IMPORTED)
#      ctx.seenFns.incl nStr
#    # else nothing to do
#  for stmt in n:
#    let res = ctx.jitCalledFns(stmt)
#    if res.len > 0:
#      result.add res

proc hasPragma(fn: PNode, pragma: string): bool =
  let pragmas = fn[4]
  for p in pragmas:
    var pName = ""
    case p.kind
    of nkExprColonExpr: pName = p[0].getName()
    of nkIdent: pName = p.getName()
    else: doAssert false, "not possible"
    if pName == pragma: return true

proc getPragmaValue(fn: PNode, pragma: string): PNode =
  let pragmas = fn[4]
  for p in pragmas:
    case p.kind
    of nkExprColonExpr:
      if p[0].getName() == pragma: return p[1]
    of nkIdent: doAssert false, "Ident pragmas have no value!"
    else: doAssert false, "not possible"

proc name(fn: PNode): PNode =
  doAssert fn.kind in {nkProcDef, nkFuncDef}
  result = fn[0]

proc params(fn: PNode): PNode =
  doAssert fn.kind in {nkProcDef, nkFuncDef}, "Not supported kind " & $fn.kind
  result = fn[3]

proc body(fn: PNode): PNode =
  doAssert fn.kind in {nkProcDef, nkFuncDef}
  result = fn[6]

proc getFunctionName(fn: PNode): string =
  ## Returns the name of the function, possibly taking into account and `importc` pragma
  if fn.hasPragma("importc"):
    result = fn.getPragmaValue("importc").getName()
  else:
    result = fn[0].getName()

proc lookupMagic(ctx: JitContext, fn: PNode): JitNode
proc jitFn(jitCtx: JitContext, fn: PNode): JitNode =
  ## This function performs JIT'ing of a given function, which must be a `nkProcDef`.
  ## All relevant parameters (input / output types, pragmas, body) are mapped to
  ## corresponding `libgccjit` calls.
  # 1. first check if it's a magic procedure, if so just generate our custom variant

  let fn = jitCtx.intr.performTransformation(fn[0].sym).ast

  let isMagic = fn.hasPragma("magic")
  if isMagic:
    echo "FOUND MAGIC !!! "
    return jitCtx.lookupMagic(fn)

  # store current information of the calling scope
  let currentNextCallRValue = jitCtx.nextCallRValue
  jitCtx.nextCallRValue = false
  let currentBlckStack = jitCtx.blckStack
  while jitCtx.blckStack.len > 0:
    discard jitCtx.blckStack.pop()

  let numBlocks = jitCtx.blckStack.len

  let params = fn.params
  debug "============================== ", fn.treerepr

  let functionKind = if fn.hasPragma("importc"): GCC_JIT_FUNCTION_IMPORTED
                     else: GCC_JIT_FUNCTION_EXPORTED
  # 1. generate params
  result = initJitNode(jtSeq)
  ## init the `JitContext` object, potentially initiating the full `libgccjit` context
  # get the return type
  let retParam = params[0]
  # construct new function
  let fnName = fn.getFunctionName()
  let fnSymbolName = fn.name.getName()
  let fnObj = newFunction(name = fnName, fnSym = fnSymbolName, retType = jitCtx.toJitType(retParam), node = fn,
                          functionKind = functionKind)
  # push new object to function stack
  jitCtx.stack.push fnObj

  var anyArgumentVarargs = false
  for i in 1 ..< params.len: # skip 0, return, will be used later
    let p = params[i]
    var pType = p[params.len - 2] # second to last is return type, unless there's a default
    if pType.kind == nkEmpty:
      ## attempt to find a default
      pType = p[params.len - 1]
    ## XXX: handle `varargs` and conversions of the types used by `echo`, `varargs[typed, $]`
    ## where the latter argument implies the actual type via a call
    if pType.kind == nkBracketExpr and pType[0].getName() == "varargs":
      anyArgumentVarargs = true
    for j in 0 ..< p.len - 2: # get all parameter names
      let paramName = genParamName(p[j])
      ## XXX: Handle
      ## - a) DONE `nkVarTy` (via `ptr T` & an `address` call)
      ## - b) DONE parameters with default arguments!
      ## - c) handle generics
      ##   -> introduce "is generic" and then pre populate the `jitContext` with
      ##      type nodes for the argument, which we can then use to determine the
      ##      generic. We don't need to be super smart, because the nim compiler
      ##      already did all the checking for us. So we know the arguments are
      ##      correct. Just have to be sure to not ignore `nkHiddenConv` nodes etc
      result.add jitCtx.genParam(fnSymbolName, paramName, pType)
  #if fn.getName() == "inc":
  #  echo fn.treerepr
  #  quit()

  ## XXX: for any blocks remaining at the end of a `jitFn` call, we need to do something,
  ## must never leave it as otherwise we end up trying to jump between functions!!

  let isVariadic = fn.hasPragma("varargs") or anyArgumentVarargs
  ## XXX: really generate the function and store it in the JitContext
  # assign remaining fields to head of stack (by assigning to ref object of function)
  fnObj.isVariadic = isVariadic
  let fnDef = jitCtx.newFunction(fnObj)
  # adjust the `fn` field of the function on top of the stack
  jitCtx.stack.head.fn = fnDef
  # add for later lookup to table
  jitCtx.fnTab[fnSymbolName] = fnObj ## Using name of the symbol to store it! this is what will be used to
                                     ## call by the user.
  result.add fnDef
  if functionKind == GCC_JIT_FUNCTION_IMPORTED: # return early if import
    # pop the parameters of this function and the function itself
    discard jitCtx.stack.pop()

    ## turn into a snapshot -> reset kind of procedure. maybe a `resetAndReturn` template
    jitCtx.nextCallRValue = currentNextCallRValue
    # reset the stack of blocks
    jitCtx.blckStack = currentBlckStack
    #while jitCtx.blckStack.len > numBlocks:
    #  discard jitCtx.blckStack.pop()
    return
  # 3. for any function in body, get the body
  #    and recurse
  ## XXX: not only AST top level of course!
  ## XXX: investigate body for other functions we need to JIT!
  let body = fn.body
  #result.add jitCtx.jitCalledFns(body)
  # 4. generate body of this procedure to be evaluated
  # 4a. generate the block of code for the body
  ## Generate the block for the body & add it to our stack of blocks
  ## Really add block instead of generating code!
  result.add jitCtx.newBlock("blck_body_" & fnSymbolName, fnDef)
  # result.add varBlock
  result.add jitCtx.genNode(body)

  if not jitCtx.hasExplicitReturn:
    ## XXX: change this to automatically return `result` varialbe instead of void!
    ## need to return `result` variable if not empty return
    jitCtx.addReturn(jitCtx.stack.head.retType)

  gcc_jit_function_dump_to_dot(toPtrFunction(fnDef), "/tmp/test.dot")
  #result.add dump
  debug "============================== JIT FN", result.repr

  # pop the parameters of this function
  discard jitCtx.stack.pop()
  jitCtx.nextCallRValue = currentNextCallRValue
  # reset the stack of blocks
  jitCtx.blckStack = currentBlckStack
  #while jitCtx.blckStack.len > numBlocks:
  #  discard jitCtx.blckStack.pop()

## NOTE: embedding the code from the playground here and replacing NimNode
## by PNode and running instead of returning code might be all that's needed to
## build a runtime version of this thing!

import times

proc performTransformation(intr: Interpreter, p: PSym): PSym =
  ## Performs the transformation pass of the given symbol, i.e.
  ## replacing for loops by while loops and so on.
  ##
  ## - for loops -> while loop
  ## - case -> case (unchanged)
  ## - inline iterator -> inlined
  ## - ...?
  ##
  ## Working with the transformed code is very useful for us, as it
  ## requires less logic on our end, i.e. how to JIT inlne iterators
  ## etc.
  ##
  ## After transformation it further injects destructors.
  var trnsf = intr.graph.transformBody(intr.idgen, p, dontUseCache)
  #echo trnsf.treerepr
  trnsf = injectDestructorCalls(intr.graph, intr.idgen, p, trnsf)
  #echo "incl destructors: ", trnsf.treerepr
  #echo trnsf.renderTree()
  #echo p.ast.treerepr
  var p = p
  p.ast[6] = trnsf
  result = p

proc jitAst(intr: Interpreter, p: PNode, name: string) =
  ## Perform JIT compilation of the given Nim AST at runtime by mapping the
  ## nodes to `libgccjit` calls.

  ## XXX: later on we will want to generate child contexts for each JIT compilation snippet
  ## to be able to add more code after having compiled some initial code. Each child
  ## can access the already compiled code!
  # set up a jit context
  let jitCtx = initJitContext(intr, true)
  let jitted = jitFn(jitCtx, p) # , GCC_JIT_FUNCTION_EXPORTED)

  # test compile it:
  var res = gcc_jit_context_compile(jitCtx.ctx)
  if res.isNil:
    echo "nil result"
  # Extract the generated code from "result".
  type
    fnType = proc(c: cstring) {.nimcall.}
    fnTypeNone = proc(): clonglong {.nimcall.}
    fnTypeInt = proc(c: cstring): clonglong {.nimcall.}
    #fnTypeBar = proc(c: Bar) {.nimcall.}
    fnTypeTwo = proc(x, y: int) {.nimcall.}
    fnTypeTwoRet = proc(x, y: int): int {.nimcall.}
    fnTypeVoid = proc() {.nimcall.}
  when true:
    var fn = cast[fnTypeVoid](gcc_jit_result_get_code(res, name))
    if fn.isNil:
      echo "nil fn"
    # Now call the generated function: */
    fn()
  stdout.flushFile()

  gcc_jit_context_release(jitCtx.ctx)
  gcc_jit_result_release(res)

proc getAst(jitCtx: JitContext, code: string, symbol: string): PNode =
  let stream = llStreamOpen(code)
  jitCtx.intr.evalScript(stream)
  let sym = jitCtx.intr.selectRoutine(symbol)
  result = jitCtx.intr.performTransformation(sym).ast
  llStreamClose(stream)

proc lookupInc(ctx: JitContext, fn: PNode): JitNode =
  const magicBody = """
#proc inc*[T](x: var T, y = 1) =
proc inc*(x: var int, y = 1) =
  x = x + y
"""
  let fnAst = ctx.getAst(magicBody, "inc")
  result = ctx.jitFn(fnAst)

proc lookupMagic(ctx: JitContext, fn: PNode): JitNode =
  ## Returns a JIT compiled version of the given magic function
  let fnName = fn.getName()
  case fnName
  of "inc": result = ctx.lookupInc(fn)
  else: doAssert false, "Unknown magic: " & $fnName

  ## XXX: looking up magic procedures should proceed as follows:
  ## 1. replace string compare by magic enum, `"inc"` -> `mInc`
  ## 2. first check via `magicsys.getCompilerProc` if we find this in the compiler
  ##   and if so, we simply need to jit that implementation! `getCompilerProc` returns
  ##   the Nim implementation of many magics
  ## 3. for all others implement functions like the `lookupInc` above.

proc setupInterpreter(moduleName = "/t/script.nim"): Interpreter =
  let std = findNimStdLibCompileTime()
  var paths = newSeq[string]()
  paths.add std
  paths.add std & "/pure"
  paths.add std & "/core"
  paths.add "/home/basti/.nimble/pkgs"
  result = createInterpreter(moduleName, paths, defines = @[])

proc shutdownInterpreter(intr: Interpreter) =
  destroyInterpreter(intr)

template withStream(code: untyped): untyped =
  let stream = llStreamOpen(code)
  intr.evalScript(stream)
  llStreamClose(stream)

proc evalString(code1, code2: string) =
  let intr = setupInterpreter()
  withStream(code1)

  ## XXX: have to apply the transformations when calling `jitFn` internally!
  let bar = intr.selectRoutine("bar")
  #let barT = intr.performTransformation(bar)
  intr.jitAst(bar.ast, "bar")

  withStream(code2)
  let mm = intr.selectRoutine("testMath")
  #let mmT = intr.performTransformation(mm)
  intr.jitAst(mm.ast, "testMath")

  #let fn = intr.selectRoutine("foo")
  #let t0 = epochTime()
  #for i in 0 ..< 100:
  #  jitAst(fn.ast)
  # intr.performTransformation(fn)
  #echo "100 JITs took ", epochTime() - t0, "s, per JIT = ", (epochTime() - t0) / 100.0
  echo magicsys.getCompilerProc(intr.graph, "LengthStr")
  echo magicsys.getCompilerProc(intr.graph, "mLengthStr")
  echo magicsys.getCompilerProc(intr.graph, "len")
  let echoBinSafe =  magicsys.getCompilerProc(intr.graph, "echoBinSafe")
  echo echoBinSafe.ast.treerepr
  echo echoBinSafe.ast.renderTree()
  if true: quit()

  #let bar = intr.selectRoutine("bar")
  #let barT = intr.performTransformation(bar)
  #intr.jitAst(barT.ast, "bar")
  shutdownInterpreter(intr)

let string2 = """
import system/ansi_c
proc testMathImpl(x, y: float): float =
  let z = x * y
  result = x * z

proc testMath*() =
  c_printf("%f\n", testMathImpl(1.34, 532.112))
"""

let runtimeString = """
import system/ansi_c
proc foo*(x, y: int) =
  let z = x + y
  c_printf("z = %i\n", z)
  let a = 5
  if true:
    let b = @[1, 2, 3]
    for el in b:
      echo el
  echo "wel"
  #result = z

import std / strutils
proc barImpl(x, y: int): int =
  var a = [1, 2, 3]
  a[0] = 234
  block:
    let test = 5
  const bb = 123
  #let s = "a string"
  #let isin = "str" in s
  #c_printf("contained ? %i \n", )
  block Another:
    let test = 123
  let z = a[0]
  for i in 0 ..< a.len:
    c_printf("is this working? %i\n", a[i])

  result = x + y + z + bb

proc bar*() =
  c_printf("%i\n", barImpl(10, 11))

proc testNestedBlocks*(x, y: int): int =
  block A:
    let x = 5
    block B:
      let z = 5
      block C:
        let ab = 5
        block D:
          let aba = 5
      result = x + z

let x* = @[1, 2, 3]
echo "Hello World"
"""
evalString(runtimeString, string2)
