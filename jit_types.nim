import std / tables
import libgccjit

type
  JitTypes* = enum
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
  JitNode* = object
    name*: string # optional name field
    case kind*: JitTypes
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
    of jtSeq: sons*: seq[JitNode]
  ## XXX: implement usage of `lineInfo` for `gcc_jit_location` arguments for proper debugging!

  ## A type storing the symbols for a given type
  JitType* = ref object
    name*: string # the name as a string of this type
    typ*: ptr gcc_jit_type
    struct*: ptr gcc_jit_struct # if it corresponds to a struct
    `fields`*: Table[string, JitNode]

proc toJitNode*(x: ptr gcc_jit_object  , name = ""): JitNode = JitNode(name: name, kind: jtObject, obj: x)
proc toJitNode*(x: ptr gcc_jit_location, name = ""): JitNode = JitNode(name: name, kind: jtLocation, loc: x)
proc toJitNode*(x: ptr gcc_jit_type    , name = ""): JitNode = JitNode(name: name, kind: jtType, typ: x)
proc toJitNode*(x: ptr gcc_jit_field   , name = ""): JitNode = JitNode(name: name, kind: jtField, field: x)
proc toJitNode*(x: ptr gcc_jit_struct  , name = ""): JitNode = JitNode(name: name, kind: jtStruct, struct: x)
proc toJitNode*(x: ptr gcc_jit_function, name = ""): JitNode = JitNode(name: name, kind: jtFunction, fn: x)
proc toJitNode*(x: ptr gcc_jit_block   , name = ""): JitNode = JitNode(name: name, kind: jtBlock, blck: x)
proc toJitNode*(x: ptr gcc_jit_rvalue  , name = ""): JitNode = JitNode(name: name, kind: jtRValue, rval: x)
proc toJitNode*(x: ptr gcc_jit_lvalue  , name = ""): JitNode = JitNode(name: name, kind: jtLValue, lval: x)
proc toJitNode*(x: ptr gcc_jit_param   , name = ""): JitNode = JitNode(name: name, kind: jtParam, param: x)
proc toJitNode*(x: ptr gcc_jit_case    , name = ""): JitNode = JitNode(name: name, kind: jtCase, cas: x)

proc toPtrObj*(n: JitNode      ): ptr gcc_jit_object   = n.obj
proc toPtrLoc*(n: JitNode      ): ptr gcc_jit_location = n.loc
proc toPtrType*(n: JitNode     ): ptr gcc_jit_type     = n.typ
proc toPtrField*(n: JitNode    ): ptr gcc_jit_field    = n.field
proc toPtrStruct*(n: JitNode   ): ptr gcc_jit_struct   = n.struct
proc toPtrFunction*(n: JitNode ): ptr gcc_jit_function = n.fn
proc toPtrBlock*(n: JitNode    ): ptr gcc_jit_block    = n.blck
proc toPtrRValue*(n: JitNode   ): ptr gcc_jit_rvalue   = n.rval
proc toPtrLValue*(n: JitNode   ): ptr gcc_jit_lvalue   = n.lval
proc toPtrParam*(n: JitNode    ): ptr gcc_jit_param    = n.param
proc toPtrCase*(n: JitNode     ): ptr gcc_jit_case     = n.cas

proc `$`*(n: JitNode): string =
  result = "JitNode(kind: " & $n.kind & ", name: " & n.name
  if n.kind == jtSeq:
    result.add ", sons: ["
    for el in n.sons:
      result.add $el & ", "
    result.add "]"
  result.add ")"

proc add*(a: var JitNode, b: JitNode) =
  ## Add the given node `b` to the sons of `a`.
  doAssert a.kind == jtSeq
  a.sons.add b

proc len*(n: JitNode): int =
  doAssert n.kind == jtSeq
  result = n.sons.len

proc `[]`*(n: JitNode, idx: int): JitNode =
  doAssert n.kind == jtSeq
  result = n.sons[idx]

proc toRaw*(n: JitNode): seq[ptr gcc_jit_rvalue] =
  doAssert n.kind == jtSeq
  result = newSeq[ptr gcc_jit_rvalue](n.len)
  for i in 0 ..< n.len:
    doAssert n[i].kind == jtRValue
    result[i] = n[i].rval

proc toRaw*(n: seq[JitNode]): seq[ptr gcc_jit_rvalue] =
  result = newSeq[ptr gcc_jit_rvalue](n.len)
  for i in 0 ..< n.len:
    doAssert n[i].kind == jtRValue
    result[i] = n[i].rval

proc initJitNode*(kind: JitTypes): JitNode =
  result = JitNode(kind: kind)

proc initJitType*(name: string): JitType =
  result = JitType(name: name,
                   typ: nil,
                   struct: nil,
                   `fields`: initTable[string, JitNode]())
