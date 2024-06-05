import compiler / nir / [nirinsts, nirtypes, nirlineinfos, nirfiles, cir]
import std / [intsets, tables]
import compiler / ic / [bitabs, rodfiles]
# Type graph

type
  ObjectType* = enum TypedefStruct, TypedefUnion

  TypeList* = object
    processed*: IntSet
    s*: seq[(TypeId, ObjectType)]

proc add(dest: var TypeList; elem: TypeId; decl: ObjectType) =
  if not containsOrIncl(dest.processed, int(elem)):
    dest.s.add (elem, decl)

type
  TypeOrder* = object
    forwardedDecls*, ordered*: TypeList
    typeImpls*: Table[string, TypeId]
    lookedAt*: IntSet

proc traverseObject(types: TypeGraph; lit: Literals; c: var TypeOrder; t: TypeId)

proc recordDependency(types: TypeGraph; lit: Literals; c: var TypeOrder; parent, child: TypeId) =
  var ch = child
  var viaPointer = false
  while true:
    case types[ch].kind
    of APtrTy, UPtrTy, AArrayPtrTy, UArrayPtrTy:
      viaPointer = true
      ch = elementType(types, ch)
    of LastArrayTy:
      ch = elementType(types, ch)
    else:
      break

  case types[ch].kind
  of ObjectTy, UnionTy:
    let decl = if types[ch].kind == ObjectTy: TypedefStruct else: TypedefUnion
    let obj = c.typeImpls.getOrDefault(lit.strings[types[ch].litId])
    if viaPointer:
      c.forwardedDecls.add obj, decl
    else:
      if not containsOrIncl(c.lookedAt, obj.int):
        traverseObject(types, lit, c, obj)
      c.ordered.add obj, decl
  of ArrayTy:
    if viaPointer:
      c.forwardedDecls.add ch, TypedefStruct
    else:
      if not containsOrIncl(c.lookedAt, ch.int):
        traverseObject(types, lit, c, ch)
      c.ordered.add ch, TypedefStruct
  else:
    discard "uninteresting type as we only focus on the required struct declarations"

proc traverseObject(types: TypeGraph; lit: Literals; c: var TypeOrder; t: TypeId) =
  for x in sons(types, t):
    case types[x].kind
    of FieldDecl:
      recordDependency types, lit, c, t, x.firstSon
    of ObjectTy:
      # inheritance
      recordDependency types, lit, c, t, x
    else: discard

proc traverseTypes*(types: TypeGraph; lit: Literals; c: var TypeOrder) =
  for t in allTypes(types):
    if types[t].kind in {ObjectDecl, UnionDecl}:
      assert types[t.firstSon].kind == NameVal
      c.typeImpls[lit.strings[types[t.firstSon].litId]] = t

  for t in allTypesIncludingInner(types):
    case types[t].kind
    of ObjectDecl, UnionDecl:
      traverseObject types, lit, c, t
      let decl = if types[t].kind == ObjectDecl: TypedefStruct else: TypedefUnion
      c.ordered.add t, decl
    of ArrayTy:
      traverseObject types, lit, c, t
      c.ordered.add t, TypedefStruct
    else: discard
