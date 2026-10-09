import Verification.Source.EquationAnnotations

/-! Section references follow `verification/RECURSIVE-EQUATIONS.md`. -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-! ### Lowering a source for the source path -/

/-- A generic module value's type, its binders their name placeholders: a
function's signature (receiver, parameters, rest element and result), a
construct signature (parameters and result), or any other type. -/
inductive GenericType where
  | function (receiver : Option Union) (params : List Union) (rest : Option Union) (result : Union)
  | construct (params : List Union) (result : Union)
  | other (type : Union)

def GenericType.map (f : Union → Union) : GenericType → GenericType
  | .function r ps e res => .function (r.map f) (ps.map f) (e.map f) (f res)
  | .construct ps res => .construct (ps.map f) (f res)
  | .other t => .other (f t)

/-- A generic module value: a generic module function, a generic class or a
generic imported value. Its type and its binders' bounds have the binders
as their name placeholders; an instance substitutes them
(`EquationStore.rebind`). -/
structure GenericValue where
  name : String
  pos : Nat × Nat
  binders : List String
  resolution : List ResolutionSlots
  type : Except String GenericType
  bounds : List (String × Option Union)

/-- A source lowered for the source path. -/
structure SourceLowering where
  /-- The store the units grow: the heads, hash-consed and compacted. -/
  store : State
  /-- Each annotation, by its path in the function tree. -/
  annotations : List (String × Union)
  /-- Each array or tuple annotation's parts, by its path. -/
  arrays : List (String × ArrayParts)
  /-- Each imported value's type, by its local name, with its span. -/
  values : List (String × (Nat × Nat) × Union)
  generics : List GenericValue
  /-- Each generic unit's binders, by its path: an owned parameter of the
  unit's head, with its declared bound over those parameters (`enterUnit`). -/
  units : List (String × List (String × Tree × Option Union))
  /-- The module initialization's binders: every generic class's, one per
  name, the first class's. -/
  initBinders : List (String × Tree × Option Union)
  /-- The claims document, its label lists spelled as trees (§9.2). -/
  claims : Json

/-- A generic value's type term: a function or construct signature by its
parts, so that several instances conjoin as one callable; any other type
whole. A rest is the pack of its element (`lowerRest`). -/
def genericType (ctx : Ctx) (term : Json) : M GenericType := do
  match (term.getObjValAs? String "k").toOption with
  | some "function" =>
    fieldsExactly term ["k", "receiver", "params", "rest", "result", "effect", "span"]
    if (← str term "effect") != "unrestricted" then return .other (← lowerType ctx term)
    let recv ← field term "receiver"
    let receiver ← if recv == .null then pure none else some <$> lowerType ctx recv
    let params ← (← arr term "params").toList.mapM (lowerType ctx)
    let restTerm ← field term "rest"
    -- A rest is its element's claim; a pack binder has no claim form.
    if kindOf restTerm == some "pack" then return .other (← lowerType ctx term)
    let rest ← if restTerm == .null then pure none else some <$> lowerType ctx restTerm
    return .function receiver params rest (← lowerType ctx (← field term "result"))
  | some "constructor" =>
    fieldsExactly term ["k", "params", "rest", "result", "span"]
    if (← field term "rest") != .null then return .other (← lowerType ctx term)
    let params ← (← arr term "params").toList.mapM (lowerType ctx)
    return .construct params (← lowerType ctx (← field term "result"))
  | _ => return .other (← lowerType ctx term)

/-- Lower a generic module value's pieces with its binders as placeholders.
Its declared bounds are checked at each instance a call names
(`Scheme.moduleInstances`), not here. -/
private def genericOf (name : String) (pos : Nat × Nat) (path : String) (node : Json) (tps : Array Json)
    (type : List (String × Binding) → M GenericType) : M GenericValue := do
  let (scope, _) ← bindNames [] [] node tps
  let parameters ← sourceParameters tps
  let binders := parameters.flatMap fun (n, r) => ResolutionWire.ownedNames n r
  let t ← tryCatch (do return Except.ok (← type scope)) fun e => pure (.error e)
  let bounds ← tps.toList.mapM fun p => do
    let n ← (str p "name" : Except String String)
    let b := p.getObjValD "bound"
    if b == .null then return (n, none)
    return (n, some (← lowerType { binders := scope, site := s!"{path}: the bound of {n}", checkBounds := false } b))
  return { name, pos, binders, resolution := ResolutionWire.groups parameters, type := t, bounds }

/-- Everything the source path lowers, in one run: the declarations, every
annotation, the imported values, the generic units' binders, the producer's
rows and the claims. -/
def lowerSource (ast claims : Json) : M (List (String × Union) × List (String × (Nat × Nat) × Union) ×
    List GenericValue × List (String × List (String × Tree × Option Union)) ×
    List (String × Tree × Option Union) × Json) := do
  primitives
  let ds := (← get).doc
  let excluded ← match ds[0]? with
    | some d =>
      if d.identity == arrayProtoIdentity then
        let names ← (← arr d.expression "fields").mapM fun f => do PropKey.decode (← field f "name")
        pure (RequestJson.arrayExcludedKeys names.toList)
      else pure (RequestJson.arrayExcludedKeys [])
    | none => pure (RequestJson.arrayExcludedKeys [])
  modify fun s => { s with excluded }
  -- Every declaration: heads now, aliases where they are used.
  for i in [:ds.size] do
    if ds[i]!.isHead then let _ ← declHead i
  -- The realm's array prototype.
  let proto ← protoLabel
  modify fun s => { s with proto := match proto with | .app h _ => some h | _ => none }
  drain
  let functionTrees := (ast.getObjValAs? (Array Json) "functions").toOption.getD #[]
  let annotations ← walk "/functions" [] [] (ast.getObjValD "functions")
  -- Generic module functions: their binders, and their types at them.
  let mut generics : List GenericValue := []
  let mut units : List (String × List (String × Tree × Option Union)) := []
  for (f, i) in functionTrees.toList.zipIdx do
    let tps := (f.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
    if tps.isEmpty then continue
    let path := s!"/functions/{i}"
    let _ ← enterUnit path [] f tps
    units := units ++ [(path, (((← get).unitBinders.lookup path).getD []))]
    let name ← str f "name"
    let pos ← (fromJson? (← field f "namePos") : Except String (Nat × Nat))
    generics := generics ++ [← genericOf name pos path f tps fun scope => do
      -- Its signature by its parameters' annotations: a rest's element, the
      -- claim of a rest being its element's (`Fragment.callableType`).
      let ctx : Ctx := { binders := scope, site := path, checkBounds := false }
      let mut params := []
      let mut rest := none
      for p in ← arr f "params" do
        let ty ← field p "type"
        if ty == .null then
          throw s!"{path}: a generic module function's type needs every parameter's annotation"
        if (p.getObjVal? "rest").isOk then
          if kindOf ty != some "array" || (← bool ty "readonly") then
            throw s!"{path}: a generic module function's rest parameter needs a mutable array contract"
          rest := some (← lowerType ctx (← field ty "element"))
        else params := params ++ [← lowerType ctx ty]
      let result ← field f "retType"
      if result == .null then throw s!"{path}: a generic module function's type needs its result's annotation"
      return .function none params rest (← lowerType ctx result)]
  let init := ast.getObjValD "init"
  let _classes ← classScope init
  let initBinders := ((← get).unitBinders.reverse.filter (·.1.startsWith "/init/")).flatMap (·.2)
    |>.foldl (fun (acc : List (String × Tree × Option Union)) (n, t, B) =>
      if (acc.lookup n).isSome then acc else acc ++ [(n, t, B)]) []
  -- The top-level code reads every generic class's binders by name, each
  -- with its declared bound, as a class's own code does.
  let ctors : List Json := match init with
    | .arr sts => sts.toList.flatMap fun st => match st.getObjVal? "bindings" with
      | .ok (.arr bs) => bs.toList.filterMap fun b =>
        let c := b.getObjValD "init"
        if (c.getObjValAs? String "k").toOption == some "ctor" &&
            ((c.getObjValAs? (Array Json) "typeParams").toOption.getD #[]).size > 0 then some c else none
      | _ => []
    | _ => []
  let (initScope, initBounds) ← ctors.foldlM (fun (acc : List (String × Binding) × List (Tree × Union)) c => do
    let tps := (c.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
    let (scope, bounds) ← bindNames [] [] c tps
    let fresh := scope.filter fun (n, _) => (acc.1.lookup n).isNone
    return (acc.1 ++ fresh, acc.2 ++ bounds.filter fun (q, _) => !acc.2.any (·.1 == q))) ([], [])
  let initAnnotations ← walk "/init" initScope initBounds init
  -- Generic classes: their construct signatures at their binders.
  let .arr sts := init | throw "the module initialization is a list"
  for (st, si) in sts.toList.zipIdx do
    if (st.getObjValAs? String "k").toOption != some "const" then continue
    let .ok (.arr bs) := st.getObjVal? "bindings" | continue
    for (b, bi) in bs.toList.zipIdx do
      let ctor := b.getObjValD "init"
      if (ctor.getObjValAs? String "k").toOption != some "ctor" then continue
      let tps := (ctor.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
      if tps.isEmpty then continue
      let path := s!"/init/{si}/bindings/{bi}"
      let name ← str b "name"
      let pos ← (fromJson? (← field b "namePos") : Except String (Nat × Nat))
      generics := generics ++ [← genericOf name pos path ctor tps fun scope => do
        genericType { binders := scope, site := s!"{path}/annot", checkBounds := false } (← field b "annot")]
  -- Imported values: a generic one is instantiated at each call.
  let mut values := []
  let document := ast.getObjValD "declarations"
  for (v, vi) in ((document.getObjValAs? (Array Json) "values").toOption.getD #[]).toList.zipIdx do
    fieldsExactly v ["binding", "declaration", "construct", "typeParams", "type"]
    let binding ← field v "binding"
    fieldsExactly binding ["local", "imported", "specifier", "span"]
    let name ← str binding "local"
    let span ← (fromJson? (← field binding "span") : Except String (Nat × Nat))
    let _ ← bool v "construct"
    let path := s!"/declarations/values/{vi}"
    let tps ← arr v "typeParams"
    if tps.isEmpty then
      values := values ++ [(name, span, ← lowerType { site := path } (← field v "type"))]
    else
      let _ ← enterUnit path [] v tps
      units := units ++ [(path, (((← get).unitBinders.lookup path).getD []))]
      let generic ← genericOf name span path v tps fun scope => do
        genericType { binders := scope, site := path, checkBounds := false } (← field v "type")
      generics := generics ++ [generic]
  -- The stable non-thenable family resolution descriptors are relative to:
  -- the intrinsic module's `%Stable%`, by its declaration identity.
  for d in ds do
    if (d.identity.getObjValAs? String "module").toOption == some "skjs/intrinsics" &&
        (d.identity.getObjValAs? String "name").toOption == some "%Stable%" then
      if !d.parameters.isEmpty || !d.bases.isEmpty then
        throw "the stable-value intrinsic takes no parameters"
      let stable ← lowerType { site := "/declarations/definitions/%Stable%" } d.expression
      modify fun s => { s with nativeStable := some stable }
  -- The producer's rows and the claims.
  let types ← arr claims "types"
  let P ← (producerRows types : Except String ProducerRows)
  modify fun s => { s with rows := P }
  -- Rows 0 to 3 are the primitive values: null, true, false, undefined.
  let primitives : List (GraphRow Nat) := [.clauses [.nul], .clauses [.boolLit true],
    .clauses [.boolLit false], .clauses [.undef]]
  if types.toList.take 4 != primitives.map toJson then
    throw "invalid source claims: the type table must start with the primitives"
  let claims ← documentForm (fun A => do return unionJson (← claimUnion [] A)) claims
  drain
  return (annotations ++ initAnnotations, values, generics, units, initBinders, claims)


end Verification.EquationLowering
