import Verification.Source.EquationCore
import Verification.Source.ResolutionWire

/-! Section references follow `verification/RECURSIVE-EQUATIONS.md`. -/
namespace Verification.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-! ### Units and annotations -/

/-- The fields of the function tree that hold a source annotation. -/
def annotationFields : List String :=
  ["annot", "functionType", "bagType", "type", "result", "bound", "retType"]

/-- The terms a unit's scheme reads: its parameters' and result's types and
its binders' bounds. -/
def unitTerms (node : Json) : Json :=
  let tps := (node.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
  let params := (node.getObjValAs? (Array Json) "params").toOption.getD #[]
  .arr (tps.map (·.getObjValD "bound") ++ params.map (·.getObjValD "type") ++
    #[node.getObjValD "retType", node.getObjValD "result", node.getObjValD "type"])

/-- Decode ownership before allocating source input and associated slots. -/
def sourceParameters (tps : Array Json) : Except String (List (String × Option ResolutionWire.Slots)) := do
  let parameters ← tps.toList.mapM fun p => do
    fieldsExactly p ["name", "bound", "resolution"]
    return (← str p "name", ← fromJson? (← field p "resolution"))
  ResolutionWire.validateOwnership parameters
  return parameters

/-- Expanded allocation entries give every source-value slot its source view.
Qualification remains on the owning scheme; associated observation and result
slots have no independent scheme bounds. -/
def expandedSourceParameters (tps : Array Json) : Except String (Array Json) := do
  let parameters ← sourceParameters tps
  return (tps.toList.zip parameters).flatMap (fun (p, (name, slots)) =>
    let entry (n : String) (bound : Json) := Json.mkObj [
      ("name", toJson n), ("bound", bound), ("resolution", .null)]
    entry name (if p.getObjValD "bound" == .null then
      Json.mkObj [("k", .str "atom"), ("name", .str "unknown"), ("span", toJson ([0, 0] : List Nat))]
      else p.getObjValD "bound") ::
      (slots.map fun s => s.names.map (entry ·
        (Json.mkObj [("k", .str "atom"), ("name", .str "unknown"), ("span", toJson ([0, 0] : List Nat))]))).getD []) |>.toArray

def sourceNames (tps : Array Json) : Except String (List String) := do
  return (← sourceParameters tps).flatMap fun (n, s) => ResolutionWire.ownedNames n s

/-- Enter a generic unit's binders: the unit is a head of its own, lifted over
the enclosing binders its scheme names, whose binders are `bound(f, A⃗, j)`,
met with its bound when it has one (§8.1). -/
def enterUnit (path : String) (scope : List (String × Binding)) (node : Json) (tps : Array Json) :
    M (List (String × Binding)) := do
  let tps ← expandedSourceParameters tps
  let names ← sourceNames tps
  let ctx : Ctx := { binders := scope, site := path, source := true }
  let items := (mentions names (unitTerms node)).filter fun it => match it with
    | .binder n => (scope.lookup n).isSome
    | _ => false
  let args ← items.mapM fun it => (ctxValue ctx it : Except String Union)
  let name := (node.getObjValAs? String "name").toOption.getD path
  let d : Draft :=
    { name, kind := .unit path, kinds := items.map fun _ => .value,
      binders := names.map fun n => ⟨n, .value⟩ }
  let u ← alloc s!"unit|{path}" d fun u => some (.unit u (liftedCtx ctx items u) node)
  let rigid := names.zipIdx.map fun (n, j) => (n, (⟨false, [mkBound u args j]⟩ : Binding))
  let mut inner := rigid ++ scope
  let mut bounds : List (Tree × Union) := []
  let mut bounded : List (String × Binding × Option Union) := []
  for (p, (n, r)) in tps.toList.zip rigid do
    let b := p.getObjValD "bound"
    if b == .null then bounded := bounded ++ [(n, r, none)]
    else
      let B ← lowerType { ctx with binders := inner, bounds }
        b
      bounded := bounded ++ [(n, r, some B)]
      inner := (n, ⟨false, meetUnions [r.value, B]⟩) :: inner
      if let [q] := r.value then bounds := bounds ++ [(q, B)]
  let bindings := bounded.map fun (n, r, B) => match B with
    | none => (n, r)
    | some B => (n, (⟨false, meetUnions [r.value, B]⟩ : Binding))
  let owned := bounded.filterMap fun (n, r, B) => match r.value with
    | [t] => some (n, t, B)
    | _ => none
  modify fun s => { s with scopes := (path, bindings) :: s.scopes, unitBinders := (path, owned) :: s.unitBinders }
  return bindings ++ scope

/-- A node's binders as their name placeholders: what each name stands for
is decided where the unit or closure is checked (`EquationStore.rebind`). A
name used as an argument pack is a placeholder of that kind. -/
def bindNames (scope : List (String × Binding)) (bounds : List (Tree × Union)) (node : Json)
    (tps : Array Json) : M (List (String × Binding) × List (Tree × Union)) := do
  let tps ← expandedSourceParameters tps
  let names ← sourceNames tps
  let bound ← names.mapM fun n => do
    let pack := (binderUse n node).pack
    return (n, (⟨pack, [← placeholder n (if pack then .arguments else .value)]⟩ : Binding))
  let inner := bound ++ scope
  -- A value binder's declared bound, read where an application over it
  -- checks a declaration's bound (`closeObligation`).
  let mut out := bounds
  for (p, (n, b)) in tps.toList.zip bound do
    let t := p.getObjValD "bound"
    if t == .null || b.pack then continue
    let B ← lowerType { binders := inner, bounds := out, site := s!"the bound of {n}", source := true } t
    if let [q] := b.value then out := (q, B) :: out
  return (inner, out)

/-- An array or tuple type's parts. -/
def arrayParts (ctx : Ctx) (term : Json) : M (Option ArrayParts) := do
  match kindOf term with
  | some "array" =>
    let element ← lowerType ctx (← field term "element")
    return some ⟨[], [], some element, ← bool term "readonly", ← field term "presence"⟩
  | some "tuple" =>
    let required ← (← arr term "required").toList.mapM (lowerType ctx)
    let optional ← (← arr term "optional").toList.mapM (lowerType ctx)
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure none else some <$> lowerType ctx restTerm
    return some ⟨required, optional, rest, ← bool term "readonly", ← field term "presence"⟩
  | _ => return none

/-- Every annotation of the function tree lowered in its scope, keyed by its
path. A binder is its name placeholder (`bindNames`). -/
partial def walk (path : String) (scope : List (String × Binding)) (bounds : List (Tree × Union))
    (j : Json) : M (List (String × Union)) := do
  match j with
  | .arr xs => return (← xs.toList.zipIdx.mapM fun (x, i) => walk s!"{path}/{i}" scope bounds x).flatten
  | .obj kvs =>
    let tps := (j.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
    let (scope, bounds) ← if tps.isEmpty then pure (scope, bounds) else bindNames scope bounds j tps
    let ctx : Ctx := { binders := scope, site := path, bounds, source := true }
    let mut out := []
    for (name, value) in kvs.toList do
      let here := s!"{path}/{name}"
      if annotationFields.contains name && value != .null then
        out := out ++ [(here, ← lowerType { ctx with site := here } value)]
        if let some parts ← arrayParts { ctx with site := here } value then
          modify fun s => { s with arrayAnnotations := s.arrayAnnotations ++ [(here, parts)] }
      else if name == "typeArgs" then
        let .arr values := value | throw s!"{here}: type arguments are a list"
        for (v, i) in values.toList.zipIdx do
          out := out ++ [(s!"{here}/{i}", ← lowerType { ctx with site := s!"{here}/{i}" } v)]
      else if name != "resolution" then out := out ++ (← walk here scope bounds value)
    return out
  | _ => return []

/-- The top-level code's scope: every generic class's binders, one per
spelling. -/
def classScope (init : Json) : M (List (String × Binding)) := do
  let mut scope := []
  let .arr sts := init | return []
  for (st, si) in sts.toList.zipIdx do
    if kindOf st != some "const" then continue
    let .ok (.arr bs) := st.getObjVal? "bindings" | continue
    for (b, bi) in bs.toList.zipIdx do
      let init := b.getObjValD "init"
      if kindOf init != some "ctor" then continue
      let tps := (init.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
      if tps.isEmpty then continue
      let inner ← enterUnit s!"/init/{si}/bindings/{bi}/init" [] init tps
      for (n, v) in inner do
        if (scope.lookup n).isNone then scope := scope ++ [(n, v)]
  return scope


end Verification.EquationLowering
