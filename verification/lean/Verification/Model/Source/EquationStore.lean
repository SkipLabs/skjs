import Verification.Model.Source.EquationLowering
import Verification.Model.Source.SourceExtraction

/-! The label store over recursive equations (RECURSIVE-EQUATIONS §8, §9.2).
Extraction grows the lowering's heads (`EquationLowering.State`), its labels
closed trees (`Tree`): a union of clauses, a scheme over fresh binders and a
bounded binder's meet become heads with lifted templates, and a binder the
source spells by its name is read as the label a unit or closure gives it
(`rebind`). A label's row is its head's template instantiated at its
arguments, which leaves every application inside unexpanded, exactly as
`Equations.row` reads it, so no family is enumerated.

A checked request is over the equations the extracted heads present,
validated by `Equations.ofRaw` once extraction is done (`freeze`): its labels
are the closed labels of those equations, and its graph is their
`Equations.graph` (`Checked`). -/
namespace Verification.Model.EquationStore
open Lean EquationGraphs EquationLowering PositiveGraphs PositiveNormalization PositiveRules
  PositiveCertificates LabelStore RequestJson CallEffects

abbrev State := EquationLowering.State

/-! ### Rows -/

/-- An application's row: its head's template at its arguments, a local its
owned parameter (`Equations.baseRow`). -/
def instantiateRow (h : Nat) (args : Args) (body : GraphRow Tree (List Tree)) : GraphRow Tree :=
  let argF (i : Nat) : Union := ((args.toList[i]?).map Types.toList).getD []
  let locF (j : Nat) : Union := [.bound h args j]
  let sub (U : Union) : Union := U.flatMap (treeSubst argF locF)
  body.map (fun t => (sub [t]).headD t) sub

/-- A label's row, not a meet's (`Equations.baseRow`). -/
def baseRow (s : State) (t : Tree) : GraphRow Tree :=
  match t with
  | .app h args => match s.heads[h]?.bind (·.body) with
    | some body => instantiateRow h args body
    | none => .clauses []
  | .bound h _ j => match s.heads[h]?.bind (·.binders[j]?) with
    | some b => .param t b.name b.kind
    | none => .clauses []
  | .var _ _ k => .param t "var" k
  | _ => .clauses []

/-- A label's row (`Equations.row`): a meet's from its parts' rows. -/
def rowOf (s : State) (t : Tree) : GraphRow Tree :=
  match t with
  | .meet ps => meetRowOf (ps.toList.map fun q => (q, baseRow s q))
  | t => baseRow s t

/- Whether a tree is a closed label of the heads (`Tree.scoped` at no
parameter and no local). -/
mutual
partial def closedTree (s : State) : Tree → Bool
  | .app h args => (s.heads[h]?.any fun d => d.kinds.length == args.toList.length) && closedArgs s args
  | .bound h args j =>
    (s.heads[h]?.any fun d => d.kinds.length == args.toList.length && j < d.binders.length) &&
      closedArgs s args
  | .argument _ | .local _ => false
  | .var .. => true
  | .meet ps => ps.toList.all fun t => closedTree s t && !t.isMeet
partial def closedArgs (s : State) (args : Args) : Bool :=
  args.toList.all fun ts => ts.toList.all (closedTree s)
end

/-- The realm's arrays, where the heads state any: `ArrayProto` and the keys
it provides. -/
def realm (s : State) : Option (ArrayRealm Tree) :=
  if s.arrays then s.proto.map fun p => ⟨[mkApp p []], s.excluded⟩ else none

def graph (s : State) : NormalGraph Tree := NormalGraph.ofRowMap (rowOf s) (realm s)

/-! ### Growing the store -/

/-- Run a lowering step on the store. A step that fails leaves an open tree,
which no store holds (`closedTree`), so a request mentioning it is refused
rather than read at another type. -/
def grow (s : State) (m : M Tree) : State × Tree :=
  match m.run s with
  | .ok (t, s) => (s, t)
  | .error _ => (s, .argument 0)

/-- Whether a clause is an array's: it owns the array store. -/
def arrayShaped (c : Clause (List Tree)) : Bool :=
  c.presentKeys.contains CallArguments.arrayStoreField

def intern (s : State) (cs : List (Clause (List Tree))) : State × Tree :=
  let s := if cs.any arrayShaped then { s with arrays := true } else s
  grow s (internLifted "type" cs)

def lookup (s : State) (cs : List (Clause (List Tree))) : Option Tree :=
  let (key, args) := internKey s.heads cs
  (s.keys.get? key).map fun h => mkApp h args

/-- A value parameter within clauses and further parameters, `p ⊓ cs ⊓ also`:
the meet label of its parts (§3.3), the clauses a head of their own. -/
def bounded (s : State) (p : Tree) (cs : List (Clause (List Tree))) (also : List Tree) : State × Tree :=
  let (s, part) := if cs == [.top] then (s, none) else
    let (s, l) := intern s cs
    (s, some l)
  match also ++ part.toList with
  | [] => (s, p)
  | rest => (s, canonMeet (p :: rest))

/-- A name placeholder's name, if it is one. -/
def placeholderName (s : State) : Tree → Option String
  | .var o i _ => if o == nameOwner then (s.names[i]?).map (·.1) else none
  | _ => none

/-- A label with the named binders read as `θ` gives them. -/
def rebind (s : State) (θ : List (String × List Tree)) (t : Tree) : List Tree :=
  normUnion (treeReplace (fun u => (placeholderName s u).bind fun n => θ.lookup n) t)

/-! ### What a diagnostic shows (OBLIGATION-DIAGNOSTICS, "The label projection") -/

/-- A label's spelling: an application as its head's name at its arguments
(`Promise<number | R>`), an owned parameter as its binder's name. -/
partial def spell (s : State) : Tree → String
  | .app h args =>
    let name := ((s.heads[h]?).map (·.name)).getD s!"#{h}"
    if args.toList.isEmpty then name
    else name ++ "<" ++ ", ".intercalate (args.toList.map fun ts => spellUnion s ts.toList) ++ ">"
  | .bound h _ j => (((s.heads[h]?).bind (·.binders[j]?)).map (·.name)).getD s!"#{h}.{j}"
  | .meet ps => " & ".intercalate (ps.toList.map (spell s))
  | .var o i _ => if o == nameOwner then ((s.names[i]?).map (·.1)).getD "?" else
      if o == freshOwner then ((s.fresh[i]?)).getD "?" else s!"?{o}.{i}"
  | .argument i => s!"arg {i}"
  | .local j => s!"local {j}"
where
  spellUnion (s : State) (U : List Tree) : String :=
    if U.isEmpty then "never" else " | ".intercalate (U.map (spell s))

/-- Whether a label is shown by a name: anything but a nullary head's
application. -/
def named : Tree → Bool
  | .app _ args => !args.toList.isEmpty
  | _ => true

/-- The labels a row names. -/
def rowLabels (r : GraphRow Tree) : List Tree :=
  match r with
  | .clauses cs => cs.flatMap fun c => c.operands.flatten
  | .scheme bs sigs bounds rests =>
    bs ++ sigs.flatMap (fun a => a.operands.flatten) ++ bounds.flatMap (fun (b, U) => b :: U) ++
      rests.flatMap fun a => a.operands.flatten
  | .param l _ _ => [l]
  | .meet p cs ps => p :: ps ++ cs.flatMap fun c => c.operands.flatten

/-- The projection of `mentioned`: positions for them and for the labels
their rows name, `depth` row references deep; past that, a label is an
opaque named row. -/
def projectWith (row : Tree → GraphRow Tree) (name : Tree → String) (mentioned : List Tree)
    (depth : Nat) : Projection Tree := Id.run do
  let mut order : Array Tree := #[]
  let mut index : Std.HashMap Tree Nat := {}
  let mut expanded : Std.HashMap Tree Unit := {}
  let mut frontier : List Tree := []
  for t in mentioned do
    if !index.contains t then
      index := index.insert t order.size
      order := order.push t
      frontier := frontier ++ [t]
  for _ in [0:depth] do
    let mut next : List Tree := []
    for t in frontier do
      expanded := expanded.insert t ()
      for u in rowLabels (row t) do
        if !index.contains u then
          index := index.insert u order.size
          order := order.push u
          next := next ++ [u]
    frontier := next
  let at_ (t : Tree) : Nat := (index.get? t).getD 0
  let rows := order.toList.map fun t =>
    if expanded.contains t then (row t).map at_ (·.map at_) else .clauses []
  let names := order.toList.zipIdx.filterMap fun (t, i) =>
    if named t || !expanded.contains t then some (i, name t) else none
  return { rows, position := at_, names }

/-! ### The store -/

instance : ToJson State where
  toJson s := .arr (s.heads.map fun d => Json.mkObj ([
      ("name", toJson d.name),
      ("parameters", toJson (d.kinds.zipIdx.map fun (k, i) =>
        Json.mkObj [("name", toJson s!"T{i}"), ("kind", toJson k)]))] ++
    (if d.binders.isEmpty then [] else [("binders", toJson (d.binders.map fun b =>
        Json.mkObj [("name", toJson b.name), ("kind", toJson b.kind)]))]) ++
    [("body", match d.body with
      | some b => toJson b
      | none => .null)]))

/-- The equations' own spelling (§9.2): each head's name, parameters, binders
and template. The realm is what the templates state: the prototype an
array's clause views, and the keys that prototype's row provides. -/
instance : FromJson State where
  fromJson? j := do
    let heads ← (← j.getArr?).mapM fun h => do
      let fields := ["name", "parameters", "body"] ++ if (h.getObjVal? "binders").isOk then ["binders"] else []
      CellClaims.fieldsExactly h fields
      let kinds ← (← (← h.getObjVal? "parameters").getArr?).mapM fun p => do
        CellClaims.fieldsExactly p ["name", "kind"]
        let _ ← p.getObjValAs? String "name"
        p.getObjValAs? ParameterKind "kind"
      let binders ← match h.getObjVal? "binders" with
        | .ok bs => (← bs.getArr?).mapM fun b => do
          CellClaims.fieldsExactly b ["name", "kind"]
          return (⟨← b.getObjValAs? String "name", ← b.getObjValAs? ParameterKind "kind"⟩ : Binder)
        | .error _ => pure #[]
      if (h.getObjVal? "binders").isOk && binders.isEmpty then throw "binders are left out when there are none"
      let body : GraphRow Tree (List Tree) ← fromJson? (← h.getObjVal? "body")
      let kind : HeadKind := match body with
        | .clauses _ => if kinds.isEmpty then .primitive else .literal
        | _ => .scheme
      return ({ name := ← h.getObjValAs? String "name", kind, kinds := kinds.toList,
                binders := binders.toList, body := some body } : Draft)
    let keys := (List.range heads.size).foldl (fun (m : Std.HashMap String Nat) h =>
      match heads[h]!.kind, heads[h]!.body with
      | .primitive, some (.clauses cs) => if m.contains s!"ground|{reprStr cs}" then m
          else m.insert s!"ground|{reprStr cs}" h
      | _, _ => m) {}
    let arrayProtos : List (List Tree) := heads.toList.flatMap fun d => match d.body with
      | some (.clauses cs) => cs.filterMap fun c => if arrayShaped c then
          (match c with
            | .refs a bs vs .. => ((a :: bs).flatten ++ vs).lookup CallArguments.protoField
            | _ => none)
          else none
      | _ => []
    let (arrays, proto, excluded) ← match arrayProtos.eraseDups with
      | [] => pure (false, none, [])
      | [[.app p args]] =>
        if !args.toList.isEmpty then throw "an array's prototype is a nullary head's application"
        let cs := match heads[p]?.bind (·.body) with
          | some (.clauses cs) => cs
          | _ => []
        pure (true, some p, arrayExcludedKeysOf cs)
      | _ => throw "every array views one prototype, a nullary head's application"
    return { doc := #[], heads, keys, arrays, proto, excluded }

instance : Store State Tree where
  graph := graph
  row := rowOf
  valid := closedTree
  wellFormed s := s.heads.all (·.body.isSome)
  labels s := (List.range s.heads.size).filterMap fun h =>
    if s.heads[h]!.kinds.isEmpty then some (mkApp h []) else none
  bound s := s.heads.size
  arrayProto s := match s.proto with
    | some p => mkApp p []
    | none => mkApp 0 []
  lookup := lookup
  project s mentioned depth := projectWith (rowOf s) (spell s) mentioned depth
  images s := finiteInstanceImages (graph s)
  intern := intern
  binder _ name := .error s!"the binder {name} is read as its unit gives it, not by its name alone"
  binders s names :=
    let (s, ls) := names.foldl (fun (s, ls) n => let (s, l) := grow s (freshBinder n); (s, ls ++ [l])) (s, [])
    (s, ls)
  bounded := bounded
  scheme s bs sigs bounds rests := grow s (schemeOver bs sigs bounds rests)
  rebind := rebind
  substitute _ σ t := normUnion (treeReplace (fun u => (σ.lookup u).map ([·])) t)

/-! ### Checked requests: the equations, frozen -/

/-- The four primitive values' heads are nullary heads 0 to 3. -/
structure Primitive (E : Equations) : Prop where
  nul : (Tree.app 0 .nil).scoped E.signature 0 0 = true
  tru : (Tree.app 1 .nil).scoped E.signature 0 0 = true
  fls : (Tree.app 2 .nil).scoped E.signature 0 0 = true
  undef : (Tree.app 3 .nil).scoped E.signature 0 0 = true

def primitive (E : Equations) : Except String (PLift (Primitive E)) :=
  if h : (Tree.app 0 .nil).scoped E.signature 0 0 = true ∧ (Tree.app 1 .nil).scoped E.signature 0 0 = true ∧
      (Tree.app 2 .nil).scoped E.signature 0 0 = true ∧ (Tree.app 3 .nil).scoped E.signature 0 0 = true then
    .ok ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩
  else .error "the equations' first four heads are the primitive values"

/-- A closed label of `E`. `p` fixes the primitive values' labels. -/
def CheckedLabel (E : Equations) (_ : Primitive E) : Type := Label E.signature

/-- A checked label's tree. -/
def CheckedLabel.tree {E : Equations} {p : Primitive E} (l : CheckedLabel E p) : Tree :=
  (l : Label E.signature).1

/-- Whether a tree holds a placeholder: a binder no unit or closure read. -/
partial def hasPlaceholder : Tree → Bool
  | t@(.var ..) => isPlaceholder t
  | .app _ args | .bound _ args _ => args.toList.any fun ts => ts.toList.any hasPlaceholder
  | .meet ps => ps.toList.any hasPlaceholder
  | _ => false

section
variable {E : Equations} {p : Primitive E}

instance : Labels (CheckedLabel E p) where
  toHashable := ⟨fun l => hash l.tree⟩
  toOrd := ⟨fun a b => compare a.tree b.tree⟩
  toToJson := ⟨fun l => Tree.toJson l.tree⟩
  toFromJson := ⟨fun j => do
    let t ← Tree.fromJson j
    if hasPlaceholder t then throw "a label names a binder no unit or closure reads"
    let l : Label E.signature ← Label.ofTree E.signature t
    return l⟩
  toRepr := ⟨fun l n => reprPrec l.tree n⟩
  decEq := inferInstanceAs (DecidableEq (Label E.signature))
  nul := (⟨.app 0 .nil, p.nul⟩ : Label E.signature)
  tru := (⟨.app 1 .nil, p.tru⟩ : Label E.signature)
  fls := (⟨.app 2 .nil, p.fls⟩ : Label E.signature)
  undef := (⟨.app 3 .nil, p.undef⟩ : Label E.signature)

end

/-- Either image check: both are proved, so accepting what either accepts is
sound. -/
def eitherImages {ι : Type} [DecidableEq ι] {G : NormalGraph ι} (a b : InstanceImageCheck G) :
    InstanceImageCheck G where
  check bs c := a.check bs c || b.check bs c
  sound bs c hlen hkinds h η := by
    cases ha : a.check bs c
    · simp only [ha, Bool.false_or] at h
      exact b.sound bs c hlen hkinds h η
    · exact a.sound bs c hlen hkinds ha η

/-- The store of a checked request: the extracted heads, whose validated
equations are `E`. It no longer grows. -/
structure Checked (E : Equations) (p : Primitive E) where
  heads : State

section
variable {E : Equations} {p : Primitive E}

instance : ToJson (Checked E p) := ⟨fun c => toJson c.heads⟩
instance : FromJson (Checked E p) := ⟨fun j => do return ⟨← fromJson? j⟩⟩

/-- A tree as a label of `E`, if it is one. -/
def Checked.label? (t : Tree) : Option (CheckedLabel E p) := Label.ofTree? t

instance : StoreView (Checked E p) (CheckedLabel E p) where
  graph _ := E.graph
  row _ l := E.row l
  valid _ _ := true
  wellFormed _ := true
  labels _ := (List.range E.signature.length).filterMap fun h => Checked.label? (mkApp h [])
  bound _ := E.signature.length
  arrayProto _ := ((E.realm.bind (·.proto.head?)) : Option (Label E.signature)).getD
    (Labels.nul : CheckedLabel E p)
  lookup c cs := (lookup c.heads (cs.map (Clause.map (·.map Subtype.val)))).bind Checked.label?
  project c mentioned depth :=
    let pr := projectWith (fun t => match (Label.ofTree? t : Option (Label E.signature)) with
        | some l => (E.row l).map Subtype.val (·.map Subtype.val)
        | none => .clauses []) (spell c.heads)
      (mentioned.map CheckedLabel.tree) depth
    { rows := pr.rows, position := fun l => pr.position l.tree, names := pr.names }
  images _ := eitherImages (finiteInstanceImages E.graph) E.instanceImageCheck

@[simp] theorem Checked.graph_eq (c : Checked E p) :
    (StoreView.graph c : NormalGraph (CheckedLabel E p)) = E.graph := rfl

end

/-- Extracted heads, frozen: their validated equations and the store over
them. -/
structure Frozen where
  equations : Equations
  primitive : Primitive equations
  store : Checked equations primitive

/-- **Freezing.** The heads become equations only through the validator
(`Equations.ofRaw`, §9.2): scope, arity and lexicality, constructor-headed
templates binding exactly their locals, meet normal form, a kind and variance
per parameter. A head lowered from the declarations declares its proposed
variance, a later one `inv`; no rule reads a variance at this stage. -/
def freeze (s : State) : Except String Frozen := do
  let bodies ← s.heads.mapM fun d => match d.body with
    | some b => pure b
    | none => throw s!"{d.name}: its row was never lowered"
  let v := (Array.range s.heads.size).map fun h =>
    match s.variances[h]? with
    | some v => if v.size == s.heads[h]!.kinds.length then v else s.heads[h]!.kinds.toArray.map fun _ => .inv
    | none => s.heads[h]!.kinds.toArray.map fun _ => .inv
  let E ← Equations.ofRaw (rawHeads s.heads bodies v)
  let E := { E with realm := if s.arrays then realmOf E s.proto s.excluded else none }
  let ⟨p⟩ ← primitive E
  return ⟨E, p, ⟨s⟩⟩

/-! ### Requests over the frozen equations -/

deriving instance ToJson, FromJson for DirectProof.Plan

/-- A value with tree labels as the same value over `F`'s labels: through
its spelling, which is the labels' (§9.2), so a label outside the equations
is refused. -/
def over {α β : Type} [ToJson α] [FromJson β] [ToJson β] (a : α) : Except String β :=
  decodeStrict (toJson a)

/-- An extracted unit's request over the frozen equations. The program is
the extracted one; every label is read as `F`'s. -/
def SourceRequest.over (F : Frozen) (r : SourceExtraction.SourceRequest State Tree) :
    Except String (SourceExtraction.SourceRequest (Checked F.equations F.primitive)
      (CheckedLabel F.equations F.primitive)) := do
  let obligations ← r.obligations.mapM fun o => do
    return ({ pos := o.pos, sequent := ← EquationStore.over o.sequent, plan := ← EquationStore.over o.plan,
              role := o.role, context := o.context } : ExpressionClaims.Required _)
  let claims ← EquationStore.over r.claims
  let result ← EquationStore.over r.result
  let inputs ← EquationStore.over r.inputs
  let codes ← EquationStore.over r.codes
  let hints ← EquationStore.over r.hints
  let nodePlans ← EquationStore.over r.nodePlans
  let request : RequestJson.Request (Checked F.equations F.primitive) (CheckedLabel F.equations F.primitive) :=
    { types := F.store, program := r.program, claims := claims, result := result, start := r.start,
      inputs := inputs, codes := codes }
  return { toRequest := request, obligations := obligations, sourceMap := r.sourceMap,
           assertions := r.assertions, cuts := r.cuts, hints := hints, codeSources := r.codeSources,
           nodePlans := nodePlans }

end Verification.Model.EquationStore
