import Verification.Model.Source.SourceTypes

/-! Single-field record claims at the invariant-cell boundary. This module does
not lower TypeScript objects. It validates a bounded export and refuses to pick
one side when SKJS's read and write types differ. The plain-cell interpretation
excludes arrays, callable objects, accessors and hidden object behavior. -/
namespace Verification.Model.CellClaims
open Lean ProgramTyping PositiveRules SourceTypes

def fieldsExactly (j : Json) (keys : List String) : Except String Unit := do
  let fields ← j.getObj?
  if fields.toList.length != keys.length || !(fields.toList.all (fun p => keys.contains p.1)) then
    throw s!"unexpected fields: expected {keys}, got {fields.toList.map Prod.fst}"

private def plainMode (j : Json) (name : String) : Except String Unit := do
  let mode ← jStr (← jField j name)
  if mode != "unknown" && mode != "absent" then throw s!"unsupported cell object mode: {name}"

def primitive (j : Json) : Except String Claim.Ty := do
  fieldsExactly j ["top","atoms"]
  for atom in ← jArr j "atoms" do
    let tag ← jStr (← jField atom "a")
    if ["booleanlit","stringlit","numberlit","bigintlit"].contains tag then
      fieldsExactly atom ["a","v"]
    else fieldsExactly atom ["a"]
  decodeTy j

structure FieldClaim where
  name : PropKey
  read : Claim.Ty
  write : Claim.Ty

/-- A field name: a string key as its JSON string, a symbol key as
`{"symbol": id}`. -/
def _root_.Verification.Model.PropKey.decode (j : Json) : Except String PropKey :=
  match j with
  | .str name => .ok (.str name)
  | j => do
    fieldsExactly j ["symbol"]
    return .sym (← (← jField j "symbol").getNat?)

/-- The accepted record is interpreted as one required slot per named field.
The schema cannot distinguish data properties from accessors; the source gate
must establish plain-data allocation before using this interpretation. Positive
call, construct, array, index, symbol and extra-field requirements are excluded
by this bounded schema. Synthetic index markers describe exporter bookkeeping,
not runtime permissions; their internal inference variables are not interpreted.
Absence and unknown modes have the same interpretation
within the plain-cell fragment; this is not full TypeScript object semantics. -/
def decodeFields (j : Json) : Except String (List (PropKey × Json × Json × Bool)) := do
  fieldsExactly j ["top","atoms"]
  if ← (← jField j "top").getBool? then throw "top is not a cell contract"
  let atoms ← jArr j "atoms"
  let atom ← match atoms with
    | [a] => pure a
    | _ => throw "expected a single record atom"
  fieldsExactly atom ["a","fields","indexes","call","construct","array"]
  if (← jStr (← jField atom "a")) != "record" then throw "expected a record atom"
  let indexes ← jField atom "indexes"
  fieldsExactly indexes ["string","number","symbol"]
  for kind in ["string","number","symbol"] do
    let mode ← jStr (← jField indexes kind)
    if mode != "absent" && mode != "synthetic" then
      throw "real index signatures are not invariant cells"
  plainMode atom "call"
  plainMode atom "construct"
  plainMode atom "array"
  let fields ← jArr atom "fields"
  if fields.isEmpty then throw "a record with no field has no location"
  let out ← fields.mapM fun field => do
    fieldsExactly field ["name","optional","read","write"]
    let name ← PropKey.decode (← jField field "name")
    return (name, ← jField field "read", ← jField field "write",
      ← (← jField field "optional").getBool?)
  let names := out.map Prod.fst
  if names.eraseDups.length != names.length then throw "duplicate field name in a record"
  return out

/-- A record's required fields: an optional one is refused where only
required cells are read. -/
def decodeShapes (j : Json) : Except String (List (PropKey × Json × Json)) := do
  (← decodeFields j).mapM fun (name, read, write, optional) => do
    if optional then throw "optional fields are not invariant cells"
    return (name, read, write)

/-- The single-field case, for the places that accept exactly one cell. -/
def decodeShape (j : Json) : Except String (PropKey × Json × Json) := do
  match ← decodeShapes j with
  | [f] => return f
  | _ => throw "expected exactly one cell field"

/-- Primitive contracts also support exact claim membership and point observations. -/
def decode (j : Json) : Except String (List FieldClaim) := do
  (← decodeShapes j).mapM fun (name, read, write) => do
    return ⟨name, ← primitive read, ← primitive write⟩

/-- Equality is after exact primitive normalization. No widening of either side
is allowed; readonly fields and different read/write contracts are rejected. -/
def agreeContract (read write : Claim.Ty) : Except String (Ty Nat) := do
  let A ← SourceTypes.translate read
  let B ← SourceTypes.translate write
  if A = B then return A
  throw "cell read and write types do not describe the same invariant"

theorem agreeContract_checked {read write : Claim.Ty} {A}
    (h : agreeContract read write = .ok A) :
    SourceTypes.translate read = .ok A ∧ SourceTypes.translate write = .ok A := by
  unfold agreeContract at h
  cases hr : SourceTypes.translate read with
  | error e => simp only [hr] at h; contradiction
  | ok R =>
    cases hw : SourceTypes.translate write with
    | error e => simp only [hr,hw] at h; contradiction
    | ok W =>
      simp only [hr,hw] at h
      change (if R = W then Except.ok R else
        Except.error "cell read and write types do not describe the same invariant") = .ok A at h
      split at h
      · rename_i he
        cases h
        exact ⟨rfl,by rw [he]⟩
      · contradiction

/-- A record's fields, each under the one contract its read and write agree on. -/
def translateFields : List FieldClaim → Except String (List (PropKey × Ty Nat))
  | [] => .ok []
  | c :: cs =>
    match agreeContract c.read c.write, translateFields cs with
    | .ok A, .ok rest => .ok ((c.name, A) :: rest)
    | .error e, _ => .error e
    | _, .error e => .error e

def translate (j : Json) : Except String (List (PropKey × Ty Nat)) := do
  translateFields (← decode j)

theorem translateFields_spec : ∀ {cs fs}, translateFields cs = .ok fs →
    cs.map FieldClaim.name = fs.map Prod.fst ∧
    ∀ p ∈ cs.zip fs, agreeContract p.1.read p.1.write = .ok p.2.2 := by
  intro cs
  induction cs with
  | nil =>
    intro fs h
    cases h
    exact ⟨rfl, by simp⟩
  | cons c cs ih =>
    intro fs h
    unfold translateFields at h
    split at h
    · rename_i A rest hA hr
      cases h
      obtain ⟨hn, hall⟩ := ih hr
      refine ⟨by simp [hn], ?_⟩
      intro p hp
      rw [List.zip_cons_cons] at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hA
      · exact hall p hp
    · contradiction
    · contradiction

theorem translate_checked {j : Json} {fs} (h : translate j = .ok fs) :
    ∃ cs, decode j = .ok cs ∧ cs.map FieldClaim.name = fs.map Prod.fst ∧
      ∀ p ∈ cs.zip fs, agreeContract p.1.read p.1.write = .ok p.2.2 := by
  unfold translate at h
  cases hd : decode j with
  | error e => simp only [hd] at h; contradiction
  | ok cs =>
    simp only [hd] at h
    exact ⟨cs, rfl, translateFields_spec h⟩

/-- The record a reference label stands for: each named field under the family
its contract denotes, of an object meeting the realm's array invariant, as
every record type's is. -/
def interpretation (T : Table) (fs : List (PropKey × Ty Nat)) : Fam := fun n W v =>
  recT (ReferenceConjunctions.famsOf (meaning (graph T)) fs) n W v ∧
    PositiveGraphs.realmInvariant (graph T) (realmValues (graph T)) (.refs fs [] []) n W v

/-- The accepted invariant preserves both supplied primitive membership tests,
using the existing exact translation theorem. No new semantic axioms are used. -/
theorem agreeContract_exact {T : Table} (hT : initial <+: T) {read write : Claim.Ty} {A u v}
    (h : agreeContract read write = .ok A) (hv : SourceTypes.value u = .ok v) (n W) :
    (Claim.mem u read ↔ meaning (graph T) A n W v) ∧
    (Claim.mem u write ↔ meaning (graph T) A n W v) := by
  obtain ⟨hr,hw⟩ := agreeContract_checked h
  exact ⟨SourceTypes.translate_exact hT hr hv n W, SourceTypes.translate_exact hT hw hv n W⟩

/-- Field by field, the label a record's contract gets denotes exactly the
values its claim admits — for reads and for writes alike, since the two must
agree before a field is accepted. -/
theorem translate_exact {T : Table} (hT : initial <+: T) {j : Json} {fs u v}
    (h : translate j = .ok fs) (hv : SourceTypes.value u = .ok v) (n W) :
    ∃ cs, decode j = .ok cs ∧ cs.map FieldClaim.name = fs.map Prod.fst ∧
      ∀ p ∈ cs.zip fs,
        (Claim.mem u p.1.read ↔ meaning (graph T) p.2.2 n W v) ∧
        (Claim.mem u p.1.write ↔ meaning (graph T) p.2.2 n W v) := by
  obtain ⟨cs,hf,hnames,hc⟩ := translate_checked h
  exact ⟨cs,hf,hnames,fun p hp => agreeContract_exact hT (hc p hp) hv n W⟩

/-- A conjunction is written inside the atom that carries one, as `and`. The
operands are the same single-contract atoms, decoded by the same decoder: the
key is removed and each part checked on its own, so nothing here relaxes what a
contract may be. -/
def conjuncts (atom : Json) : Except String (List Json) := do
  let fields ← atom.getObj?
  let plain := Json.mkObj (fields.toList.filter (fun p => p.1 != "and"))
  match atom.getObjVal? "and" with
  | .error _ => return [plain]
  | .ok rest =>
    let others ← rest.getArr?
    if others.isEmpty then throw "an empty conjunction is not a contract"
    for other in others.toList do
      if (other.getObjVal? "and").toOption.isSome then
        throw "nested conjunction in a cell contract"
    return plain :: others.toList

/-- The label of a location under one record contract. -/
def reference (fs : List (PropKey × Ty Nat)) : Lowering Nat := use (.refs fs [] [])

/-- The label of a location under one record contract with readonly views:
the invariant fields and, separately, the fields read through a capability. -/
def viewReference (fs vs : List (PropKey × Ty Nat)) : Lowering Nat := use (.refs fs [] vs)

/-- The one-field spelling, for the places that still speak of a single cell. -/
def cellReference (A : Ty Nat) : Lowering Nat := reference [(valueField, A)]

/-- Lexicographic order on label lists, for canonical operand order. -/
def before : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && before as bs)

/-- Field maps compare by name first, then by the labels their contracts got. -/
def beforeFields : List (PropKey × Ty Nat) → List (PropKey × Ty Nat) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    a.1.before b.1 || (a.1 == b.1 && (before a.2 b.2 || (a.2 == b.2 && beforeFields as bs)))

/-- A location under every contract in the conjunction. Conjunction is
commutative and idempotent, so the operands are sorted and deduplicated, and a
conjunction of one contract is the plain cell. -/
def conjunction (atom : Json) : Lowering Nat := do
  let parts ← conjuncts atom
  let types ← parts.mapM fun part =>
    translate (Json.mkObj [("top",toJson false),("atoms",toJson [part])])
  let first :: rest := (types.mergeSort beforeFields).eraseDups
    | throw "an empty conjunction is not a contract"
  use (.refs first rest [])

/-- The reference label denotes exactly the cell invariant, over any table
holding its row, at every world and budget. -/
theorem reference_exact {T : Table} {fs : List (PropKey × Ty Nat)}
    (hm : RequestJson.Row.clauses [.refs fs [] []] ∈ T) (n W v) :
    meaning (graph T) [label T (.refs fs [] [])] n W v ↔ interpretation T fs n W v := by
  rw [label_meaning hm]
  simp only [clauseSem, PositiveGraphs.rowSem, interpretation]
  refine and_congr ?_ Iff.rfl
  simp [PositiveNormalization.semWithArgs, ReferenceConjunctions.refsT,
    ReferenceConjunctions.famsOf, viewT]
  exact fun h => ⟨recT_optT_nil h, MethodMembers.methodT_nil _ _ _⟩

/-- Interning a reference yields a table holding its row and its label there. -/
theorem reference_run {fs : List (PropKey × Ty Nat)} {T T' : Table} {l}
    (h : (reference fs).run T = .ok (l, T')) :
    RequestJson.Row.clauses [.refs fs [] []] ∈ T' ∧ l = label T' (.refs fs [] []) ∧ T <+: T' :=
  use_spec h

#print axioms reference_exact
#print axioms translate_exact
#print axioms agreeContract_exact
end Verification.Model.CellClaims
