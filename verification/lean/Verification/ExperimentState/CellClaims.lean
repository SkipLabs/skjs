import Verification.ExperimentState.SourceTypes

/-! Single-field record claims at the invariant-cell boundary. This module does
not lower TypeScript objects. It validates a bounded export and refuses to pick
one side when SKJS's read and write types differ. The plain-cell interpretation
excludes arrays, callable objects, accessors and hidden object behavior. -/
namespace Verification.ExperimentState.CellClaims
open Lean ProgramTyping PositiveRules

def fieldsExactly (j : Json) (keys : List String) : Except String Unit := do
  let fields ← j.getObj?
  if fields.toList.length != keys.length || !(fields.toList.all (fun p => keys.contains p.1)) then
    throw "unexpected fields in the cell record claim"

private def plainMode (j : Json) (name : String) : Except String Unit := do
  let mode ← jStr (← jField j name)
  if mode != "unknown" && mode != "absent" then throw s!"unsupported cell object mode: {name}"

def primitive (j : Json) : Except String Core.Ty := do
  fieldsExactly j ["top","atoms"]
  for atom in ← jArr j "atoms" do
    let tag ← jStr (← jField atom "a")
    if ["booleanlit","stringlit","numberlit"].contains tag then
      fieldsExactly atom ["a","v"]
    else fieldsExactly atom ["a"]
  decodeTy j

structure FieldClaim where
  read : Core.Ty
  write : Core.Ty

/-- The accepted record is interpreted as one required slot named `value`.
The schema cannot distinguish data properties from accessors; the source gate
must establish plain-data allocation before using this interpretation. Positive
call, construct, array, index, symbol and extra-field requirements are excluded
by this bounded schema. Synthetic index markers describe exporter bookkeeping,
not runtime permissions; their internal inference variables are not interpreted.
Absence and unknown modes have the same interpretation
within the plain-cell fragment; this is not full TypeScript object semantics. -/
def decode (j : Json) : Except String FieldClaim := do
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
  let field ← match fields with
    | [f] => pure f
    | _ => throw "expected exactly one cell field"
  fieldsExactly field ["name","optional","read","write"]
  if (← jStr (← jField field "name")) != "value" then throw "cell field must be named value"
  if ← (← jField field "optional").getBool? then throw "optional fields are not invariant cells"
  return ⟨← primitive (← jField field "read"), ← primitive (← jField field "write")⟩

/-- Equality is after exact primitive normalization. No widening of either side
is allowed; readonly fields and different read/write contracts are rejected. -/
def agreeContract (read write : Core.Ty) : Except String (Ty Nat) := do
  let A ← SourceTypes.translate read
  let B ← SourceTypes.translate write
  if A = B then return A
  throw "cell read and write types do not describe the same invariant"

def translate (j : Json) : Except String (Ty Nat) := do
  let f ← decode j
  agreeContract f.read f.write

theorem agreeContract_checked {read write : Core.Ty} {A}
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

theorem translate_checked {j : Json} {A} (h : translate j = .ok A) :
    ∃ f, decode j = .ok f ∧ agreeContract f.read f.write = .ok A := by
  unfold translate at h
  cases hd : decode j with
  | error e => simp only [hd] at h; contradiction
  | ok f =>
    simp only [hd] at h
    exact ⟨f,rfl,h⟩

def interpretation (A : Ty Nat) : Fam := refT (meaning SourceTypes.graph A)

/-- The accepted invariant preserves both supplied primitive membership tests,
using the existing exact translation theorem. No new semantic axioms are used. -/
theorem agreeContract_exact {read write : Core.Ty} {A u v}
    (h : agreeContract read write = .ok A) (hv : SourceTypes.value u = .ok v) (n W) :
    (Core.mem u read ↔ meaning SourceTypes.graph A n W v) ∧
    (Core.mem u write ↔ meaning SourceTypes.graph A n W v) := by
  obtain ⟨hr,hw⟩ := agreeContract_checked h
  exact ⟨SourceTypes.translate_exact hr hv n W, SourceTypes.translate_exact hw hv n W⟩

theorem translate_exact {j : Json} {A u v}
    (h : translate j = .ok A) (hv : SourceTypes.value u = .ok v) (n W) :
    ∃ f, decode j = .ok f ∧
      (Core.mem u f.read ↔ meaning SourceTypes.graph A n W v) ∧
      (Core.mem u f.write ↔ meaning SourceTypes.graph A n W v) := by
  obtain ⟨f,hf,hc⟩ := translate_checked h
  exact ⟨f,hf,agreeContract_exact hc hv n W⟩

/-- The eight canonical primitive invariants have fixed reference labels. -/
def referenceLabel (A : Ty Nat) : Nat :=
  3 + (if A.contains 0 then 1 else 0) +
    (if A.contains 1 then 2 else 0) + (if A.contains 2 then 4 else 0)

theorem reference_encode (t : Core.Ty) :
    expand SourceTypes.graph [referenceLabel (SourceTypes.encode t)] =
      [.refs (SourceTypes.encode t) []] := by
  cases hn : SourceTypes.admits t .vnull <;>
    cases ht : SourceTypes.admits t (.vbool true) <;>
    cases hf : SourceTypes.admits t (.vbool false) <;>
    simp [referenceLabel, SourceTypes.encode, hn, ht, hf, expand,
      SourceTypes.graph, SourceTypes.types]

/-- The graph label used by source extraction denotes exactly the accepted
cell invariant, at every world and budget. -/
theorem reference_exact {j : Json} {A} (h : translate j = .ok A) (n W v) :
    meaning SourceTypes.graph [referenceLabel A] n W v ↔ interpretation A n W v := by
  obtain ⟨f,_,hc⟩ := translate_checked h
  have ht := (agreeContract_checked hc).1
  unfold SourceTypes.translate at ht
  split at ht
  · cases ht
    rw [expand_sem, reference_encode]
    simp [PositiveNormalization.semList, Tower.setSem, PositiveNormalization.sem,
      ReferenceConjunctions.refsT, interpretation]
  · contradiction

#print axioms reference_exact
#print axioms translate_exact
#print axioms agreeContract_exact
end Verification.ExperimentState.CellClaims
