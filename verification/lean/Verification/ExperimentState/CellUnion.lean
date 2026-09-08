import Verification.ExperimentState.CellClaims

/-! Exact absorption of redundant read/write record alternatives at the claim
boundary. This is a schema law about allowed reads and required writes, not an
inference rule for retaining observations of mutable storage. Every surviving
record must still have equal read/write meanings at the invariant-cell boundary. -/
namespace Verification.ExperimentState.CellUnion
open Lean ProgramTyping PositiveRules

structure Contract where
  read : List Nat
  write : List Nat
  deriving DecidableEq

/-- `Reads` are possible read results; `Writes` are accepted write inputs.
The law below is independent of how those capabilities are implemented. Absorption additionally
keeps the storage invariant fixed, as required by the point-assertion interpretation. -/
def Satisfies (c : Contract) (Reads Writes : Nat → Prop) : Prop :=
  (∀ a, Reads a → a ∈ c.read) ∧ (∀ a, a ∈ c.write → Writes a)

def covers (a b : Contract) : Bool :=
  a.read.all b.read.contains && decide (a.write = b.write)

theorem covers_sound {a b Reads Writes} (h : covers a b = true)
    (ha : Satisfies a Reads Writes) : Satisfies b Reads Writes := by
  simp only [covers, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  exact ⟨fun x hx => h.1 x (ha.1 x hx), fun x hx => ha.2 x (h.2 ▸ hx)⟩

def select (cs : List Contract) (c : Contract) : Contract :=
  if c.read == c.write then c else
    (cs.find? fun d => d.read == d.write && covers c d).getD c

/-- A replacement is an existing invariant alternative. We never invent a
wider contract, eliminate an unsupported field, or use another non-invariant
alternative as an intermediate approximation. -/
theorem select_spec {cs c} (hc : c ∈ cs) :
    select cs c ∈ cs ∧ ∀ Reads Writes,
      Satisfies c Reads Writes → Satisfies (select cs c) Reads Writes := by
  unfold select
  split
  · exact ⟨hc,fun _ _ h => h⟩
  · cases hf : cs.find? (fun d => d.read == d.write && covers c d) with
    | none => simp only [Option.getD_none]; exact ⟨hc,fun _ _ h => h⟩
    | some d =>
      simp only [Option.getD_some]
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true] at hp
      exact ⟨hm,fun _ _ h => covers_sound hp.2 h⟩

def normalize (cs : List Contract) : List Contract := cs.map (select cs)

def UnionSatisfies (cs : List Contract) (Reads Writes : Nat → Prop) : Prop :=
  ∃ c ∈ cs, Satisfies c Reads Writes

/-- Absorption preserves the whole union of read/write requirements in both
 directions, for arbitrary read and write capabilities. -/
theorem normalize_exact (cs Reads Writes) :
    UnionSatisfies (normalize cs) Reads Writes ↔ UnionSatisfies cs Reads Writes := by
  constructor
  · rintro ⟨d,hd,hs⟩
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
    exact ⟨select cs c,(select_spec hc).1,hs⟩
  · rintro ⟨c,hc,hs⟩
    exact ⟨select cs c,List.mem_map.mpr ⟨c,hc,rfl⟩,(select_spec hc).2 _ _ hs⟩

def decode (atom : Json) : Except String Contract := do
  let f ← CellClaims.decode (Json.mkObj [("top",toJson false),("atoms",toJson [atom])])
  return ⟨← SourceTypes.translate f.read, ← SourceTypes.translate f.write⟩

/-- All arms are validated before absorption, including their field and object
modes. A remaining non-invariant arm rejects the entire union. -/
def translate (atoms : List Json) : Except String (List (Ty Nat)) := do
  let cs ← atoms.mapM decode
  (normalize cs).mapM fun c => do
    if c.read == c.write then return [CellClaims.referenceLabel c.read]
    throw "cell read and write types do not describe the same invariant"

#print axioms normalize_exact
end Verification.ExperimentState.CellUnion
