import Verification.Model.Programs.CellClaims

/-! Exact absorption of redundant read/write record alternatives at the claim
boundary. This is a schema law about allowed reads and required writes, not an
inference rule for retaining observations of mutable storage. Every surviving
record must still have equal read/write meanings at the invariant-cell boundary. -/
namespace Verification.Model.CellUnion
open Lean ProgramTyping PositiveRules LabelStore

variable {ι : Type}

/-- One field's read and write capabilities. A record alternative states one
of these per named field. -/
structure FieldContract (ι : Type) where
  name : PropKey
  read : List ι
  write : List ι
  deriving DecidableEq

abbrev Contract (ι : Type) := List (FieldContract ι)

/-- `Reads` are possible read results; `Writes` are accepted write inputs, both
per field. The law below is independent of how those capabilities are
implemented. Absorption additionally keeps the storage invariant fixed, as
required by the point-assertion interpretation. -/
def Satisfies (c : Contract ι) (Reads Writes : PropKey → ι → Prop) : Prop :=
  ∀ f ∈ c, (∀ a, Reads f.name a → a ∈ f.read) ∧ (∀ a, a ∈ f.write → Writes f.name a)

def coversField [DecidableEq ι] (a b : FieldContract ι) : Bool :=
  a.name == b.name && a.read.all b.read.contains && decide (a.write = b.write)

/-- Every field the replacement states is covered by a field of the same name. -/
def covers [DecidableEq ι] (a b : Contract ι) : Bool := b.all fun f => a.any fun g => coversField g f

theorem covers_sound [DecidableEq ι] {a b : Contract ι} {Reads Writes} (h : covers a b = true)
    (ha : Satisfies a Reads Writes) : Satisfies b Reads Writes := by
  intro f hf
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp h f hf)
  simp only [coversField, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem, decide_eq_true_eq] at hc
  obtain ⟨hr,hw⟩ := ha g hg
  exact ⟨fun x hx => hc.1.2 x (hr x (hc.1.1 ▸ hx)), fun x hx => hc.1.1 ▸ hw x (hc.2 ▸ hx)⟩

def invariant [DecidableEq ι] (c : Contract ι) : Bool := c.all fun f => f.read == f.write

/-- A readonly field accepts no write: its write capability is `never`. -/
def readonly [DecidableEq ι] (f : FieldContract ι) : Bool := f.write == []

/-- Every field is invariant or readonly: a record with views. -/
def viewed [DecidableEq ι] (c : Contract ι) : Bool := c.all fun f => f.read == f.write || readonly f

def select [DecidableEq ι] (cs : List (Contract ι)) (c : Contract ι) : Contract ι :=
  if invariant c then c else
    (cs.find? fun d => invariant d && covers c d).getD c

/-- A replacement is an existing invariant alternative. We never invent a
wider contract, eliminate an unsupported field, or use another non-invariant
alternative as an intermediate approximation. -/
theorem select_spec [DecidableEq ι] {cs : List (Contract ι)} {c} (hc : c ∈ cs) :
    select cs c ∈ cs ∧ ∀ Reads Writes,
      Satisfies c Reads Writes → Satisfies (select cs c) Reads Writes := by
  unfold select
  split
  · exact ⟨hc,fun _ _ h => h⟩
  · cases hf : cs.find? (fun d => invariant d && covers c d) with
    | none => simp only [Option.getD_none]; exact ⟨hc,fun _ _ h => h⟩
    | some d =>
      simp only [Option.getD_some]
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true] at hp
      exact ⟨hm,fun _ _ h => covers_sound hp.2 h⟩

def normalize [DecidableEq ι] (cs : List (Contract ι)) : List (Contract ι) := cs.map (select cs)

def UnionSatisfies (cs : List (Contract ι)) (Reads Writes : PropKey → ι → Prop) : Prop :=
  ∃ c ∈ cs, Satisfies c Reads Writes

/-- Absorption preserves the whole union of read/write requirements in both
 directions, for arbitrary read and write capabilities. -/
theorem normalize_exact [DecidableEq ι] (cs : List (Contract ι)) (Reads Writes) :
    UnionSatisfies (normalize cs) Reads Writes ↔ UnionSatisfies cs Reads Writes := by
  constructor
  · rintro ⟨d,hd,hs⟩
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hd
    exact ⟨select cs c,(select_spec hc).1,hs⟩
  · rintro ⟨c,hc,hs⟩
    exact ⟨select cs c,List.mem_map.mpr ⟨c,hc,rfl⟩,(select_spec hc).2 _ _ hs⟩

section
variable {σ : Type} [Labels ι] [Store σ ι]

/-- A record alternative, lowered where the table can grow: a numeric field
contract is interned rather than refused for being outside the four fixed
primitive labels. -/
def decode (atom : Json) : SourceTypes.Lowering σ (Contract ι) := do
  let fs ← liftM (CellClaims.decode
    (Json.mkObj [("top",toJson false),("atoms",toJson [atom])]) : Except String _)
  fs.mapM fun f => do
    return ⟨f.name, ← SourceTypes.translateArm f.read, ← SourceTypes.translateArm f.write⟩

/-- All arms are validated before absorption, including their field and object
modes. A remaining non-invariant arm rejects the entire union. -/
def lower (cs : List (Contract ι)) : SourceTypes.Lowering σ (List (Ty ι)) := do
  (normalize cs).mapM fun c => do
    if invariant c then return [← CellClaims.reference (c.map fun f => (f.name, f.read))]
    if viewed c then
      let fields := (c.filter fun f => !readonly f).map fun f => (f.name, f.read)
      let views := (c.filter readonly).map fun f => (f.name, f.read)
      return [← CellClaims.viewReference fields views]
    throw "cell read and write types do not describe the same invariant"

def translate (atoms : List Json) : SourceTypes.Lowering σ (List (Ty ι)) := do
  lower (← atoms.mapM decode)

end

#print axioms normalize_exact
end Verification.Model.CellUnion
