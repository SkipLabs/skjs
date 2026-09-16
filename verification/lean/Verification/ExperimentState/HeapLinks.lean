import Verification.ExperimentState.HeapFacts

/-! A read-to-cell relation is a current-heap fact, not a timeless alias of an
immutable value. It survives pure slot transfers and allocation, but is discarded
on writes and calls. This is the witness needed to refine a cell from a guard. -/
namespace Verification.ExperimentState.HeapLinks
open ProgramTyping

/-- A read link names the field it was read through; an alias link relates two
slots holding the same value and ignores it. -/
structure Link where
  cell : Nat
  value : Nat
  alias : Bool := false
  field : String := valueField
  deriving DecidableEq, Repr

abbrev Links := List Link

def Holds (ls : Links) (ρ : Env) (h : Heap) : Prop :=
  ∀ g ∈ ls, if g.alias then ρ g.cell = ρ g.value
    else ∃ flds c l, ρ g.cell = .objAt flds c ∧ flds.lookup g.field = some l ∧
      h[l]? = some (ρ g.value)

/-- Pull back through a finite selection of aliases for each old slot. -/
def pull (ls : Links) (pre : Nat → List Nat) : Links :=
  ls.flatMap fun g => (pre g.cell).flatMap fun c => (pre g.value).map fun v =>
    ⟨c,v,g.alias,g.field⟩

theorem pull_holds {ls pre ρ τ h} (hh : Holds ls ρ h)
    (he : ∀ i j, j ∈ pre i → τ j = ρ i) : Holds (pull ls pre) τ h := by
  intro g hg
  obtain ⟨a,ha,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨c,hc,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  simpa [he _ _ hc,he _ _ hv] using hh a ha

def check (a b : Links) (m : PointClaims.Mapping) : Bool :=
  b.all fun g => a.any fun f =>
    f.cell == PointClaims.slot m g.cell &&
      (f.value == PointClaims.slot m g.value && (f.field == g.field && f.alias == g.alias))

theorem check_sound {a b m ρ h} (hc : check a b m = true) (hh : Holds a ρ h) :
    Holds b (PointClaims.mapEnv m ρ) h := by
  intro g hg
  obtain ⟨f,hf,hfg⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc g hg)
  simp only [Bool.and_eq_true,beq_iff_eq] at hfg
  simpa [PointClaims.mapEnv,← hfg.1,← hfg.2.1,← hfg.2.2.1,← hfg.2.2.2] using hh f hf

theorem alloc_frame {ls ρ h v} (hh : Holds ls ρ h) : Holds ls ρ (h ++ [v]) := by
  intro g hg
  have hh := hh g hg
  cases ha : g.alias <;> simp only [ha,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
  · obtain ⟨flds,c,l,hl,hfd,hv⟩ := hh
    exact ⟨flds,c,l,hl,hfd,HeapObservations.alloc_frame hv⟩
  · exact hh

theorem alloc_frames {ls ρ h} (vs : List Val) (hh : Holds ls ρ h) : Holds ls ρ (h ++ vs) := by
  intro g hg
  have hh := hh g hg
  cases ha : g.alias <;> simp only [ha,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
  · obtain ⟨flds,c,l,hl,hfd,hv⟩ := hh
    exact ⟨flds,c,l,hl,hfd,HeapObservations.alloc_frames vs hv⟩
  · exact hh

/-- Value equalities survive arbitrary heap changes; read links do not. -/
def stable (ls : Links) := ls.filter (·.alias)

theorem stable_holds {ls ρ h h'} (hh : Holds ls ρ h) : Holds (stable ls) ρ h' := by
  intro g hg
  have hg := List.mem_filter.mp hg
  simpa [hg.2] using hh g hg.1

/-- Only witnessed equalities extend a write to another slot. -/
def aliases (ls : Links) (i : Nat) : List Nat := i ::
  ls.filterMap (fun g => if g.alias then
    if g.cell == i then some g.value else if g.value == i then some g.cell else none
    else none)

theorem aliases_eq {ls i j ρ h} (hh : Holds ls ρ h) (hj : j ∈ aliases ls i) : ρ j = ρ i := by
  rcases List.mem_cons.mp hj with rfl | hj
  · rfl
  · obtain ⟨g,hg,hj⟩ := List.mem_filterMap.mp hj
    split at hj
    · rename_i ha
      have he : ρ g.cell = ρ g.value := by simpa [ha] using hh g hg
      split at hj
      · rename_i hc
        simp only [beq_iff_eq] at hc
        cases hj
        simpa [hc] using he.symm
      · split at hj
        · rename_i hv
          simp only [beq_iff_eq] at hv
          cases hj
          simpa [hv] using he
        · contradiction
    · contradiction

end Verification.ExperimentState.HeapLinks
