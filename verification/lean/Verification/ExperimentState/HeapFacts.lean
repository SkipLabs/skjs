import Verification.ExperimentState.PointClaims
import Verification.ExperimentState.HeapObservations

/-! Finite current-content assertions. They constrain the current heap, never
change a world's contract, and carry no ownership or disjointness promise.
Edge entailment selects facts by runtime-environment slots and weakens their
literal sets. The representation has no execution indices in its syntax. -/
namespace Verification.ExperimentState.HeapFacts
open ProgramTyping PositiveRules PositiveGraphs HeapObservations

inductive Literal where
  | nul | undef | tru | fls
  deriving DecidableEq, Repr

def Literal.value : Literal → Tm
  | .nul => .nul | .undef => .undef | .tru => .tru | .fls => .fls

def Literal.ofTerm : Tm → Option Literal
  | .nul => some .nul | .undef => some .undef | .tru => some .tru | .fls => some .fls | _ => none

/-- A current-content assertion: at the object a runtime slot holds, the named
field currently contains one of these literals. A value fact reuses the same
shape and ignores the field, which is why it defaults to the cell's. -/
structure Fact where
  slot : Nat
  contents : List Literal
  field : String := valueField
  deriving DecidableEq, Repr

abbrev Facts := List Fact

def Holds (facts : Facts) (ρ : Env) (h : Heap) : Prop :=
  ∀ f ∈ facts, ∃ flds c l v, ρ f.slot = .objAt flds c ∧ flds.lookup f.field = some l ∧
    h[l]? = some v ∧ ∃ a ∈ f.contents, v = a.value

theorem holds_nil (ρ h) : Holds [] ρ h := by simp [Holds]

/-- All target facts must have an incoming justification. Repeated slot maps
retain aliases; different slot numbers do not imply different locations. -/
def check (source target : Facts) (mapping : PointClaims.Mapping) : Bool :=
  target.all fun f => source.any fun g =>
    g.slot == PointClaims.slot mapping f.slot && g.field == f.field &&
      g.contents.all f.contents.contains

theorem check_sound {source target mapping ρ h}
    (hc : check source target mapping = true) (hs : Holds source ρ h) :
    Holds target (PointClaims.mapEnv mapping ρ) h := by
  intro f hmem
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc f hmem)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at hc
  obtain ⟨flds,c,l,v,hl,hfd,hv,a,ha,he⟩ := hs g hg
  refine ⟨flds,c,l,v,?_,?_,hv,a,hc.2 a ha,he⟩
  · simpa [PointClaims.mapEnv,hc.1.1] using hl
  · rw [← hc.1.2]; exact hfd

/-- The value added by a bind shifts every old environment slot. -/
def shift (facts : Facts) : Facts := facts.map fun f => { f with slot := f.slot+1 }

theorem shift_holds {facts ρ h v} (hf : Holds facts ρ h) :
    Holds (shift facts) (push v ρ) h := by
  intro f hm
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
  exact hf g hg

/-- A read preserves all assertions because it leaves the heap unchanged. -/
theorem read {facts ρ h i fld R n W}
    (hf : Holds facts ρ h) (hm : Fact.mk i R fld ∈ facts)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (fun _ _ v => ∃ a ∈ R, v = a.value)
      (fun h' _ => Holds facts ρ h') n W h (.readAt fld (ρ i)) := by
  obtain ⟨flds,c,l,v,hl,hfd,hv,a,ha,rfl⟩ := hf _ hm
  rw [hl]
  apply consequence _ _ (read_observed hw hh hfd (by cases a <;> rfl) hv)
  · intro _ _ u hu; exact ⟨a,ha,hu⟩
  · intro h' _ hp; rw [hp.1]; exact hf

/-- A write invalidates every old observation, including facts about aliases.
Only the fact about the written location is established. -/
theorem write {A : Fam} (ha : Adm A) {ρ h i a n W}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hr : refT A n W (ρ i))
    (ht : A n W (Literal.value a)) :
    SafePost nulT (fun h' _ => Holds [⟨i,[a],valueField⟩] ρ h') n W h
      (.write (ρ i) a.value) := by
  obtain ⟨flds,l,c,he,hfd,hl,hc⟩ := refT_iff.mp hr
  have hrec : recT [(valueField, A)] n W (.objAt flds .absent) :=
    recT_single.mpr ⟨flds,l,c,rfl,hfd,hl,hc⟩
  rw [he]
  apply weaken _ (write_observed ha hw hh hrec hfd (by cases a <;> rfl) ht)
  intro h' _ hp f hmem
  simp only [List.mem_singleton] at hmem
  subst f
  refine ⟨flds,.absent,l,a.value,he,hfd,?_,a,by simp,rfl⟩
  rw [hp.1]
  apply write_new
  rw [hh.1]
  exact (List.getElem?_eq_some_iff.mp hl).1

/-- Allocation preserves existing observations and adds the new cell at the
result slot. This relies on actual heap extension, not on non-aliasing names. -/
theorem alloc {A : Fam} (ha : Adm A) {facts ρ h a n W}
    (hf : Holds facts ρ h) (hw : WorldAdm W) (hh : HeapOk n W h)
    (ht : A n W (Literal.value a)) :
    SafePost (refT A)
      (fun h' v => Holds (⟨0,[a],valueField⟩ :: shift facts) (push v ρ) h') n W h
      (.alloc a.value) := by
  apply weaken _ (alloc_observed ha hw hh (by cases a <;> rfl) ht)
  intro h' v hp f hm
  rw [hp.1,hp.2]
  rcases List.mem_cons.mp hm with rfl | hm
  · exact ⟨[(valueField,h.length)],.absent,h.length,a.value,rfl,lookup_value _,
      alloc_new h a.value,a,by simp,rfl⟩
  · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
    obtain ⟨flds,c,l,u,hl,hfd,hu,b,hb,he⟩ := hf g hg
    exact ⟨flds,c,l,u,hl,hfd,alloc_frame hu,b,hb,he⟩

#print axioms check_sound
#print axioms read
#print axioms write
#print axioms alloc
end Verification.ExperimentState.HeapFacts
