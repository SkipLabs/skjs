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

structure Fact where
  slot : Nat
  contents : List Literal
  deriving DecidableEq, Repr

abbrev Facts := List Fact

def Holds (facts : Facts) (ρ : Env) (h : Heap) : Prop :=
  ∀ f ∈ facts, ∃ l v, ρ f.slot = .loc l ∧ h[l]? = some v ∧
    ∃ a ∈ f.contents, v = a.value

theorem holds_nil (ρ h) : Holds [] ρ h := by simp [Holds]

/-- All target facts must have an incoming justification. Repeated slot maps
retain aliases; different slot numbers do not imply different locations. -/
def check (source target : Facts) (mapping : PointClaims.Mapping) : Bool :=
  target.all fun f => source.any fun g =>
    g.slot == PointClaims.slot mapping f.slot && g.contents.all f.contents.contains

theorem check_sound {source target mapping ρ h}
    (hc : check source target mapping = true) (hs : Holds source ρ h) :
    Holds target (PointClaims.mapEnv mapping ρ) h := by
  intro f hf
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc f hf)
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at hc
  obtain ⟨l,v,hl,hv,a,ha,he⟩ := hs g hg
  exact ⟨l,v,by simpa [PointClaims.mapEnv,hc.1] using hl,hv,a,hc.2 a ha,he⟩

/-- The value added by a bind shifts every old environment slot. -/
def shift (facts : Facts) : Facts := facts.map fun f => { f with slot := f.slot+1 }

theorem shift_holds {facts ρ h v} (hf : Holds facts ρ h) :
    Holds (shift facts) (push v ρ) h := by
  intro f hm
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
  exact hf g hg

/-- A read preserves all assertions because it leaves the heap unchanged. -/
theorem read {facts ρ h i R n W}
    (hf : Holds facts ρ h) (hm : Fact.mk i R ∈ facts)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (fun _ _ v => ∃ a ∈ R, v = a.value)
      (fun h' _ => Holds facts ρ h') n W h (.read (ρ i)) := by
  obtain ⟨l,v,hl,hv,a,ha,rfl⟩ := hf _ hm
  rw [hl]
  apply consequence _ _ (read_observed hw hh (by cases a <;> rfl) hv)
  · intro _ _ u hu; exact ⟨a,ha,hu⟩
  · intro h' _ hp; rw [hp.1]; exact hf

/-- A write invalidates every old observation, including facts about aliases.
Only the fact about the written location is established. -/
theorem write {A : Fam} (ha : Adm A) {ρ h i a n W}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hr : refT A n W (ρ i))
    (ht : A n W (Literal.value a)) :
    SafePost nulT (fun h' _ => Holds [⟨i,[a]⟩] ρ h') n W h
      (.write (ρ i) a.value) := by
  obtain ⟨l,c,he,hl,hc⟩ := hr
  have hr : refT A n W (.loc l) := ⟨l,c,rfl,hl,hc⟩
  rw [he]
  apply weaken _ (write_observed ha hw hh hr (by cases a <;> rfl) ht)
  intro h' _ hp f hf
  simp only [List.mem_singleton] at hf
  subst f
  refine ⟨l,a.value,he,?_,a,by simp,rfl⟩
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
      (fun h' v => Holds (⟨0,[a]⟩ :: shift facts) (push v ρ) h') n W h (.alloc a.value) := by
  apply weaken _ (alloc_observed ha hw hh (by cases a <;> rfl) ht)
  intro h' v hp f hm
  rw [hp.1,hp.2]
  rcases List.mem_cons.mp hm with rfl | hm
  · exact ⟨h.length,a.value,rfl,alloc_new h a.value,a,by simp,rfl⟩
  · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
    obtain ⟨l,u,hl,hu,b,hb,he⟩ := hf g hg
    exact ⟨l,u,hl,alloc_frame hu,b,hb,he⟩

#print axioms check_sound
#print axioms read
#print axioms write
#print axioms alloc
end Verification.ExperimentState.HeapFacts
