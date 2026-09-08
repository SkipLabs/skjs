import Verification.ExperimentState.HeapFacts

/-! Finite heap and immutable-value facts for expression postconditions. Facts
are execution-state assertions, not extra world contracts or source type labels. -/
namespace Verification.ExperimentState.HeapKnowledge
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower HeapFacts

structure Knowledge where
  cells : Facts := []
  values : Facts := []
  deriving DecidableEq, Repr

def ValueHolds (facts : Facts) (ρ : Env) : Prop :=
  ∀ f ∈ facts, ∃ a ∈ f.contents, ρ f.slot = a.value

def Holds (k : Knowledge) (ρ : Env) (h : Heap) : Prop :=
  HeapFacts.Holds k.cells ρ h ∧ ValueHolds k.values ρ

theorem empty (ρ h) : Holds ⟨[],[]⟩ ρ h := ⟨holds_nil ρ h,by simp [ValueHolds]⟩

def check (a b : Knowledge) (m : PointClaims.Mapping) : Bool :=
  HeapFacts.check a.cells b.cells m && HeapFacts.check a.values b.values m

theorem check_sound {a b m ρ h} (hc : check a b m = true) (ha : Holds a ρ h) :
    Holds b (PointClaims.mapEnv m ρ) h := by
  simp only [check,Bool.and_eq_true] at hc
  refine ⟨HeapFacts.check_sound hc.1 ha.1,?_⟩
  intro f hf
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc.2 f hf)
  simp only [Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.contains_iff_mem] at hc
  obtain ⟨a,ham,he⟩ := ha.2 g hg
  exact ⟨a,hc.2 a ham,by simpa [PointClaims.mapEnv,hc.1] using he⟩

def shift (k : Knowledge) : Knowledge := ⟨HeapFacts.shift k.cells,HeapFacts.shift k.values⟩

theorem shift_holds {k ρ h v} (hk : Holds k ρ h) : Holds (shift k) (push v ρ) h := by
  refine ⟨HeapFacts.shift_holds hk.1,?_⟩
  intro f hf
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  exact hk.2 g hg

/-- Project facts along an executable slot map. All runtime aliases selected by
that map are retained; facts about unselected slots are forgotten. -/
def projectFacts (facts : Facts) (m : PointClaims.Mapping) (count : Nat) : Facts :=
  (List.range count).flatMap fun i =>
    (facts.filter fun f => f.slot == PointClaims.slot m i).map fun f => { f with slot := i }

def project (k : Knowledge) (m : PointClaims.Mapping) (count : Nat) : Knowledge :=
  ⟨projectFacts k.cells m count,projectFacts k.values m count⟩

theorem project_checked (k : Knowledge) (m count) : check k (project k m count) m = true := by
  have one (fs : Facts) : HeapFacts.check fs (projectFacts fs m count) m = true := by
    apply List.all_eq_true.mpr
    intro f hf
    obtain ⟨i,_,hf⟩ := List.mem_flatMap.mp hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    have hg := List.mem_filter.mp hg
    apply List.any_eq_true.mpr
    exact ⟨g,hg.1,by simp [hg.2]⟩
  simp only [check,Bool.and_eq_true]
  exact ⟨one _,one _⟩

/-- Finite literal interpretation exists only for entirely primitive clauses. -/
def primitive : List (Clause (Ty ι)) → Option (List Literal)
  | [] => some []
  | .nul :: cs => (primitive cs).map ([.nul] ++ ·)
  | .bool :: cs => (primitive cs).map ([.tru,.fls] ++ ·)
  | .boolLit b :: cs => (primitive cs).map ([if b then .tru else .fls] ++ ·)
  | _ => none

def literals (G : NormalGraph ι) (A : Ty ι) := primitive (expand G A)

theorem primitive_sem {G : NormalGraph ι} {cs R} (hc : primitive cs = some R) (n W v) :
    semList (meaning G) cs n W v ↔ ∃ a ∈ R, v = a.value := by
  induction cs generalizing R with
  | nil => simp [primitive] at hc; subst R; simp [semList,setSem]
  | cons c cs ih =>
    cases c <;> simp only [primitive] at hc
    all_goals try contradiction
    all_goals
      cases hr : primitive cs with
      | none => simp [hr] at hc
      | some rs =>
        simp only [hr,Option.map_some,Option.some.injEq] at hc
        subst R
        have hi := ih hr
        simp only [semList,setSem,List.mem_cons,exists_eq_or_imp] at hi ⊢
        rw [hi]
        simp [sem,nulT,boolT,Literal.value,apply_ite,exists_or,or_assoc]
        all_goals split <;> simp_all [Literal.value]

theorem literals_sem {G : NormalGraph ι} {A R} (h : literals G A = some R) (n W v) :
    meaning G A n W v ↔ ∃ a ∈ R, v = a.value := by
  rw [expand_sem]
  exact primitive_sem h n W v

end Verification.ExperimentState.HeapKnowledge
