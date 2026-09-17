import Verification.ExperimentState.HeapLinks
import Verification.ExperimentState.BranchRefinement

/-! Finite heap and immutable-value facts for expression postconditions. Facts
are execution-state assertions, not extra world contracts or source type labels. -/
namespace Verification.ExperimentState.HeapKnowledge
open ProgramTyping PositiveRules PositiveGraphs PositiveNormalization Tower HeapFacts

structure Knowledge where
  cells : Facts := []
  values : Facts := []
  links : HeapLinks.Links := []
  deriving DecidableEq, Repr

def ValueHolds (facts : Facts) (ρ : Env) : Prop :=
  ∀ f ∈ facts, ∃ a ∈ f.contents, ρ f.slot = a.value

def Holds (k : Knowledge) (ρ : Env) (h : Heap) : Prop :=
  HeapFacts.Holds k.cells ρ h ∧ ValueHolds k.values ρ ∧ HeapLinks.Holds k.links ρ h

theorem empty (ρ h) : Holds ⟨[],[],[]⟩ ρ h := ⟨holds_nil ρ h,by simp [ValueHolds],by simp [HeapLinks.Holds]⟩

/-- A fresh allocation preserves every assertion about existing cells and aliases. -/
theorem alloc_frame {k ρ h v} (hk : Holds k ρ h) : Holds k ρ (h ++ [v]) := by
  refine ⟨?_, hk.2.1, HeapLinks.alloc_frame hk.2.2⟩
  intro f hf
  obtain ⟨flds,c,l,u,he,hfd,hu,a,ha,hv⟩ := hk.1 f hf
  exact ⟨flds,c,l,u,he,hfd,HeapObservations.alloc_frame hu,a,ha,hv⟩

/-- The same across a whole object's worth of fresh locations. -/
theorem alloc_frames {k ρ h} (vs : List Val) (hk : Holds k ρ h) : Holds k ρ (h ++ vs) := by
  refine ⟨?_, hk.2.1, HeapLinks.alloc_frames vs hk.2.2⟩
  intro f hf
  obtain ⟨flds,c,l,u,he,hfd,hu,a,ha,hv⟩ := hk.1 f hf
  exact ⟨flds,c,l,u,he,hfd,HeapObservations.alloc_frames vs hu,a,ha,hv⟩

def check (a b : Knowledge) (m : PointClaims.Mapping) : Bool :=
  HeapFacts.check a.cells b.cells m && (HeapFacts.check a.values b.values m && HeapLinks.check a.links b.links m)

theorem check_sound {a b m ρ h} (hc : check a b m = true) (ha : Holds a ρ h) :
    Holds b (PointClaims.mapEnv m ρ) h := by
  simp only [check,Bool.and_eq_true] at hc
  refine ⟨HeapFacts.check_sound hc.1 ha.1,?_,HeapLinks.check_sound hc.2.2 ha.2.2⟩
  intro f hf
  obtain ⟨g,hg,hc⟩ := List.any_eq_true.mp (List.all_eq_true.mp hc.2.1 f hf)
  simp only [Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.contains_iff_mem] at hc
  obtain ⟨a,ham,he⟩ := ha.2.1 g hg
  exact ⟨a,hc.2 a ham,by simpa [PointClaims.mapEnv,hc.1] using he⟩

def shift (k : Knowledge) : Knowledge := ⟨HeapFacts.shift k.cells,HeapFacts.shift k.values,HeapLinks.pull k.links (fun i => [i+1])⟩

theorem shift_holds {k ρ h v} (hk : Holds k ρ h) : Holds (shift k) (push v ρ) h := by
  refine ⟨HeapFacts.shift_holds hk.1,?_,?_⟩
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    exact hk.2.1 g hg
  · apply HeapLinks.pull_holds (pre := fun i => [i+1]) hk.2.2
    intro i j hj
    have hj := List.mem_singleton.mp hj
    subst j
    rfl
/-- Effect-only continuations discard the result slot. Facts about it cannot
be transferred into the old environment. -/
def dropFacts (fs : Facts) : Facts :=
  (fs.filter fun f => 0 < f.slot).map fun f => {f with slot := f.slot - 1}

def dropResult (k : Knowledge) : Knowledge := ⟨dropFacts k.cells,dropFacts k.values,HeapLinks.pull k.links (fun i => if i = 0 then [] else [i-1])⟩

theorem dropResult_holds {k ρ h v} (hk : Holds k (push v ρ) h) :
    Holds (dropResult k) ρ h := by
  constructor
  · intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    have hg := List.mem_filter.mp hg
    have hp : 0 < g.slot := of_decide_eq_true hg.2
    have he : push v ρ g.slot = ρ (g.slot - 1) := by
      cases hs : g.slot with
      | zero => omega
      | succ i => rfl
    simpa [he] using hk.1 g hg.1
  · constructor
    · intro f hf
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      have hg := List.mem_filter.mp hg
      have hp : 0 < g.slot := of_decide_eq_true hg.2
      have he : push v ρ g.slot = ρ (g.slot - 1) := by
        cases hs : g.slot with
        | zero => omega
        | succ i => rfl
      simpa [he] using hk.2.1 g hg.1
    · apply HeapLinks.pull_holds (pre := fun i => if i = 0 then [] else [i-1]) hk.2.2
      intro i j hj
      split at hj
      · simp at hj
      · have hj := List.mem_singleton.mp hj
        subst j
        cases i with
        | zero => contradiction
        | succ i => rfl

/-- Project facts along an executable slot map. All runtime aliases selected by
that map are retained; facts about unselected slots are forgotten. -/
def projectFacts (facts : Facts) (m : PointClaims.Mapping) (count : Nat) : Facts :=
  (List.range count).flatMap fun i =>
    (facts.filter fun f => f.slot == PointClaims.slot m i).map fun f => { f with slot := i }

def project (k : Knowledge) (m : PointClaims.Mapping) (count : Nat) : Knowledge :=
  ⟨projectFacts k.cells m count,projectFacts k.values m count,
    HeapLinks.pull k.links (fun i => (List.range count).filter fun j => PointClaims.slot m j == i)⟩

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
  refine ⟨one _,one _,?_⟩
  apply List.all_eq_true.mpr
  intro g hg
  obtain ⟨f,hf,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨c,hc,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  apply List.any_eq_true.mpr
  refine ⟨f,hf,?_⟩
  have hc := List.mem_filter.mp hc
  have hv := List.mem_filter.mp hv
  simp only [beq_iff_eq] at hc hv
  simp [hc.2,hv.2]

/-- An observed Boolean outcome refines cells only through current read links.
The ordinary value fact is useful even when no cell link exists. -/
def observeBoolean (k : Knowledge) (slot : Nat) (q : Bool) : Knowledge :=
  let R := [if q then HeapFacts.Literal.tru else .fls]
  ⟨(k.links.filter (fun g => !g.alias && g.value == slot)).map
      (fun g => ⟨g.cell,R,g.field⟩) ++ k.cells,
    ⟨slot,R,valueField⟩ :: k.values,k.links⟩

theorem observeBoolean_holds {k slot q ρ h} (hk : Holds k ρ h)
    (hq : ρ slot = if q then .tru else .fls) : Holds (observeBoolean k slot q) ρ h := by
  refine ⟨?_,?_,hk.2.2⟩
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
      have hg := List.mem_filter.mp hg
      have hg2 := hg.2
      simp only [Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq] at hg2
      have hs := hg2.2
      obtain ⟨flds,c,l,hl,hfd,hh⟩ := (show ∃ flds c l, ρ g.cell = .objAt flds c ∧
          flds.lookup g.field = some l ∧ h[l]? = some (ρ g.value) from
        by simpa [hg2.1] using hk.2.2 g hg.1)
      refine ⟨flds,c,l,ρ g.value,hl,hfd,hh,(if q then .tru else .fls),by simp,?_⟩
      cases q <;> simpa [hs,HeapFacts.Literal.value] using hq
    · exact hk.1 f hf
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · refine ⟨(if q then .tru else .fls),by simp,?_⟩
      cases q <;> simpa [HeapFacts.Literal.value] using hq
    · exact hk.2.1 f hf

/-- A tag narrows a saved finite value, and its still-live read links transfer
that observation to the heap. No link means no assertion about a mutable cell. -/
def observeTag (k : Knowledge) (slot : Nat) (tag : Tag) (q : Bool) : Knowledge :=
  match k.values.find? (fun f => f.slot == slot) with
  | none => k
  | some f =>
    let R := f.contents.filter (fun a => tagHolds tag a.value == q)
    ⟨(k.links.filter (fun g => !g.alias && g.value == slot)).map
        (fun g => ⟨g.cell,R,g.field⟩) ++ k.cells,
      ⟨slot,R,valueField⟩ :: k.values,k.links⟩

theorem observeTag_holds {k slot tag q ρ h} (hk : Holds k ρ h)
    (hq : tagHolds tag (ρ slot) = q) : Holds (observeTag k slot tag q) ρ h := by
  unfold observeTag
  split
  · exact hk
  · rename_i f hf
    have hm := List.mem_of_find?_eq_some hf
    have hs : f.slot = slot := by simpa using List.find?_some hf
    obtain ⟨a,ha,hv⟩ := hk.2.1 f hm
    have hv : ρ slot = a.value := by simpa [hs] using hv
    have hmem : a ∈ f.contents.filter (fun a => tagHolds tag a.value == q) :=
      List.mem_filter.mpr ⟨ha,by simpa [hv] using hq⟩
    refine ⟨?_,?_,hk.2.2⟩
    · intro f' hf'
      rcases List.mem_append.mp hf' with hf' | hf'
      · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf'
        have hg := List.mem_filter.mp hg
        have hg2 := hg.2
        simp only [Bool.and_eq_true,Bool.not_eq_true',beq_iff_eq] at hg2
        obtain ⟨flds,c,l,hl,hfd,hh⟩ :=
          (show ∃ flds c l, ρ g.cell = .objAt flds c ∧
            flds.lookup g.field = some l ∧ h[l]? = some (ρ g.value) from
            by simpa [hg2.1] using hk.2.2 g hg.1)
        exact ⟨flds,c,l,ρ g.value,hl,hfd,hh,a,hmem,by simpa [hg2.2] using hv⟩
      · exact hk.1 f' hf'
    · intro f' hf'
      rcases List.mem_cons.mp hf' with rfl | hf'
      · exact ⟨a,hmem,hv⟩
      · exact hk.2.1 f' hf'

def observe (k : Knowledge) (slot : Nat) : BranchRefinement.Observation → Knowledge
  | .boolean q => observeBoolean k slot q
  | .tag t q => observeTag k slot t q

theorem observe_holds {k slot o ρ h} (hk : Holds k ρ h)
    (ho : o.holds (ρ slot)) : Holds (observe k slot o) ρ h := by
  cases o with
  | boolean q => exact observeBoolean_holds hk ho
  | tag t q => exact observeTag_holds hk ho

/-- Finite literal interpretation exists only for entirely primitive clauses. -/
def primitive : List (Clause (Ty ι)) → Option (List Literal)
  | [] => some []
  | .nul :: cs => (primitive cs).map ([.nul] ++ ·)
  | .undef :: cs => (primitive cs).map ([.undef] ++ ·)
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
        simp [sem,nulT,undefT,boolT,Literal.value,apply_ite,exists_or,or_assoc]
        all_goals split <;> simp_all [Literal.value]

theorem literals_sem {G : NormalGraph ι} {A R} (h : literals G A = some R) (n W v) :
    meaning G A n W v ↔ ∃ a ∈ R, v = a.value := by
  rw [expand_sem]
  exact primitive_sem h n W v

#print axioms observeTag_holds

end Verification.ExperimentState.HeapKnowledge
