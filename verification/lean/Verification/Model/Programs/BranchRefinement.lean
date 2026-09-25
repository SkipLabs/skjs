import Verification.Model.Programs.PointClaims

/-! Refinement of immutable environment slots under observed Boolean or tag outcomes.
Heap contents are not refined: the witness concerns the tested value,
not a retained observation about a mutable location. -/
namespace Verification.Model.BranchRefinement
open ProgramTyping PositiveGraphs PositiveRules PositiveNormalization PointClaims

def booleanMember [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) (q : Bool) : Bool :=
  (expand G A).any fun c => match c with
    | .bool => true
    | .boolLit b => b == q
    | _ => false

def onlyBoolean (G : NormalGraph ι) (A : Ty ι) : Bool :=
  G.plainTy A && (expand G A).all fun c => match c with
    | .bool | .boolLit _ => true
    | _ => false

theorem booleanMember_sound [DecidableEq ι] {G : NormalGraph ι} {A q}
    (h : booleanMember G A q = true) (n W) :
    meaning G A n W (if q then .tru else .fls) := by
  obtain ⟨c,hc,h⟩ := List.any_eq_true.mp h
  refine expand_sem_mpr ⟨c,expand_sub hc,?_⟩
  cases c <;> simp_all [clauseSem, semWithArgs, boolT]

theorem onlyBoolean_sound {G : NormalGraph ι} {A n W v}
    (h : onlyBoolean G A = true) (hv : meaning G A n W v) :
    v = .tru ∨ v = .fls := by
  simp only [onlyBoolean, Bool.and_eq_true] at h
  rw [expand_sem G A h.1] at hv
  obtain ⟨c,hc,hv⟩ := hv
  have h := List.all_eq_true.mp h.2 c hc
  cases c <;> simp_all [clauseSem, semWithArgs, boolT]

/-- Drop only labels whose every clause contradicts the observed tag. A mixed
label is retained intact: this does not assume that labels have uniform shapes.
A parameter or scheme row has no clauses to contradict it, and is retained. -/
def tagSlice (G : NormalGraph ι) (A : Ty ι) (tag : Tag) (q : Bool) : Ty ι :=
  A.filter fun a => !(G.plain a && (expand G [a]).all fun c => (tagClause tag c) == some (!q))

theorem tagSlice_sound {G : NormalGraph ι} {A tag q n W v}
    (hv : meaning G A n W v) (hq : tagHolds tag v = q) :
    meaning G (tagSlice G A tag q) n W v := by
  obtain ⟨a, ha, hv⟩ := hv
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hv⟩
  cases h : (G.plain a && (expand G [a]).all fun c => (tagClause tag c) == some (!q)) with
  | false => rfl
  | true =>
    simp only [Bool.and_eq_true] at h
    have hop : Answers G [a] tag (!q) := by
      refine ⟨by simp [NormalGraph.plainTy, h.1], fun c hc => ?_⟩
      exact beq_iff_eq.mp (List.all_eq_true.mp h.2 c hc)
    have he := answers_sound hop (show meaning G [a] n W v from ⟨a, by simp, hv⟩)
    cases q <;> simp_all

/-- A small, explicit vocabulary of observations established by execution. -/
inductive Observation where
  | boolean (value : Bool)
  | tag (test : Tag) (answer : Bool)

def Observation.holds : Observation → Tm → Prop
  | .boolean q, v => v = (if q then .tru else .fls)
  | .tag t q, v => tagHolds t v = q

/-- The durable refinement obligation. B is supplied; no canonical filtered
representation, join, or inferred invariant is required by this contract. -/
def ObservedSub (G : NormalGraph ι) (A B : Ty ι) (o : Observation) : Prop :=
  ∀ n W v, meaning G A n W v → o.holds v → meaning G B n W v

def isSubset : PositiveCertificates.Proof ι → Bool
  | .subset => true
  | _ => false

/-- Whether one clause of `B` holds every value a passed tag test admits:
`string` after `typeof x === "string"`, whatever `x` was before, `unknown`
included. Only the tests that name one primitive family do. -/
def tagMember (G : NormalGraph ι) (B : Ty ι) : Tag → Bool → Bool
  | .isStr, true => (expand G B).any fun c => match c with | .str => true | _ => false
  | .isNum, true => (expand G B).any fun c => match c with | .num => true | _ => false
  | .isBigint, true => (expand G B).any fun c => match c with | .bigint => true | _ => false
  | .isSymbol, true => (expand G B).any fun c => match c with | .symbol => true | _ => false
  | .isUndef, true => (expand G B).any fun c => match c with | .undef => true | _ => false
  | .isNul, true => (expand G B).any fun c => match c with | .nul => true | _ => false
  | .isBool, true => (expand G B).any fun c => match c with | .bool => true | _ => false
  | _, _ => false

theorem tagMember_sound {G : NormalGraph ι} {B : Ty ι} {t : Tag} {q : Bool}
    (hm : tagMember G B t q = true) {n W v} (hv : isVal v = true) (ht : tagHolds t v = q) :
    meaning G B n W v := by
  cases t <;> cases q <;> simp only [tagMember, Bool.false_eq_true] at hm
  all_goals
    obtain ⟨c, hc, hk⟩ := List.any_eq_true.mp hm
    cases c <;> simp at hk
    cases v <;> simp [tagHolds, isVal] at ht hv <;>
      exact expand_sem_mpr ⟨_, expand_sub hc, by
        simp [semWithArgs, nulT, undefT, boolT, numT, strT, bigintT, symbolT]⟩

/-- Sufficient implementations of ObservedSub. Whole-label filtering is only
an algorithm for the tag case, not the meaning of refinement. -/
def checkObservedSub [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι)
    (o : Observation) (p : PositiveCertificates.Proof ι) : Bool :=
  match o with
  | .boolean q => isSubset p && booleanMember G B q
  | .tag t q => PositiveCertificates.check G (tagSlice G A t q) B p || (isSubset p && tagMember G B t q)

theorem checkObservedSub_sound [DecidableEq ι] {G : NormalGraph ι} {A B o p}
    (hc : checkObservedSub G A B o p = true) : ObservedSub G A B o := by
  intro n W v hv ho
  cases o with
  | boolean q =>
    simp only [checkObservedSub, Bool.and_eq_true] at hc
    have hb := hc.2
    change v = (if q then .tru else .fls) at ho
    rw [ho]
    exact booleanMember_sound hb n W
  | tag t q =>
    simp only [checkObservedSub, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with hc | ⟨_, hm⟩
    · exact (PositiveCertificates.check_sound hc).sound n W v (tagSlice_sound hv ho)
    · exact tagMember_sound hm (meaning_value hv).1 ho

/-- One mapped-edge checker for all supported observations. Other slots use
ordinary subtype evidence. The tested slot must exist, even if forgotten. -/
def checkObserved [DecidableEq ι] (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (tested : Nat) (o : Observation) (mapping : Mapping) (ps : EdgeEvidence ι) : Bool :=
  Γ[tested]?.isSome &&
  (match mapping with | none => true | some slots => slots.length == Δ.length) &&
  ps.length == Δ.length && (List.range Δ.length).all (fun j =>
    match Γ[slot mapping j]?, Δ[j]?, ps[j]? with
    | some A, some B, some p =>
      if slot mapping j == tested then checkObservedSub G A B o p
      else PositiveCertificates.check G A B p
    | _, _, _ => false)

def ObservedCovers (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (tested : Nat) (o : Observation) (mapping : Mapping) : Prop :=
  ∀ j B, Δ[j]? = some B → ∃ A, Γ[slot mapping j]? = some A ∧
    (if slot mapping j = tested then ObservedSub G A B o else Sub G A B)

theorem checkObserved_sound [DecidableEq ι] {G : NormalGraph ι} {Γ Δ i o mapping ps}
    (h : checkObserved G Γ Δ i o mapping ps = true) : ObservedCovers G Γ Δ i o mapping := by
  simp only [checkObserved, Bool.and_eq_true, List.all_eq_true] at h
  intro j B hj
  have hc := h.2 j (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hj).1)
  rw [hj] at hc
  cases ha : Γ[slot mapping j]? with
  | none => simp [ha] at hc
  | some A =>
    cases hp : ps[j]? with
    | none => simp [ha,hp] at hc
    | some p =>
      refine ⟨A,rfl,?_⟩
      simp only [ha,hp] at hc
      by_cases he : slot mapping j = i
      · simp only [beq_iff_eq,he,↓reduceIte] at hc
        simp only [he,↓reduceIte]
        exact checkObservedSub_sound hc
      · simp only [beq_iff_eq,he,↓reduceIte] at hc
        simp only [he,↓reduceIte]
        exact PositiveCertificates.check_sound hc

theorem ObservedCovers.env {G : NormalGraph ι} {Γ Δ i o mapping ρ n W}
    (hc : ObservedCovers G Γ Δ i o mapping) (he : EnvOk G Γ ρ n W)
    (ho : o.holds (ρ i)) : EnvOk G Δ (mapEnv mapping ρ) n W := by
  refine ⟨fun j => he.1 (slot mapping j), ?_⟩
  intro j B hj
  obtain ⟨A,ha,h⟩ := hc j B hj
  by_cases hij : slot mapping j = i
  · simp only [hij,↓reduceIte] at h
    change meaning G B n W (ρ (slot mapping j))
    rw [hij]
    exact h n W _ (by simpa [hij] using he.2 _ A ha) ho
  · simp only [hij,↓reduceIte] at h
    exact h.sound n W _ (he.2 _ A ha)

#print axioms checkObservedSub_sound
#print axioms checkObserved_sound
#print axioms ObservedCovers.env
end Verification.Model.BranchRefinement
