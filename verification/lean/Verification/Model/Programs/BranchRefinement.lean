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
    (hv : meaning G A n W v) (hq : tagHolds tag v = q ∨ protoFree tag v = false) :
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
    have he := answers_weak hop (show meaning G [a] n W v from ⟨a, by simp, hv⟩) hq
    cases q <;> simp at he

/-! ### Refinement by an observed field

A tag observed on a value read from a field of an object excludes each label
whose record contract for that field answers the other way: the field's
location holds the read value, and its world contract, fixed at allocation,
admits only values of the field's type. The exclusion concerns the object's
label, which is timeless; what the field holds later is not claimed. -/

/-- Whether a record clause fixes the field `f` at a type answering `tag`
with `q`: an invariant field or a readonly view. -/
def fieldAnswers (G : NormalGraph ι) (c : Clause (Ty ι)) (f : PropKey) (tag : Tag) (q : Bool) : Bool :=
  match c with
  | .refs a _ vs _ _ _ => (a ++ vs).any fun p =>
      decide (p.1 = f) && G.plainTy p.2 && (expand G p.2).all fun c => tagClause tag c == some q
  | _ => false

/-- The labels of `A` an object may still have once the value of its field
`f` answered `tag` with `q`. A label is dropped only where every clause of it
fixes `f` at a type answering the other way. -/
def fieldSlice (G : NormalGraph ι) (A : Ty ι) (f : PropKey) (tag : Tag) (q : Bool) : Ty ι :=
  A.filter fun a => !(G.plain a && (expand G [a]).all fun c => fieldAnswers G c f tag (!q))

/-- The value in a record's field location is of the field's type, one level
down: its contract says so, and a heap meeting the world holds it. -/
theorem field_value {G : NormalGraph ι} {c : Clause (Ty ι)} {f : PropKey} {K : Ty ι}
    {n W h v flds code l u}
    (hK : match c with
      | .refs a _ vs _ _ _ => (f, K) ∈ a ++ vs
      | _ => False)
    (hv : clauseSem G c (n+1) W v) (hh : HeapOk (n+1) W h)
    (hl : v = .objAt flds code) (hf : flds.lookup f = some l) (hu : h[l]? = some u) :
    meaning G K n (trunc n (Nat.le_succ n) W) u := by
  cases c with
  | refs a bs vs os ms ks =>
    simp only at hK
    have take : ∀ (c' : Ctr (n+1)), lookup W l = some c' →
        (∀ (W' : WorldT n) (w : Val), c' n (Nat.lt_succ_self n) W' w → meaning G K n W' w) →
        meaning G K n (trunc n (Nat.le_succ n) W) u := by
      intro c' hc' himp
      obtain ⟨u', hu', hall⟩ := hh.2 l c' hc'
      rw [hu] at hu'
      cases hu'
      exact himp _ _ (hall n (Nat.lt_succ_self n))
    rcases List.mem_append.mp hK with hK | hK
    · obtain ⟨flds', hv', hall⟩ := hv.1.1
      rw [hl] at hv'
      cases hv'
      obtain ⟨l', c', hl', hc', hag⟩ := hall f (meaning G K) (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩)
      rw [hf] at hl'
      cases hl'
      exact take c' hc' fun W' w hw => (hag n (Nat.lt_succ_self n) W' w).mp hw
    · obtain ⟨flds', l', c', hv', hl', hc', himp⟩ :=
        hv.2.1 f (meaning G K) (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩)
      rw [hl] at hv'
      cases hv'
      rw [hf] at hl'
      cases hl'
      exact take c' hc' fun W' w hw => himp n (Nat.lt_succ_self n) W' w hw
  | _ => exact hK.elim

theorem fieldSlice_sound {G : NormalGraph ι} {A : Ty ι} {f tag q n W h v flds code l u}
    (hv : meaning G A (n+1) W v) (hh : HeapOk (n+1) W h)
    (hl : v = .objAt flds code) (hf : flds.lookup f = some l) (hu : h[l]? = some u)
    (hq : tagHolds tag u = q ∨ protoFree tag u = false) : meaning G (fieldSlice G A f tag q) (n+1) W v := by
  obtain ⟨a, ha, hva⟩ := hv
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hva⟩
  cases hd : (G.plain a && (expand G [a]).all fun c => fieldAnswers G c f tag (!q)) with
  | false => rfl
  | true =>
    exfalso
    simp only [Bool.and_eq_true, List.all_eq_true] at hd
    have hm : meaning G [a] (n+1) W v := ⟨a, by simp, hva⟩
    rw [expand_sem G [a] (by simp [NormalGraph.plainTy, hd.1])] at hm
    obtain ⟨c, hc, hcv⟩ := hm
    have hans := hd.2 c hc
    cases c with
    | refs a' bs vs os ms ks =>
      simp only [fieldAnswers, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hans
      obtain ⟨⟨g, K⟩, hp, ⟨rfl, hplain⟩, hall⟩ := hans
      have hK : Answers G K tag (!q) :=
        ⟨hplain, fun c hc => beq_iff_eq.mp (List.all_eq_true.mp hall c hc)⟩
      have hu' := field_value (c := .refs a' bs vs os ms ks) (K := K) hp hcv hh hl hf hu
      have := answers_weak hK hu' hq
      cases q <;> simp at this
    | _ => simp [fieldAnswers] at hans

/-- A small, explicit vocabulary of observations established by execution. -/
inductive Observation where
  | boolean (value : Bool)
  | tag (test : Tag) (answer : Bool)

def Observation.holds : Observation → Tm → Prop
  | .boolean q, v => v = (if q then .tru else .fls)
  -- `key in o` on an object reading a prototype may answer either way.
  | .tag t q, v => tagHolds t v = q ∨ protoFree t v = false

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
    · exact tagMember_sound hm (meaning_value hv).1 (ho.resolve_right (by
        cases t <;> simp [tagMember] at hm <;> simp [protoFree]))

/-- The field refinements a tag observation admits for other slots: each
object a current read link says the tested value was read from, and the
field it was read through. -/
def fieldRefinements (o : Observation) (fields : List (Nat × PropKey)) (A B : Ty ι) (j : Nat)
    (G : NormalGraph ι) (p : PositiveCertificates.Proof ι) [DecidableEq ι] : Bool :=
  match o with
  | .tag t q => fields.any fun (k, f) => k == j && PositiveCertificates.check G (fieldSlice G A f t q) B p
  | .boolean _ => false

/-- An observation no value of the tested type makes: a tag answer every
label contradicts, or a Boolean the type does not hold. The edge is then
never taken, and constrains nothing. -/
def impossible [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) : Observation → Bool
  | .tag t q => (tagSlice G A t q).isEmpty
  | .boolean q => G.plainTy A && (expand G A).all fun c =>
      c == .boolLit (!q) || tagClause .isBool c == some false

theorem impossible_sound [DecidableEq ι] {G : NormalGraph ι} {A o n W v}
    (h : impossible G A o = true) (hv : meaning G A n W v) (ho : o.holds v) : False := by
  cases o with
  | tag t q =>
    simp only [impossible, List.isEmpty_iff] at h
    obtain ⟨a, ha, _⟩ := tagSlice_sound hv ho
    rw [h] at ha
    cases ha
  | boolean q =>
    simp only [impossible, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨c, hc, hcv⟩ := (expand_sem G A h.1 n W v).mp hv
    change v = (if q then .tru else .fls) at ho
    subst ho
    rcases h.2 c hc with rfl | hb
    · cases q <;> simp [semWithArgs] at hcv
    · have := tagClause_sound hb hcv
      cases q <;> simp [tagHolds] at this

/-- One mapped-edge checker for all supported observations. Other slots use
ordinary subtype evidence, or, for an object the tested value was read from
(`fields`), subtype evidence from its field slice. The tested slot must
exist, even if forgotten. -/
def checkObserved [DecidableEq ι] (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (tested : Nat) (o : Observation) (mapping : Mapping) (ps : EdgeEvidence ι)
    (fields : List (Nat × PropKey) := []) : Bool :=
  Γ[tested]?.isSome &&
  ((Γ[tested]?).any (impossible G · o) ||
  (match mapping with | none => true | some slots => slots.length == Δ.length) &&
  ps.length == Δ.length && (List.range Δ.length).all (fun j =>
    match Γ[slot mapping j]?, Δ[j]?, ps[j]? with
    | some A, some B, some p =>
      if slot mapping j == tested then checkObservedSub G A B o p
      else PositiveCertificates.check G A B p || fieldRefinements o fields A B (slot mapping j) G p
    | _, _, _ => false))

def ObservedCovers (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (tested : Nat) (o : Observation) (mapping : Mapping) (fields : List (Nat × PropKey) := []) : Prop :=
  (∃ A, Γ[tested]? = some A ∧ ∀ n W v, meaning G A n W v → o.holds v → False) ∨
  ∀ j B, Δ[j]? = some B → ∃ A, Γ[slot mapping j]? = some A ∧
    (if slot mapping j = tested then ObservedSub G A B o
     else Sub G A B ∨ ∃ t q f, o = .tag t q ∧ (slot mapping j, f) ∈ fields ∧
       Sub G (fieldSlice G A f t q) B)

theorem checkObserved_sound [DecidableEq ι] {G : NormalGraph ι} {Γ Δ i o mapping ps fields}
    (h : checkObserved G Γ Δ i o mapping ps fields = true) : ObservedCovers G Γ Δ i o mapping fields := by
  simp only [checkObserved, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at h
  rcases h.2 with hdead | h
  · left
    cases ht : Γ[i]? with
    | none => simp [ht] at hdead
    | some A =>
      rw [ht] at hdead
      exact ⟨A, rfl, fun n W v hv ho => impossible_sound (by simpa using hdead) hv ho⟩
  right
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
      · simp only [beq_iff_eq,he,↓reduceIte,Bool.or_eq_true] at hc
        simp only [he,↓reduceIte]
        rcases hc with hc | hc
        · exact .inl (PositiveCertificates.check_sound hc)
        · right
          cases o with
          | boolean _ => simp [fieldRefinements] at hc
          | tag t q =>
            simp only [fieldRefinements, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨⟨k, f⟩, hk, rfl, hck⟩ := hc
            exact ⟨t, q, f, rfl, hk, PositiveCertificates.check_sound hck⟩

/-- A branch edge's environment, one level above the one it is used at: a
field slice needs the heap's contents at the field, which the world types one
level down. -/
theorem ObservedCovers.env {G : NormalGraph ι} {Γ Δ i o mapping fields ρ n W h}
    (hc : ObservedCovers G Γ Δ i o mapping fields) (he : EnvOk G Γ ρ (n+1) W)
    (ho : o.holds (ρ i)) (hh : HeapOk (n+1) W h)
    (hl : ∀ k f, (k, f) ∈ fields → ∃ flds c l, ρ k = .objAt flds c ∧ flds.lookup f = some l ∧
      h[l]? = some (ρ i)) :
    EnvOk G Δ (mapEnv mapping ρ) (n+1) W := by
  rcases hc with ⟨A, ha, himp⟩ | hc
  · exact (himp _ _ _ (he.2 _ A ha) ho).elim
  refine ⟨fun j => he.1 (slot mapping j), ?_⟩
  intro j B hj
  obtain ⟨A,ha,h⟩ := hc j B hj
  by_cases hij : slot mapping j = i
  · simp only [hij,↓reduceIte] at h
    change meaning G B (n+1) W (ρ (slot mapping j))
    rw [hij]
    exact h (n+1) W _ (by simpa [hij] using he.2 _ A ha) ho
  · simp only [hij,↓reduceIte] at h
    rcases h with h | ⟨t, q, f, rfl, hf, hs⟩
    · exact h.sound (n+1) W _ (he.2 _ A ha)
    · obtain ⟨flds, c, l, hv, hfl, hu⟩ := hl _ f hf
      exact hs.sound (n+1) W _ (fieldSlice_sound (he.2 _ A ha) hh hv hfl hu ho)

#print axioms fieldSlice_sound
#print axioms checkObservedSub_sound
#print axioms checkObserved_sound
#print axioms ObservedCovers.env
end Verification.Model.BranchRefinement
