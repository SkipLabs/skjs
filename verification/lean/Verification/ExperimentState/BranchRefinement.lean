import Verification.ExperimentState.PointClaims

/-! Refinement of immutable environment slots by an actual Boolean test.
Heap contents are not refined: the witness is equality of the tested value,
not a retained observation about a mutable location. -/
namespace Verification.ExperimentState.BranchRefinement
open ProgramTyping PositiveGraphs PositiveRules PositiveNormalization PointClaims

def booleanMember [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) (q : Bool) : Bool :=
  (expand G A).any fun c => match c with
    | .bool => true
    | .boolLit b => b == q
    | _ => false

def onlyBoolean (G : NormalGraph ι) (A : Ty ι) : Bool :=
  (expand G A).all fun c => match c with
    | .bool | .boolLit _ => true
    | _ => false

theorem booleanMember_sound [DecidableEq ι] {G : NormalGraph ι} {A q}
    (h : booleanMember G A q = true) (n W) :
    meaning G A n W (if q then .tru else .fls) := by
  rw [expand_sem]
  obtain ⟨c,hc,h⟩ := List.any_eq_true.mp h
  refine ⟨c,hc,?_⟩
  cases c <;> simp_all [sem, boolT]

theorem onlyBoolean_sound {G : NormalGraph ι} {A n W v}
    (h : onlyBoolean G A = true) (hv : meaning G A n W v) :
    v = .tru ∨ v = .fls := by
  rw [expand_sem] at hv
  obtain ⟨c,hc,hv⟩ := hv
  have h := List.all_eq_true.mp h c hc
  cases c <;> simp_all [sem, boolT]

def isSubset : PositiveCertificates.Proof ι → Bool
  | .subset => true
  | _ => false

/-- The tested slot uses its branch equality; every other mapped slot still
requires an ordinary subtype proof. The placeholder for the equality rule is
exactly `subset`, not an unchecked arbitrary proof. -/
def checkRefined [DecidableEq ι] (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (tested : Nat) (q : Bool) (mapping : Mapping) (ps : EdgeEvidence ι) : Bool :=
  (match mapping with | none => true | some slots => slots.length == Δ.length) &&
  ps.length == Δ.length && (List.range Δ.length).all (fun j =>
    match Γ[slot mapping j]?, Δ[j]?, ps[j]? with
    | some A, some B, some p =>
      if slot mapping j == tested then isSubset p && booleanMember G B q
      else PositiveCertificates.check G A B p
    | _, _, _ => false)

def RefinedCovers [DecidableEq ι] (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (tested : Nat) (q : Bool) (mapping : Mapping) : Prop :=
  ∀ j B, Δ[j]? = some B → ∃ A, Γ[slot mapping j]? = some A ∧
    (if slot mapping j = tested then booleanMember G B q = true else Sub G A B)

theorem checkRefined_sound [DecidableEq ι] {G : NormalGraph ι} {Γ Δ i q mapping ps}
    (h : checkRefined G Γ Δ i q mapping ps = true) : RefinedCovers G Γ Δ i q mapping := by
  simp only [checkRefined, Bool.and_eq_true, List.all_eq_true] at h
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
      · have hc' : (isSubset p && booleanMember G B q) = true := by simpa only [beq_iff_eq,he,↓reduceIte] using hc
        simp only [Bool.and_eq_true] at hc'
        simpa [he] using hc'.2
      · simp only [beq_iff_eq,he,↓reduceIte] at hc
        simp only [he,↓reduceIte]
        exact PositiveCertificates.check_sound hc

theorem RefinedCovers.env [DecidableEq ι] {G : NormalGraph ι} {Γ Δ i q mapping ρ n W}
    (hc : RefinedCovers G Γ Δ i q mapping) (he : EnvOk G Γ ρ n W)
    (hq : ρ i = (if q then .tru else .fls)) : EnvOk G Δ (mapEnv mapping ρ) n W := by
  refine ⟨fun j => he.1 (slot mapping j), ?_⟩
  intro j B hj
  obtain ⟨A,ha,h⟩ := hc j B hj
  by_cases hij : slot mapping j = i
  · simp only [hij,↓reduceIte] at h
    change meaning G B n W (ρ (slot mapping j))
    rw [hij,hq]
    exact booleanMember_sound h n W
  · simp only [hij,↓reduceIte] at h
    exact h.sound n W _ (he.2 _ A ha)

#print axioms checkRefined_sound
#print axioms RefinedCovers.env
end Verification.ExperimentState.BranchRefinement
