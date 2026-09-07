import Verification.ExperimentState.ProgramCertificates

/-! Supplied point environments with checked incoming edges. Environment slots
keep their de Bruijn positions: an edge can widen slots and forget a suffix,
but cannot silently reorder values. No join or invariant inference is performed.
Explicit mappings additionally support selection, reordering and alias retention. -/
namespace Verification.ExperimentState.PointClaims
open ProgramTyping PositiveGraphs PositiveRules

abbrev EdgeEvidence (ι : Type) := List (PositiveCertificates.Proof ι)

def checkEdge [DecidableEq ι] (G : NormalGraph ι) :
    List (Ty ι) → List (Ty ι) → EdgeEvidence ι → Bool
  | _, [], [] => true
  | A :: Γ, B :: Δ, p :: ps => PositiveCertificates.check G A B p && checkEdge G Γ Δ ps
  | _, _, _ => false

/-- Declarative coverage is per slot, with no least-upper-bound operation. -/
def Covers [DecidableEq ι] (G : NormalGraph ι) (Γ Δ : List (Ty ι)) : Prop :=
  ∀ (i : Nat) B, Δ[i]? = some B → ∃ A, Γ[i]? = some A ∧ Sub G A B

theorem checkEdge_sound [DecidableEq ι] {G : NormalGraph ι} {Γ Δ ps}
    (hc : checkEdge G Γ Δ ps = true) : Covers G Γ Δ := by
  induction Δ generalizing Γ ps with
  | nil => simp [Covers]
  | cons B Δ ih =>
    cases Γ with
    | nil => cases ps <;> simp [checkEdge] at hc
    | cons A Γ =>
      cases ps with
      | nil => simp [checkEdge] at hc
      | cons p ps =>
        simp only [checkEdge, Bool.and_eq_true] at hc
        intro i C hi
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst C
          exact ⟨A, rfl, PositiveCertificates.check_sound hc.1⟩
        | succ i =>
          obtain ⟨D, hd, hs⟩ := ih hc.2 i C hi
          exact ⟨D, hd, hs⟩

theorem checkEdge_complete [DecidableEq ι] {G : NormalGraph ι} {Γ Δ}
    (hc : Covers G Γ Δ) : ∃ ps, checkEdge G Γ Δ ps = true := by
  induction Δ generalizing Γ with
  | nil => exact ⟨[], by cases Γ <;> rfl⟩
  | cons B Δ ih =>
    obtain ⟨A, ha, hab⟩ := hc 0 B rfl
    cases Γ with
    | nil => simp at ha
    | cons D Γ =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst D
      obtain ⟨p, hp⟩ := PositiveCertificates.check_complete hab
      obtain ⟨ps, hps⟩ := ih (fun i C hi => hc (i+1) C hi)
      exact ⟨p :: ps, by simp [checkEdge, hp, hps]⟩

/-- Every concrete environment meeting the incoming claim meets the supplied
outgoing claim, in the same world. Heap contents are not refinements of slots. -/
theorem Covers.env [DecidableEq ι] {G : NormalGraph ι} {Γ Δ ρ n W}
    (hc : Covers G Γ Δ) (he : EnvOk G Γ ρ n W) : EnvOk G Δ ρ n W := by
  refine ⟨he.1, ?_⟩
  intro i B hi
  obtain ⟨A, ha, hab⟩ := hc i B hi
  exact hab.sound n W (ρ i) (he.2 i A ha)

theorem checked_env [DecidableEq ι] {G : NormalGraph ι} {Γ Δ ps ρ n W}
    (hc : checkEdge G Γ Δ ps = true) (he : EnvOk G Γ ρ n W) : EnvOk G Δ ρ n W :=
  (checkEdge_sound hc).env he

/-- Explicit maps belong to the program: target slot i receives source slot
`slots[i]`. None preserves positions. Repetition retains aliases, never copies
heap contents. Out-of-range slots are rejected by the checker. -/
abbrev Mapping := Option (List Nat)

def slot (mapping : Mapping) (i : Nat) : Nat :=
  match mapping with
  | none => i
  | some slots => slots[i]?.getD 0

def mapEnv (mapping : Mapping) (ρ : Env) : Env := fun i => ρ (slot mapping i)

def MappedCovers [DecidableEq ι] (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (mapping : Mapping) : Prop :=
  ∀ i B, Δ[i]? = some B → ∃ A, Γ[slot mapping i]? = some A ∧ Sub G A B

def checkMapped [DecidableEq ι] (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (mapping : Mapping) (ps : EdgeEvidence ι) : Bool :=
  match mapping with
  | none => checkEdge G Γ Δ ps
  | some slots => decide (slots.length = Δ.length ∧ ps.length = Δ.length) &&
      (List.range Δ.length).all (fun i =>
        match Γ[slot mapping i]?, Δ[i]?, ps[i]? with
        | some A, some B, some p => PositiveCertificates.check G A B p
        | _, _, _ => false)

theorem checkMapped_sound [DecidableEq ι] {G : NormalGraph ι} {Γ Δ mapping ps}
    (hc : checkMapped G Γ Δ mapping ps = true) : MappedCovers G Γ Δ mapping := by
  cases mapping with
  | none => exact checkEdge_sound hc
  | some slots =>
    simp only [checkMapped, Bool.and_eq_true, List.all_eq_true] at hc
    intro i B hi
    have h := hc.2 i (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1)
    rw [hi] at h
    cases ha : Γ[slot (some slots) i]? with
    | none => simp [ha] at h
    | some A =>
      cases hp : ps[i]? with
      | none => simp [ha, hp] at h
      | some p => exact ⟨A, rfl, PositiveCertificates.check_sound (by simpa [ha, hp] using h)⟩

theorem MappedCovers.env [DecidableEq ι] {G : NormalGraph ι} {Γ Δ mapping ρ n W}
    (hc : MappedCovers G Γ Δ mapping) (he : EnvOk G Γ ρ n W) :
    EnvOk G Δ (mapEnv mapping ρ) n W := by
  refine ⟨fun i => he.1 (slot mapping i), ?_⟩
  intro i B hi
  obtain ⟨A, ha, hab⟩ := hc i B hi
  exact hab.sound n W (ρ (slot mapping i)) (he.2 _ A ha)

/-- A supplied merge claim is checked separately against every incoming edge. -/
def checkIncoming [DecidableEq ι] (G : NormalGraph ι) (target : List (Ty ι))
    (incoming : List (List (Ty ι) × EdgeEvidence ι)) : Bool :=
  incoming.all (fun edge => checkEdge G edge.1 target edge.2)

theorem incoming_env [DecidableEq ι] {G : NormalGraph ι} {target incoming Γ ps ρ n W}
    (hc : checkIncoming G target incoming = true) (hm : (Γ,ps) ∈ incoming)
    (he : EnvOk G Γ ρ n W) : EnvOk G target ρ n W :=
  checked_env ((List.all_eq_true.mp hc) (Γ,ps) hm) he

/-- A computation followed by a checked point claim and a typed continuation.
The edge is checked after pushing the computation's result. Allocation and
mutation are handled by the existing world/heap safety theorem. -/
theorem bind_claim [DecidableEq ι] {G : NormalGraph ι} {Γ a A Δ b B ps}
    (ha : HasTy G Γ a A) (hc : checkEdge G (A :: Γ) Δ ps = true)
    (hb : HasTy G Δ b B) (n W h ρ) (he : EnvOk G Γ ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaning G B) n W h (.app (.lam (instantiate 1 ρ b)) (instantiate 0 ρ a)) := by
  apply ProgramTyping.bind (.app (.lam (instantiate 1 ρ b))) (Step.appR rfl) n W h _ hw hh
    (ha.sound n W h ρ he hw hh)
  intro j hj U hx hu heap v hok hv hav
  cases j with
  | zero => trivial
  | succ k =>
    apply beta_rule _ _ hv k U heap hu hok
    rw [instantiate_beta ρ he.1]
    have he' := (checked_env hc ((he.transfer (k+1) hj U hx).push hav)).transfer k
      (Nat.le_succ k) (trunc k (Nat.le_succ k) U) (WExt_refl _)
    exact hb.sound k _ heap (push v ρ) he' (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)

/-- Bind the two program-evidence roots to the actual source and target claims. -/
theorem checked_bind_claim [DecidableEq ι] {G : NormalGraph ι} {Γ a A Δ b B ps ea eb}
    (hja : ProgramCertificates.claim ea = ⟨Γ,a,A⟩)
    (ha : ProgramCertificates.checkTree G ea = true)
    (hc : checkEdge G (A :: Γ) Δ ps = true)
    (hjb : ProgramCertificates.claim eb = ⟨Δ,b,B⟩)
    (hb : ProgramCertificates.checkTree G eb = true)
    (n W h ρ) (he : EnvOk G Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaning G B) n W h (.app (.lam (instantiate 1 ρ b)) (instantiate 0 ρ a)) := by
  apply bind_claim (G := G) (Γ := Γ) (Δ := Δ) (A := A) _ hc _ n W h ρ he hw hh
  · simpa only [hja] using ProgramCertificates.checkTree_sound ea ha
  · simpa only [hjb] using ProgramCertificates.checkTree_sound eb hb

#print axioms checkEdge_sound
#print axioms checkEdge_complete
#print axioms checked_bind_claim
end Verification.ExperimentState.PointClaims
