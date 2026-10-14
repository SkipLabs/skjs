import Verification.Programs.ProgramCertificates

/-! Supplied point environments with checked incoming edges. Environment slots
keep their de Bruijn positions: an edge can widen slots and forget a suffix,
but cannot silently reorder values. No join or invariant inference is performed.
Explicit mappings additionally support selection, reordering and alias retention.
Every checker here takes a proved instance image checker (`InstanceImageCheck`);
the finite one is the default. -/
namespace Verification.PointClaims
open ProgramTyping PositiveGraphs PositiveRules ProgramCertificates
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

abbrev EdgeEvidence (ι : Type) := List (PositiveCertificates.SubtypeChoices ι)

/-- Check incoming slots against outgoing contracts, retaining unfinished comparisons. -/
@[nospecialize] def checkEdgeResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) :
    List (Ty ι) → List (Ty ι) → EdgeEvidence ι → CheckResult ι Unit
  | _, [], [] => pure ()
  | A :: Γ, B :: Δ, p :: ps =>
    (ProgramCertificates.checkSubtypeUsing G images A B p).bind fun _ => checkEdgeResult G images Γ Δ ps
  | _, _, _ => failure

@[nospecialize] def checkEdgeUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (ps : EdgeEvidence ι) : Bool :=
  (checkEdgeResult G images Γ Δ ps).accepted

theorem checkEdgeUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (ps : EdgeEvidence ι) :
    checkEdgeUsing G images Γ Δ ps = match Γ, Δ, ps with
    | _, [], [] => true
    | A :: Γ, B :: Δ, p :: ps =>
        PositiveCertificates.checkUsing G images A B p && checkEdgeUsing G images Γ Δ ps
    | _, _, _ => false := by
  cases Γ <;> cases Δ <;> cases ps <;>
    simp only [checkEdgeUsing, checkEdgeResult, CheckResult.accepted_bind,
      ProgramCertificates.checkSubtypeUsing_accepted] <;> rfl

/-- The finite image checker, the default. -/
abbrev checkEdge [DecidableEq ι] (G : NormalGraph ι) :=
  @checkEdgeUsing _ _ G (finiteInstanceImages G)

/-- Coverage is per slot, with no least-upper-bound operation: each outgoing
slot's type contains its incoming slot's, as families. -/
def Covers (G : NormalGraph ι) (Γ Δ : List (Ty ι)) : Prop :=
  ∀ (i : Nat) B, Δ[i]? = some B → ∃ A, Γ[i]? = some A ∧ FamLe (meaning G A) (meaning G B)

theorem checkEdge_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {Γ Δ ps} (hc : checkEdgeUsing G images Γ Δ ps = true) : Covers G Γ Δ := by
  induction Δ generalizing Γ ps with
  | nil => simp [Covers]
  | cons B Δ ih =>
    cases Γ with
    | nil => cases ps <;> simp [checkEdgeUsing_eq] at hc
    | cons A Γ =>
      cases ps with
      | nil => simp [checkEdgeUsing_eq] at hc
      | cons p ps =>
        rw [checkEdgeUsing_eq] at hc
        simp only [Bool.and_eq_true] at hc
        intro i C hi
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst C
          exact ⟨A, rfl, PositiveCertificates.acceptedUsing hc.1⟩
        | succ i =>
          obtain ⟨D, hd, hs⟩ := ih hc.2 i C hi
          exact ⟨D, hd, hs⟩

/-- Every concrete environment meeting the incoming claim meets the supplied
outgoing claim, in the same world. Heap contents are not refinements of slots. -/
theorem Covers.env {G : NormalGraph ι} {Γ Δ ρ n W}
    (hc : Covers G Γ Δ) (he : EnvOk G Γ ρ n W) : EnvOk G Δ ρ n W := by
  refine ⟨he.1, ?_⟩
  intro i B hi
  obtain ⟨A, ha, hab⟩ := hc i B hi
  exact hab n W (ρ i) (he.2 i A ha)

theorem checked_env [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {Γ Δ ps ρ n W}
    (hc : checkEdgeUsing G images Γ Δ ps = true) (he : EnvOk G Γ ρ n W) : EnvOk G Δ ρ n W :=
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

def MappedCovers (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (mapping : Mapping) : Prop :=
  ∀ i B, Δ[i]? = some B → ∃ A, Γ[slot mapping i]? = some A ∧ FamLe (meaning G A) (meaning G B)

/-- A mapped slot names existing source, target and evidence entries. -/
@[nospecialize] def checkSlotResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (source target : Option (Ty ι)) (evidence : Option (PositiveCertificates.SubtypeChoices ι)) : CheckResult ι Unit :=
  match source, target, evidence with
  | some A, some B, some p => ProgramCertificates.checkSubtypeUsing G images A B p
  | _, _, _ => failure

theorem checkSlotResult_accepted [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (source target : Option (Ty ι)) (evidence : Option (PositiveCertificates.SubtypeChoices ι)) :
    (checkSlotResult G images source target evidence).accepted = match source, target, evidence with
    | some A, some B, some p => PositiveCertificates.checkUsing G images A B p
    | _, _, _ => false := by
  cases source <;> cases target <;> cases evidence <;>
    simp only [checkSlotResult, ProgramCertificates.checkSubtypeUsing_accepted] <;> rfl

@[nospecialize] def checkMappedResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (mapping : Mapping) (ps : EdgeEvidence ι) : CheckResult ι Unit :=
  match mapping with
  | none => checkEdgeResult G images Γ Δ ps
  | some slots =>
      (CheckResult.ofBool (decide (slots.length = Δ.length ∧ ps.length = Δ.length))).bind fun _ =>
      CheckResult.all (List.range Δ.length) fun i =>
        checkSlotResult G images Γ[slot mapping i]? Δ[i]? ps[i]?

@[nospecialize] def checkMappedUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (mapping : Mapping) (ps : EdgeEvidence ι) : Bool :=
  (checkMappedResult G images Γ Δ mapping ps).accepted

theorem checkMappedUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (Γ Δ : List (Ty ι)) (mapping : Mapping) (ps : EdgeEvidence ι) :
    checkMappedUsing G images Γ Δ mapping ps =
  match mapping with
  | none => checkEdgeUsing G images Γ Δ ps
  | some slots => decide (slots.length = Δ.length ∧ ps.length = Δ.length) &&
      (List.range Δ.length).all (fun i =>
        match Γ[slot mapping i]?, Δ[i]?, ps[i]? with
        | some A, some B, some p => PositiveCertificates.checkUsing G images A B p
        | _, _, _ => false) := by
  cases mapping <;> simp only [checkMappedUsing, checkMappedResult, CheckResult.accepted_bind,
    CheckResult.accepted_ofBool, CheckResult.accepted_all, checkSlotResult_accepted]
  rfl

abbrev checkMapped [DecidableEq ι] (G : NormalGraph ι) :=
  @checkMappedUsing _ _ G (finiteInstanceImages G)

theorem checkMapped_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {Γ Δ mapping ps}
    (hc : checkMappedUsing G images Γ Δ mapping ps = true) : MappedCovers G Γ Δ mapping := by
  cases mapping with
  | none => exact checkEdge_sound hc
  | some slots =>
    simp only [checkMappedUsing_eq, Bool.and_eq_true, List.all_eq_true] at hc
    intro i B hi
    have h := hc.2 i (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1)
    rw [hi] at h
    cases ha : Γ[slot (some slots) i]? with
    | none => simp [ha] at h
    | some A =>
      cases hp : ps[i]? with
      | none => simp [ha, hp] at h
      | some p => exact ⟨A, rfl, PositiveCertificates.acceptedUsing (by simpa [ha, hp] using h)⟩

theorem MappedCovers.env {G : NormalGraph ι} {Γ Δ mapping ρ n W}
    (hc : MappedCovers G Γ Δ mapping) (he : EnvOk G Γ ρ n W) :
    EnvOk G Δ (mapEnv mapping ρ) n W := by
  refine ⟨fun i => he.1 (slot mapping i), ?_⟩
  intro i B hi
  obtain ⟨A, ha, hab⟩ := hc i B hi
  exact hab n W (ρ (slot mapping i)) (he.2 _ A ha)

/-- A supplied merge claim is checked separately against every incoming edge. -/
@[nospecialize] def checkIncomingResult [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (target : List (Ty ι)) (incoming : List (List (Ty ι) × EdgeEvidence ι)) : CheckResult ι Unit :=
  CheckResult.all incoming fun edge => checkEdgeResult G images edge.1 target edge.2

@[nospecialize] def checkIncomingUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (target : List (Ty ι)) (incoming : List (List (Ty ι) × EdgeEvidence ι)) : Bool :=
  (checkIncomingResult G images target incoming).accepted

theorem checkIncomingUsing_eq [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (target : List (Ty ι)) (incoming : List (List (Ty ι) × EdgeEvidence ι)) :
    checkIncomingUsing G images target incoming =
      incoming.all (fun edge => checkEdgeUsing G images edge.1 target edge.2) := by
  rw [checkIncomingUsing, checkIncomingResult, CheckResult.accepted_all]
  rfl

abbrev checkIncoming [DecidableEq ι] (G : NormalGraph ι) :=
  @checkIncomingUsing _ _ G (finiteInstanceImages G)

theorem incoming_env [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {target incoming Γ ps ρ n W}
    (hc : checkIncomingUsing G images target incoming = true) (hm : (Γ,ps) ∈ incoming)
    (he : EnvOk G Γ ρ n W) : EnvOk G target ρ n W := by
  rw [checkIncomingUsing_eq] at hc
  exact checked_env ((List.all_eq_true.mp hc) (Γ,ps) hm) he

/-- A computation followed by a checked point claim and a typed continuation.
The edge is checked after pushing the computation's result. Allocation and
mutation are handled by the existing world/heap safety theorem. -/
theorem bind_claim [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {Γ a A Δ b B ps}
    (ha : HasTyUsing G images Γ a A) (hc : checkEdgeUsing G images (A :: Γ) Δ ps = true)
    (hb : HasTyUsing G images Δ b B) (n W h ρ) (he : EnvOk G Γ ρ n W)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (excOf G) (meaning G B) n W h (.letE (instantiate 0 ρ a) (instantiate 1 ρ b)) := by
  apply ProgramTyping.bind (fun a => .letE a (instantiate 1 ρ b)) Step.letC Raises.letC n W h _ hw hh
    (ha.sound n W h ρ he hw hh)
  intro j hj U hx hu heap v hok hv hav
  cases j with
  | zero => trivial
  | succ k =>
    apply let_rule _ _ hv k U heap hu hok
    rw [instantiate_beta ρ he.1]
    have he' := (checked_env hc ((he.transfer (k+1) hj U hx).push hav)).transfer k
      (Nat.le_succ k) (trunc k (Nat.le_succ k) U) (WExt_refl _)
    exact hb.sound k _ heap (push v ρ) he' (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)

/-- Bind the two program-evidence roots to the actual source and target claims. -/
theorem checked_bind_claim [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {Γ a A Δ b B ps ea eb}
    (hja : ProgramCertificates.claim ea = ⟨Γ,a,A⟩)
    (ha : ProgramCertificates.checkTreeUsing G images ea = true)
    (hc : checkEdgeUsing G images (A :: Γ) Δ ps = true)
    (hjb : ProgramCertificates.claim eb = ⟨Δ,b,B⟩)
    (hb : ProgramCertificates.checkTreeUsing G images eb = true)
    (n W h ρ) (he : EnvOk G Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (excOf G) (meaning G B) n W h (.letE (instantiate 0 ρ a) (instantiate 1 ρ b)) := by
  apply bind_claim (G := G) (images := images) (Γ := Γ) (Δ := Δ) (A := A) _ hc _ n W h ρ he hw hh
  · simpa only [hja] using ProgramCertificates.checkTreeUsing_sound ea ha
  · simpa only [hjb] using ProgramCertificates.checkTreeUsing_sound eb hb

#print axioms checkEdge_sound
#print axioms checked_bind_claim
end Verification.PointClaims
