import Verification.Model.Programs.CertificateProducer

/-! # Graph evidence is parametric in the assignment

A graph's parameter rows mean what its assignment `env` gives them, and a
graph's `meaning` reads them there. No check reads `env`: every checker reads a
graph through its rows, schemes, parameter kinds and meets. This file proves
it for the whole graph checker, `CertificateProducer.acceptUsing`, with any
proved instance image checker: acceptance of a graph is acceptance of every
reassignment of it by the same checker (`accept_reassign`). The
safety theorem for accepted evidence then holds at every assignment
(`accepted_at`), so a body checked once with its type parameters as opaque
parameter rows is safe at every instantiation of them.

Most checkers are definitionally independent of `env`; the lemmas below are
for the ones whose unfolding the kernel does not do on its own: the recursive
checkers, the inductive subtyping judgment, and the checkers built on them. -/
namespace Verification.Model.Parametricity
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ProgramCertificates
  PositiveCertificates PointClaims BranchRefinement HeapExpressionRules ControlFlow

variable {ι : Type} [DecidableEq ι] (G : NormalGraph ι) (η : MixedAssignment ι)

theorem reads_reassign : reads (reassign G η) = reads G := rfl

theorem readsFrom_go_reassign : ∀ fuel (seen frontier : List ι),
    readsFrom.go (reassign G η) fuel seen frontier = readsFrom.go G fuel seen frontier
  | 0, _, _ => rfl
  | fuel + 1, seen, frontier => by
    simp only [readsFrom.go, reads_reassign, readsFrom_go_reassign fuel]

theorem readsFrom_reassign (fuel : Nat) (S : List ι) :
    readsFrom (reassign G η) fuel S = readsFrom G fuel S := by
  simp only [readsFrom, readsFrom_go_reassign]

theorem freeMapOf_reassign (D : List ι) : ∀ fuel (V : FreeMap ι),
    freeMapOf (reassign G η) D fuel V = freeMapOf G D fuel V
  | 0, _ => rfl
  | fuel + 1, V => by
    simp only [freeMapOf, reads_reassign, freeMapOf_reassign D fuel]
    rfl

theorem expand_reassign (F : List ι) : expand (reassign G η) F = expand G F := rfl

/-- Fixing the assignment erases an earlier reassignment of image metadata. -/
theorem images_reassign_fixed (images : InstanceImageCheck G) :
    (images.reassign η).reassign (ParameterAssignment.empty .mixed) =
      images.reassign (ParameterAssignment.empty .mixed) := by
  cases hs : images.sub <;>
    simp only [InstanceImageCheck.reassign, hs, Option.map_none, Option.map_some] <;> rfl

theorem checkStructural_reassign (images : InstanceImageCheck G)
    (S T : List ι) (known : Known ι) (table : Table ι)
    (arrows : PositiveCertificates.Evidence ι) :
    checkStructural (reassign G η) (images.reassign η) S T known table arrows =
      checkStructural G images S T known table arrows := by
  simp only [checkStructural, images_reassign_fixed]
  rfl

theorem comparePrepared_reassign (images : InstanceImageCheck G)
    (S T : List ι) (known : Known ι) (fb : Fallback ι) :
    comparePrepared (reassign G η) (images.reassign η) S T known fb =
      comparePrepared G images S T known fb := by
  simp only [comparePrepared, images_reassign_fixed, checkStructural_reassign]
  rfl

/-- Reassigning parameter meanings preserves execution policy. -/
theorem budget_reassign (images : InstanceImageCheck G) :
    (images.reassign η).budget = images.budget := rfl

/-- Structural comparison uses one fixed parameter assignment. -/
theorem compareStructural_reassign (images : InstanceImageCheck G) (S T : List ι)
    (known : Known ι) :
    compareStructural (reassign G η) (images.reassign η) S T known =
      compareStructural G images S T known := by
  simp only [compareStructural, images_reassign_fixed, comparePrepared_reassign, budget_reassign]
  rfl

/-- A bound is decided at the graph with its assignment fixed. -/
theorem boundOk_reassign (images : InstanceImageCheck G) (binders : List ι)
    (θs : List (List ι)) (b : ι × List ι) :
    boundOk (reassign G η) (images.reassign η) binders θs b = boundOk G images binders θs b := by
  simp only [boundOk, compareStructural_reassign, budget_reassign]

/-! Every checker below takes a proved instance image checker. Its check is
the same function at every reassignment (`InstanceImageCheck.reassign`). -/
variable (images : InstanceImageCheck G)

theorem checkInstArrs_reassign (S : List ι) (L : Ops ι)
    (M : List (CallEffects.RestArrow (List ι))) (c : Instance ι) :
    checkInstArrsUsing (reassign G η) (images.reassign η) S L M c =
      checkInstArrsUsing G images S L M c := by
  simp only [checkInstArrsUsing, boundOk_reassign]
  rfl

theorem checkInst_reassign (S T : List ι) (c : Instance ι) :
    checkInstUsing (reassign G η) (images.reassign η) S T c = checkInstUsing G images S T c := by
  simp only [checkInstUsing, checkInstArrs_reassign]
  rfl

theorem sub_reassign : (images.reassign η).sub = images.sub.map (·.reassign η) := rfl

/-- The premise judgment and family certificates are checked at a fixed
assignment, the same for the graph and its reassignments. -/
theorem premAt_reassign (r : Renaming G) (S T : List ι) :
    premAt (reassign G η) (images.reassign η) (r.reassign η) S T = premAt G images r S T := rfl

theorem subsetUsing_reassign (S T : List ι) :
    subsetUsing (reassign G η) (images.reassign η) S T = subsetUsing G images S T := by
  unfold subsetUsing
  cases hr : images.sub with
  | none => simp only [sub_reassign, hr, Option.map_none]
  | some r => simp only [sub_reassign, hr, Option.map_some, premAt_reassign]

theorem compareUsing_reassign (S T : List ι) (instantiation : Unit → Option (Instance ι))
    (members : Table ι → List (KnownInstance ι)) :
    compareUsing (reassign G η) (images.reassign η) S T instantiation members =
      compareUsing G images S T instantiation members := by
  have hi : checkInstUsing (reassign G η) (images.reassign η) S T =
      checkInstUsing G images S T := funext fun c => checkInst_reassign G η images S T c
  simp only [compareUsing, subsetUsing_reassign, hi, checkInstArrs_reassign,
    images_reassign_fixed, comparePrepared_reassign, budget_reassign]
  rfl

theorem check_reassign (S T : List ι) (p : SubtypeChoices ι) :
    PositiveCertificates.checkUsing (reassign G η) (images.reassign η) S T p =
      PositiveCertificates.checkUsing G images S T p := by
  simp only [PositiveCertificates.checkUsing, compareUsing_reassign, budget_reassign]

/-- The subtype checker as a function of its graph. -/
theorem check_fun_reassign :
    PositiveCertificates.checkUsing (reassign G η) (images.reassign η) =
      PositiveCertificates.checkUsing G images := by
  funext S T p; exact check_reassign G η images S T p

theorem checkEdge_reassign (Γ Δ : List (List ι)) (ps : EdgeEvidence ι) :
    checkEdgeUsing (reassign G η) (images.reassign η) Γ Δ ps = checkEdgeUsing G images Γ Δ ps := by
  induction ps generalizing Γ Δ with
  | nil => cases Γ <;> cases Δ <;> rfl
  | cons p ps ih => cases Γ <;> cases Δ <;> simp only [checkEdgeUsing, check_reassign, ih]

theorem checkMapped_reassign (Γ Δ : List (List ι)) (m : Mapping) (ps : EdgeEvidence ι) :
    checkMappedUsing (reassign G η) (images.reassign η) Γ Δ m ps =
      checkMappedUsing G images Γ Δ m ps := by
  cases m <;> simp only [checkMappedUsing, checkEdge_reassign, check_fun_reassign]

/-- The realm checks read the graph's rows only. -/
theorem realmFree_reassign (P : List ι) : realmFree (reassign G η) P = realmFree G P := by
  simp only [realmFree, readsFrom_reassign, freeMapOf_reassign]
  rfl

theorem allocRealm_reassign (parts : List (PropKey × List ι)) :
    allocRealm (reassign G η) parts = allocRealm G parts := by
  unfold allocRealm
  simp only [realmFree_reassign]
  rfl

theorem realmArrayLabel_reassign :
    BranchRefinement.realmArrayLabel (reassign G η) = BranchRefinement.realmArrayLabel G := by
  funext L
  unfold BranchRefinement.realmArrayLabel
  simp only [realmFree_reassign]
  rfl

theorem arraySlice_reassign (A B : List ι) :
    BranchRefinement.arraySlice (reassign G η) A B = BranchRefinement.arraySlice G A B := by
  unfold BranchRefinement.arraySlice
  simp only [realmArrayLabel_reassign]
  rfl

theorem checkObservedSub_reassign (A B : List ι) (o : Observation) (p : SubtypeChoices ι) :
    checkObservedSubUsing (reassign G η) (images.reassign η) A B o p =
      checkObservedSubUsing G images A B o p := by
  cases o <;> simp only [checkObservedSubUsing, check_reassign, arraySlice_reassign] <;> rfl

theorem fieldRefinements_reassign (o : Observation) (fields : List (Nat × PropKey)) (A B : List ι)
    (j : Nat) (p : SubtypeChoices ι) :
    fieldRefinements o fields A B j (reassign G η) (images.reassign η) p =
      fieldRefinements o fields A B j G images p := by
  cases o <;> simp only [fieldRefinements, check_fun_reassign] <;> rfl

theorem optionalRefinements_reassign (o : Observation) (optionals : List (Nat × PropKey)) (A B : List ι)
    (j : Nat) :
    optionalRefinements o optionals A B j (reassign G η) = optionalRefinements o optionals A B j G := rfl

theorem checkObserved_reassign (Γ Δ : List (List ι)) (tested : Nat) (o : Observation)
    (m : Mapping) (ps : EdgeEvidence ι) (fields optionals : List (Nat × PropKey)) :
    checkObservedUsing (reassign G η) (images.reassign η) Γ Δ tested o m ps fields optionals =
      checkObservedUsing G images Γ Δ tested o m ps fields optionals := by
  simp only [checkObservedUsing, checkObservedSub_reassign, check_fun_reassign,
    fieldRefinements_reassign, optionalRefinements_reassign]
  rfl

theorem CallProofs_reassign (q : CallEffects.Arrow (List ι)) (c : CallEffects.MethodArrow (List ι))
    (ps : List (SubtypeChoices ι) × SubtypeChoices ι) :
    CallProofsUsing (reassign G η) (images.reassign η) q c ps = CallProofsUsing G images q c ps := by
  simp only [CallProofsUsing, check_reassign]

theorem RestProofs_reassign (q : CallEffects.RestArrow (List ι)) (c : CallEffects.MethodRestArrow (List ι))
    (ps : List (SubtypeChoices ι) × SubtypeChoices ι × SubtypeChoices ι) :
    RestProofsUsing (reassign G η) (images.reassign η) q c ps = RestProofsUsing G images q c ps := by
  simp only [RestProofsUsing, check_reassign]

/-- A generic closure's capture check reads the graph's rows only. -/
theorem capturesFree_reassign (s : SchemeRow ι) (Cs : List (List ι)) :
    capturesFree (reassign G η) s Cs = capturesFree G s Cs := by
  simp only [capturesFree, captureDomain, captureFree, readsFrom_reassign, freeMapOf_reassign]
  rfl

theorem graphCodesChecked_reassign (A : List ι) (codes : CodeEntry ι → Bool) (arity : Nat)
    (E : List Tm) (K : List (ControlFlow.Continuation × Option ControlFlow.Target)) (start : Nat)
    (Cs : List (List ι)) :
    graphCodesChecked (reassign G η) A codes arity E K start Cs =
      graphCodesChecked G A codes arity E K start Cs := by
  unfold graphCodesChecked
  simp only [capturesFree_reassign]
  rfl

theorem Local_reassign (j : Sequent ι) (r : Rule ι) (ps : List (Sequent ι))
    (codes : CodeEntry ι → Bool := fun _ => false) :
    LocalUsing (reassign G η) (images.reassign η) j r ps codes = LocalUsing G images j r ps codes := by
  unfold LocalUsing
  simp only [check_fun_reassign, CallProofs_reassign, RestProofs_reassign, graphCodesChecked_reassign,
    allocRealm_reassign]
  rfl

theorem checkTree_reassign (e : ProgramCertificates.Evidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) :
    checkTreeUsing (reassign G η) (images.reassign η) e codes = checkTreeUsing G images e codes := by
  match e with
  | .node j r ps =>
    rw [checkTreeUsing, checkTreeUsing]
    simp only [Local_reassign]
    congr 1
    congr 1
    funext x
    exact checkTree_reassign x.val codes
termination_by sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem x.property
  simp only [ProgramCertificates.Evidence.node.sizeOf_spec]
  omega

theorem checkStep_reassign (j : Sequent ι) (k : HeapKnowledge.Knowledge) (e : StepEvidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) :
    checkStepUsing (reassign G η) (images.reassign η) j k e codes = checkStepUsing G images j k e codes := by
  cases e <;> simp only [checkStepUsing, checkTree_reassign, check_fun_reassign] <;> rfl

theorem checkTarget_reassign (P : Program) (C : ControlFlow.Certificate ι) (Γ : List (List ι)) (t : Target)
    (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge) :
    checkTargetUsing (reassign G η) (images.reassign η) P C Γ t p facts =
      checkTargetUsing G images P C Γ t p facts := by
  simp only [checkTargetUsing, checkMapped_reassign]

theorem checkBranchTarget_reassign (P : Program) (C : ControlFlow.Certificate ι) (Γ : List (List ι))
    (o : Observation) (t : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge) :
    checkBranchTargetUsing (reassign G η) (images.reassign η) P C Γ o t p facts =
      checkBranchTargetUsing G images P C Γ o t p facts := by
  simp only [checkBranchTargetUsing, checkObserved_reassign]

theorem checkHandler_reassign (P : Program) (C : ControlFlow.Certificate ι) (node : Node) (c : NodeEvidence ι) :
    checkHandlerUsing (reassign G η) (images.reassign η) P C node c =
      checkHandlerUsing G images P C node c := by
  simp only [checkHandlerUsing, checkTarget_reassign]
  rfl

theorem checkNode_reassign (Rty : List ι) (P : Program) (C : ControlFlow.Certificate ι) (node : Node)
    (c : NodeEvidence ι) (codes : CodeEntry ι → Bool := fun _ => false) :
    checkNodeUsing (reassign G η) (images.reassign η) Rty P C node c codes =
      checkNodeUsing G images Rty P C node c codes := by
  simp only [checkNodeUsing, checkHandler_reassign, checkStep_reassign, checkTarget_reassign,
    checkBranchTarget_reassign]
  rfl

theorem checkGraph_reassign (Rty : List ι) (P : Program) (C : ControlFlow.Certificate ι)
    (codes : CodeEntry ι → Bool := fun _ => false) :
    checkGraphUsing (reassign G η) (images.reassign η) Rty P C codes =
      checkGraphUsing G images Rty P C codes := by
  simp only [checkGraphUsing, checkNode_reassign]

theorem checkEntry_reassign (Rty : List ι) (P : Program) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (List ι)) (codes : CodeEntry ι → Bool := fun _ => false) :
    checkEntryUsing (reassign G η) (images.reassign η) Rty P C start inputs codes =
      checkEntryUsing G images Rty P C start inputs codes := by
  simp only [checkEntryUsing, checkGraph_reassign]

/-- **Acceptance reads no assignment.** A graph's evidence is accepted exactly
when it is accepted for every reassignment of the graph's parameter rows, by
the same image checker. -/
theorem accept_reassign (R : List ι) (P : Program) (claims : List (CertificateProducer.PointClaim ι))
    (C : ControlFlow.Certificate ι) (start : Nat) (inputs : List (List ι))
    (codes : CodeEntry ι → Bool := fun _ => false) :
    CertificateProducer.acceptUsing (reassign G η) (images.reassign η) R P claims C start inputs codes =
      CertificateProducer.acceptUsing G images R P claims C start inputs codes := by
  simp only [CertificateProducer.acceptUsing, checkEntry_reassign]

/-- **Parametricity.** Accepted evidence is safe at every assignment of the
graph's parameter rows: every input environment meeting the inputs read at
`η` runs safely to a result of the result type read at `η`. -/
theorem accepted_at {G : NormalGraph ι} {images : InstanceImageCheck G} {R P claims C start inputs}
    {codes : CodeEntry ι → Bool}
    (hc : CertificateProducer.acceptUsing G images R P claims C start inputs codes = true)
    (η : MixedAssignment ι) (n W h ρ)
    (he : EnvOk (reassign G η) inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hcodes : CodesSound (reassign G η) codes := by exact Verification.Model.ProgramCertificates.codesSound_none _) :
    SafeGraph P (meaning (reassign G η) R) n W h (.at start ρ) :=
  CertificateProducer.accepted_from_inputs
    ((accept_reassign G η images R P claims C start inputs codes).trans hc) n W h ρ he hw hh hcodes

#print axioms accept_reassign
#print axioms accepted_at

end Verification.Model.Parametricity

