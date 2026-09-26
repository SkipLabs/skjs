import Verification.Model.Programs.CertificateProducer

/-! # Graph evidence is parametric in the assignment

A graph's parameter rows mean what its assignment `env` gives them, and a
graph's `meaning` reads them there. No check reads `env`: every checker reads a
graph through its rows, schemes, parameter kinds and meets. This file proves
it for the whole graph checker, `CertificateProducer.accept`: acceptance of a
graph is acceptance of every reassignment of it (`accept_reassign`). The
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

theorem checkArrow_reassign (table : Table ι) (L : Ops ι)
    (S : List (List ι × List (List ι) × List ι × List ι)) (Rt : List ι) (As : List (List ι))
    (d : List ι) (cert : ArrowCert ι) :
    checkArrow (reassign G η) table L S Rt As d cert = checkArrow G table L S Rt As d cert := by
  induction cert generalizing Rt As d <;> simp only [checkArrow, *] <;> rfl

/-- Method coverage along a prototype chain reads the graph's rows only. -/
theorem protoHolds_reassign (R : List ι → List ι → Prop) (known : Known ι) (self : List ι)
    (q : MethodMembers.Sig (List ι)) :
    ∀ d P, ProtoHolds (reassign G η) R known self q d P ↔ ProtoHolds G R known self q d P
  | 0, _ => Iff.rfl
  | d + 1, P => by
    simp only [ProtoHolds]
    exact or_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun P' =>
      and_congr Iff.rfl (protoHolds_reassign R known self q d P')))

theorem checkClause_reassign (table : Table ι) (known : Known ι) (proofs : PositiveCertificates.Evidence ι)
    (self : List ι) (a b : Clause (List ι)) :
    checkClause (reassign G η) table known proofs self a b = checkClause G table known proofs self a b := by
  have hA : ArrowsChecked (reassign G η) table proofs = ArrowsChecked G table proofs := by
    funext L S M; simp only [ArrowsChecked, checkArrow_reassign]
  unfold checkClause
  apply decide_eq_decide.mpr
  rw [hA]
  exact Iff.rfl

theorem checkCore_reassign (known : Known ι) (S T : List ι) (cert : PositiveCertificates.Certificate ι) :
    checkCore (reassign G η) known S T cert = checkCore G known S T cert := by
  simp only [checkCore, checkClause_reassign]
  rfl

theorem boundOk_reassign (binders : List ι) (θs : List (List ι)) (b : ι × List ι)
    (c : Option (PositiveCertificates.Certificate ι)) :
    boundOk (reassign G η) binders θs b c = boundOk G binders θs b c := by
  simp only [boundOk, checkCore_reassign]

theorem checkInstArrs_reassign (S : List ι) (L : Ops ι)
    (M : List (List ι × List (List ι) × List ι × List ι)) (c : Instance ι) :
    checkInstArrs (reassign G η) S L M c = checkInstArrs G S L M c := by
  simp only [checkInstArrs, boundOk_reassign]
  rfl

theorem checkInst_reassign (S T : List ι) (c : Instance ι) :
    checkInst (reassign G η) S T c = checkInst G S T c := by
  simp only [checkInst, checkInstArrs_reassign]
  rfl

theorem check_reassign (S T : List ι) (p : Proof ι) :
    PositiveCertificates.check (reassign G η) S T p = PositiveCertificates.check G S T p := by
  induction p generalizing S T <;>
    simp only [PositiveCertificates.check, checkCore_reassign, checkInstArrs_reassign,
      checkInst_reassign, *] <;> rfl

/-- The subtype checker as a function of its graph. -/
theorem check_fun_reassign :
    PositiveCertificates.check (reassign G η) = PositiveCertificates.check G := by
  funext S T p; exact check_reassign G η S T p

theorem checkEdge_reassign (Γ Δ : List (List ι)) (ps : EdgeEvidence ι) :
    checkEdge (reassign G η) Γ Δ ps = checkEdge G Γ Δ ps := by
  induction ps generalizing Γ Δ with
  | nil => cases Γ <;> cases Δ <;> rfl
  | cons p ps ih => cases Γ <;> cases Δ <;> simp only [checkEdge, check_reassign, ih]

theorem checkMapped_reassign (Γ Δ : List (List ι)) (m : Mapping) (ps : EdgeEvidence ι) :
    checkMapped (reassign G η) Γ Δ m ps = checkMapped G Γ Δ m ps := by
  cases m <;> simp only [checkMapped, checkEdge_reassign, check_fun_reassign]

theorem checkObservedSub_reassign (A B : List ι) (o : Observation) (p : Proof ι) :
    checkObservedSub (reassign G η) A B o p = checkObservedSub G A B o p := by
  cases o <;> simp only [checkObservedSub, check_reassign] <;> rfl

theorem fieldRefinements_reassign (o : Observation) (fields : List (Nat × PropKey)) (A B : List ι)
    (j : Nat) (p : Proof ι) :
    fieldRefinements o fields A B j (reassign G η) p = fieldRefinements o fields A B j G p := by
  cases o <;> simp only [fieldRefinements, check_fun_reassign] <;> rfl

theorem optionalRefinements_reassign (o : Observation) (optionals : List (Nat × PropKey)) (A B : List ι)
    (j : Nat) (p : Proof ι) :
    optionalRefinements o optionals A B j (reassign G η) p = optionalRefinements o optionals A B j G p := rfl

theorem checkObserved_reassign (Γ Δ : List (List ι)) (tested : Nat) (o : Observation)
    (m : Mapping) (ps : EdgeEvidence ι) (fields optionals : List (Nat × PropKey)) :
    checkObserved (reassign G η) Γ Δ tested o m ps fields optionals =
      checkObserved G Γ Δ tested o m ps fields optionals := by
  simp only [checkObserved, checkObservedSub_reassign, check_fun_reassign, fieldRefinements_reassign,
    optionalRefinements_reassign]
  rfl

theorem CallProofs_reassign (q : List ι × List (List ι) × List ι) (c : List (List ι) × List ι)
    (ps : List (Proof ι) × Proof ι) :
    CallProofs (reassign G η) q c ps = CallProofs G q c ps := by
  simp only [CallProofs, check_reassign]

theorem Local_reassign (j : Sequent ι) (r : Rule ι) (ps : List (Sequent ι))
    (codes : CodeEntry ι → Bool := fun _ => false) :
    Local (reassign G η) j r ps codes = Local G j r ps codes := by
  unfold Local
  simp only [check_fun_reassign, CallProofs_reassign]
  rfl

theorem checkTree_reassign (e : ProgramCertificates.Evidence ι)
    (codes : CodeEntry ι → Bool := fun _ => false) :
    checkTree (reassign G η) e codes = checkTree G e codes := by
  match e with
  | .node j r ps =>
    rw [checkTree, checkTree]
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
    checkStep (reassign G η) j k e codes = checkStep G j k e codes := by
  cases e <;> simp only [checkStep, checkTree_reassign, check_fun_reassign] <;> rfl

theorem checkTarget_reassign (P : Program) (C : ControlFlow.Certificate ι) (Γ : List (List ι)) (t : Target)
    (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge) :
    checkTarget (reassign G η) P C Γ t p facts = checkTarget G P C Γ t p facts := by
  simp only [checkTarget, checkMapped_reassign]

theorem checkBranchTarget_reassign (P : Program) (C : ControlFlow.Certificate ι) (Γ : List (List ι))
    (o : Observation) (t : Target) (p : EdgeEvidence ι) (facts : HeapKnowledge.Knowledge) :
    checkBranchTarget (reassign G η) P C Γ o t p facts = checkBranchTarget G P C Γ o t p facts := by
  simp only [checkBranchTarget, checkObserved_reassign]

theorem checkHandler_reassign (P : Program) (C : ControlFlow.Certificate ι) (node : Node) (c : NodeEvidence ι) :
    checkHandler (reassign G η) P C node c = checkHandler G P C node c := by
  simp only [checkHandler, checkTarget_reassign]
  rfl

theorem checkNode_reassign (Rty : List ι) (P : Program) (C : ControlFlow.Certificate ι) (node : Node)
    (c : NodeEvidence ι) (codes : CodeEntry ι → Bool := fun _ => false) :
    checkNode (reassign G η) Rty P C node c codes = checkNode G Rty P C node c codes := by
  simp only [checkNode, checkHandler_reassign, checkStep_reassign, checkTarget_reassign,
    checkBranchTarget_reassign]
  rfl

theorem checkGraph_reassign (Rty : List ι) (P : Program) (C : ControlFlow.Certificate ι)
    (codes : CodeEntry ι → Bool := fun _ => false) :
    checkGraph (reassign G η) Rty P C codes = checkGraph G Rty P C codes := by
  simp only [checkGraph, checkNode_reassign]

theorem checkEntry_reassign (Rty : List ι) (P : Program) (C : ControlFlow.Certificate ι) (start : Nat)
    (inputs : List (List ι)) (codes : CodeEntry ι → Bool := fun _ => false) :
    checkEntry (reassign G η) Rty P C start inputs codes = checkEntry G Rty P C start inputs codes := by
  simp only [checkEntry, checkGraph_reassign]

/-- **Acceptance reads no assignment.** A graph's evidence is accepted exactly
when it is accepted for every reassignment of the graph's parameter rows. -/
theorem accept_reassign (R : List ι) (P : Program) (claims : List (CertificateProducer.PointClaim ι))
    (C : ControlFlow.Certificate ι) (start : Nat) (inputs : List (List ι))
    (codes : CodeEntry ι → Bool := fun _ => false) :
    CertificateProducer.accept (reassign G η) R P claims C start inputs codes =
      CertificateProducer.accept G R P claims C start inputs codes := by
  simp only [CertificateProducer.accept, checkEntry_reassign]

/-- **Parametricity.** Accepted evidence is safe at every assignment of the
graph's parameter rows: every input environment meeting the inputs read at
`η` runs safely to a result of the result type read at `η`. -/
theorem accepted_at {G : NormalGraph ι} {R P claims C start inputs}
    {codes : CodeEntry ι → Bool}
    (hc : CertificateProducer.accept G R P claims C start inputs codes = true)
    (η : MixedAssignment ι) (n W h ρ)
    (he : EnvOk (reassign G η) inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h)
    (hcodes : CodesSound (reassign G η) codes := by exact Verification.Model.ProgramCertificates.codesSound_none _) :
    SafeGraph P (meaning (reassign G η) R) n W h (.at start ρ) :=
  CertificateProducer.accepted_from_inputs ((accept_reassign G η R P claims C start inputs codes).trans hc) n W h ρ he hw hh hcodes

#print axioms accept_reassign
#print axioms accepted_at

end Verification.Model.Parametricity
