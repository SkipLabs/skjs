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

theorem checkArrow_reassign (table : Table ι) (L : Ops ι)
    (S : List (CallEffects.RestArrow (List ι))) (q : CallEffects.Arrow (List ι)) (cert : ArrowCert ι) :
    checkArrow (reassign G η) table L S q cert = checkArrow G table L S q cert := by
  induction cert generalizing q <;> simp only [checkArrow, *] <;> rfl

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

/-- A scheme's receivers read none of its binders whatever the graph's
assignment: the check follows rows, not the assignment. -/
theorem bindersFree_reassign (bs A : List ι) :
    bindersFree (reassign G η) bs A = bindersFree G bs A := by
  simp only [bindersFree, readsFrom_reassign, freeMapOf_reassign]
  rfl

theorem schemes_reassign (i : ι) : (reassign G η).schemes i = G.schemes i := rfl
theorem params_reassign (i : ι) : (reassign G η).params i = G.params i := rfl
theorem expand_reassign (F : List ι) : expand (reassign G η) F = expand G F := rfl

theorem schemeBinds_reassign (R : List ι → List ι → Prop) (s : SchemeRow ι) (S' : List ι) :
    SchemeBinds (reassign G η) R s S' ↔ SchemeBinds G R s S' := by
  unfold SchemeBinds
  rcases S' with _ | ⟨j, _ | _⟩
  · exact Iff.rfl
  · simp only [schemes_reassign, params_reassign]
    cases G.schemes j <;> exact Iff.rfl
  · exact Iff.rfl

theorem coversByScheme_reassign (R : List ι → List ι → Prop) (self F : List ι)
    (q : MethodMembers.Sig (List ι)) :
    CoversByScheme (reassign G η) R self F q ↔ CoversByScheme G R self F q := by
  unfold CoversByScheme
  rcases F with _ | ⟨i, _ | _⟩
  · exact Iff.rfl
  · simp only [schemes_reassign, params_reassign, bindersFree_reassign, schemeBinds_reassign]
  · exact Iff.rfl

theorem coversByFunction_reassign (R : List ι → List ι → Prop) (self F : List ι)
    (q : MethodMembers.Sig (List ι)) :
    CoversByFunction (reassign G η) R self F q ↔ CoversByFunction G R self F q := by
  unfold CoversByFunction
  rw [expand_reassign]
  split
  · exact Iff.rfl
  · exact coversByScheme_reassign G η R self F q

theorem foundOn_reassign (R : List ι → List ι → Prop) (known : Known ι) (self : List ι)
    (q : MethodMembers.Sig (List ι)) (P : List ι) :
    FoundOn (reassign G η) R known self q P ↔ FoundOn G R known self q P := by
  unfold FoundOn
  exact or_congr Iff.rfl (exists_congr fun F => and_congr Iff.rfl
    (coversByFunction_reassign G η R self F q))

/-- Method coverage along a prototype chain reads the graph's rows only. -/
theorem protoHolds_reassign (R : List ι → List ι → Prop) (known : Known ι) (self : List ι)
    (q : MethodMembers.Sig (List ι)) :
    ∀ d P, ProtoHolds (reassign G η) R known self q d P ↔ ProtoHolds G R known self q d P
  | 0, P => by
    simp only [ProtoHolds]
    exact foundOn_reassign G η R known self q P
  | d + 1, P => by
    simp only [ProtoHolds]
    exact or_congr (foundOn_reassign G η R known self q P) (and_congr Iff.rfl (exists_congr fun P' =>
      and_congr Iff.rfl (protoHolds_reassign R known self q d P')))

theorem coversMethods_reassign (R : List ι → List ι → Prop) (known : Known ι) (self : List ι)
    (fields : List (PropKey × List ι)) (bounds : List KeyBound)
    (source target : List (MethodMembers.Sig (List ι))) :
    CoversMethods (reassign G η) R known self fields bounds source target ↔
      CoversMethods G R known self fields bounds source target := by
  unfold CoversMethods CoversByProto
  refine forall_congr' fun q => imp_congr_right fun _ => or_congr Iff.rfl (or_congr ?_ ?_)
  · exact exists_congr fun f => and_congr Iff.rfl (and_congr Iff.rfl (coversByFunction_reassign G η R self f.2 q))
  · exact and_congr Iff.rfl (exists_congr fun f => and_congr Iff.rfl (and_congr Iff.rfl
      (protoHolds_reassign G η R known self q protoChainDepth f.2)))

set_option maxHeartbeats 1000000 in
theorem coversWith_reassign (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (CallEffects.RestArrow (List ι)) → Ops ι → Prop)
    (self : List ι) (a b : Clause (List ι)) :
    CoversWith (reassign G η) R known arrows self a b ↔ CoversWith G R known arrows self a b := by
  cases a <;> cases b <;> simp only [CoversWith, coversMethods_reassign] <;> exact Iff.rfl

theorem schemeCoversWith_reassign (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (CallEffects.RestArrow (List ι)) → Ops ι → Prop) (i j : ι) :
    SchemeCoversWith (reassign G η) R known arrows i j ↔ SchemeCoversWith G R known arrows i j := by
  unfold SchemeCoversWith
  rw [schemes_reassign, schemes_reassign]
  cases G.schemes i <;> cases G.schemes j
  all_goals first | exact Iff.rfl | simp only [params_reassign, coversWith_reassign]

theorem opaqueWith_reassign (R : List ι → List ι → Prop) (known : Known ι)
    (arrows : Ops ι → List (CallEffects.RestArrow (List ι)) → Ops ι → Prop) (S T : List ι) :
    OpaqueWith (reassign G η) R known arrows S T ↔ OpaqueWith G R known arrows S T := by
  unfold OpaqueWith
  exact forall_congr' fun i => imp_congr_right fun _ => or_congr Iff.rfl (or_congr Iff.rfl
    (or_congr Iff.rfl (or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl
      (schemeCoversWith_reassign G η R known arrows i j)))))

theorem checkClause_reassign (table : Table ι) (known : Known ι) (proofs : PositiveCertificates.Evidence ι)
    (self : List ι) (a b : Clause (List ι)) :
    checkClause (reassign G η) table known proofs self a b = checkClause G table known proofs self a b := by
  have hA : ArrowsChecked (reassign G η) table proofs = ArrowsChecked G table proofs := by
    funext L S M; simp only [ArrowsChecked, checkArrow_reassign]
  unfold checkClause
  apply decide_eq_decide.mpr
  rw [hA]
  exact coversWith_reassign G η _ known _ self a b

theorem checkCore_reassign (known : Known ι) (S T : List ι) (cert : PositiveCertificates.Certificate ι) :
    checkCore (reassign G η) known S T cert = checkCore G known S T cert := by
  have hA : ArrowsChecked (reassign G η) cert.table cert.arrows =
      ArrowsChecked G cert.table cert.arrows := by
    funext L S M; simp only [ArrowsChecked, checkArrow_reassign]
  unfold checkCore
  apply decide_eq_decide.mpr
  simp only [checkClause_reassign, hA, opaqueWith_reassign]
  exact Iff.rfl

theorem boundOk_reassign (binders : List ι) (θs : List (List ι)) (b : ι × List ι)
    (c : Option (PositiveCertificates.Certificate ι)) :
    boundOk (reassign G η) binders θs b c = boundOk G binders θs b c := by
  simp only [boundOk, checkCore_reassign]

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

theorem check_reassign (S T : List ι) (p : Proof ι) :
    PositiveCertificates.checkUsing (reassign G η) (images.reassign η) S T p =
      PositiveCertificates.checkUsing G images S T p := by
  induction p generalizing S T <;>
    simp only [PositiveCertificates.checkUsing, checkCore_reassign, checkInstArrs_reassign,
      checkInst_reassign, *] <;> rfl

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

theorem checkObservedSub_reassign (A B : List ι) (o : Observation) (p : Proof ι) :
    checkObservedSubUsing (reassign G η) (images.reassign η) A B o p =
      checkObservedSubUsing G images A B o p := by
  cases o <;> simp only [checkObservedSubUsing, check_reassign, arraySlice_reassign] <;> rfl

theorem fieldRefinements_reassign (o : Observation) (fields : List (Nat × PropKey)) (A B : List ι)
    (j : Nat) (p : Proof ι) :
    fieldRefinements o fields A B j (reassign G η) (images.reassign η) p =
      fieldRefinements o fields A B j G images p := by
  cases o <;> simp only [fieldRefinements, check_fun_reassign] <;> rfl

theorem optionalRefinements_reassign (o : Observation) (optionals : List (Nat × PropKey)) (A B : List ι)
    (j : Nat) (p : Proof ι) :
    optionalRefinements o optionals A B j (reassign G η) p = optionalRefinements o optionals A B j G p := rfl

theorem checkObserved_reassign (Γ Δ : List (List ι)) (tested : Nat) (o : Observation)
    (m : Mapping) (ps : EdgeEvidence ι) (fields optionals : List (Nat × PropKey)) :
    checkObservedUsing (reassign G η) (images.reassign η) Γ Δ tested o m ps fields optionals =
      checkObservedUsing G images Γ Δ tested o m ps fields optionals := by
  simp only [checkObservedUsing, checkObservedSub_reassign, check_fun_reassign,
    fieldRefinements_reassign, optionalRefinements_reassign]
  rfl

theorem CallProofs_reassign (q : CallEffects.Arrow (List ι)) (c : CallEffects.MethodArrow (List ι))
    (ps : List (Proof ι) × Proof ι) :
    CallProofsUsing (reassign G η) (images.reassign η) q c ps = CallProofsUsing G images q c ps := by
  simp only [CallProofsUsing, check_reassign]

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
  simp only [check_fun_reassign, CallProofs_reassign, graphCodesChecked_reassign,
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

