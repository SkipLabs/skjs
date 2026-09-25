import Verification.Model.Tests.CallableGraphTests

/-! Effectful initialization and invocation share the ordinary left-to-right
machine. Code creation does not run the body or skip initializer effects. -/
namespace Verification.Model.CallableOrderTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ProgramCertificates
open CertificateProducer ControlFlow RequestJson HeapExpressionRules

private def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.refs [(valueField, [1])] [] []],[.callable [(valueField, [1])] [] [] []],
   [.callable [(valueField, [1])] [] [([5],[[0]],[1])] []],[.top],[.undef]]
private def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
private def labels := List.range types.length
-- The initializer writes true, allocates an intermediate object, and returns
-- false for the new function's bag. Its invocation body reads the captured bag,
-- past its parameter and receiver.
private def initial : Tm := .letE (.write (.var 0) .tru) (.letE (.alloc .tru) .fls)
private def callee : Tm := .attach (.read (.var 2)) initial
private def argument : Tm := .letE (.write (.var 0) .fls) .nul
private def program (callable : Bool) : Program :=
  [⟨if callable then .attach (.var 0) .fls else .alloc .fls,.bind 1,none⟩,
   ⟨.app callee argument,.ret,none⟩]
private def claims : List (PointClaim Nat) := [⟨[],[2,3]⟩,⟨[[2,3]],[1]⟩]
private def request (callable : Bool) : Request := ⟨types,program callable,claims,[1],0,[], []⟩
#guard [false,true].all fun callable => match (do
    let r := Lean.toJson (request callable)
    let response ← produceJson r 12
    verifyJson r response) with
  | .ok _ => true | .error _ => false

-- An effectful initializer cannot use the allocation/creation shortcuts to
-- retain the pre-initialization false fact about the captured cell.
private def pool := vocabulary G labels claims []
private def creation : Sequent Nat := ⟨[[2,3]],callee,[4]⟩
private def evidence : Evidence Nat :=
  (expression G pool 12 creation.context creation.term creation.type).getD (.node creation .nul [])
private def knowledge : HeapKnowledge.Knowledge := ⟨[⟨0,[.fls],valueField⟩],[],[]⟩
#guard checkTree G evidence
#guard allocationSlot callee == none
#guard checkStep G creation knowledge (.allocated evidence) == none
#guard checkStep G creation knowledge (.created evidence) == none
#guard checkStep G creation knowledge (.pure evidence) == none
#guard checkStep G creation knowledge (.ordinary evidence) == some (ordinaryOutput knowledge)

/-- Initializer write and intermediate allocation precede function allocation;
argument write then precedes beta and the body read. The three cells are the
captured bag, the initializer's object, and the newly allocated callable bag. -/
theorem returns_false (callable : Bool) : Execution (program callable) 14 []
    (.at 0 (fun _ => .nul)) [.fls,.tru,.fls] (.done .fls) := by
  cases callable <;>
    repeat first
      | exact Execution.refl
      | apply Execution.next (.enter rfl)
      | apply Execution.next (.expr (.makeV rfl))
      | apply Execution.next (.expr (.appL (.makeC (.letC (.writeV rfl (by decide))))))
      | apply Execution.next (.expr (.appL (.makeC (.letV rfl))))
      | apply Execution.next (.expr (.appL (.makeC (.letC (.makeV rfl)))))
      | apply Execution.next (.expr (.appL (.makeV rfl)))
      | apply Execution.next (.expr (.appR rfl (.letC (.writeV rfl (by decide)))))
      | apply Execution.next (.expr (.appR rfl (.letV rfl)))
      | apply Execution.next (.expr (.beta rfl))
      | apply Execution.next (.expr (.readV rfl))
      | apply Execution.next (.bind rfl)
      | apply Execution.next (.ret rfl)

/-- A stuck initializer prevents both outer allocation and argument effects. -/
theorem initializer_blocks_argument {h h' t'} :
    ¬ Step h (.app (.attach .nul (.app .nul .nul))
      (.write (.obj 0 .absent) .fls)) h' t' := by
  intro step
  cases step with
  | callL step =>
    cases step with
    | @makeArg _ _ _ i _ _ a _ hg _ step =>
      cases i with
      | zero => simp at hg; subst a; exact stuck_no_step step
      | succ i => simp at hg
    | makeFields hv _ => have h := hv (.app .nul .nul) (by simp); simp [isVal] at h
  | callRecv hv _ => simp [isVal] at hv
  | callArg hv _ _ _ _ => simp [isVal] at hv
  | callSpread hv _ _ _ _ => simp [isVal] at hv

/-- Even a discarded extra argument must finish: a stuck second actual blocks
both a later argument write and the unary callee's mutating body. -/
theorem argument_blocks_body {h h' t'} :
    ¬ Step h (.call (.fn 1 (.write (.obj 0 .absent) .tru))
      [.tru, .app .nul .nul, .write (.obj 0 .absent) .fls]) h' t' := by
  intro step
  rcases CallArguments.call_step_iff.mp step with ⟨frame, hp, _⟩ | ⟨_, hi⟩
  · cases hp with
    | callee hs => exact obj_no_step hs
    | recv _ hs => exact value_no_step rfl hs
    | args _ _ hs =>
      cases hs with
      | head hs => exact tru_no_step hs
      | tail _ hs =>
        cases hs with
        | head hs => exact stuck_no_step hs
        | tail hv _ => simp [isVal] at hv
    | @splice _ _ _ _ pre post ls vs _ _ he _ _ =>
      have hm : Tm.spread (.arr ls) ∈ pre ++ .spread (.arr ls) :: post := by simp
      rw [← he] at hm
      simp at hm
  · cases hi with
    | closure _ hv => simp [CallArguments.Values, isVal] at hv

#print axioms initializer_blocks_argument
#print axioms argument_blocks_body
#print axioms returns_false
end Verification.Model.CallableOrderTests
