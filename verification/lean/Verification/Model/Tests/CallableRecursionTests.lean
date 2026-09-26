import Verification.Model.Tests.CallableGraphTests
import Verification.Model.Tests.GraphCodeFixtures

/-! A recursive invocation is tied through an allocated cell, rather than a
runtime identity embedded in source syntax. Safety permits this infinite run. -/
namespace Verification.Model.CallableRecursionTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ControlFlow
open CertificateProducer RequestJson ProgramCertificates GraphCodeFixtures

private def types : List (List (Clause (List Nat))) :=
  [[.nul],[.arrs [([3],[[0]],[0])] []], [.refs [(valueField, [0,1])] [] []], [.undef]]
private def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
private def labels := List.range types.length
private def dispatch : Tm := .ite (.test .isFun (.var 0)) (.app (.var 0) .nul) .nul
/-- The body reads the captured cell, past its parameter and receiver. -/
private def body : Tm := .letE (.read (.var 2)) dispatch
private def program (body : Tm) : Program :=
  [⟨.alloc .nul,.bind 1,none⟩,
   ⟨.make (oneNode 1 body 1) .nul,.bind 2,none⟩,
   ⟨.write (.var 1) (.var 0),.effect 3,none⟩,
   ⟨.app (.var 0) .nul,.ret,none⟩]
private def claims : List (PointClaim Nat) :=
  [⟨[],[2]⟩,⟨[[2]],[1]⟩,⟨[[1],[2]],[0]⟩,⟨[[1],[2]],[0]⟩]
private def request (body : Tm) : Request :=
  ⟨types,program body,claims,[0],0,[],oneNodeCodes 1 body [[2]] [([3],[[0]],[0])]⟩
#guard ok (roundtrip (request body))

-- The nullable cell must be guarded on every invocation, and the recursive
-- call's argument must satisfy its contract. Current contents are not captures.
#guard !ok (roundtrip (request (.app (.read (.var 2)) .nul)))
#guard !ok (roundtrip (request (.letE (.read (.var 2))
  (.ite (.test .isFun (.var 0)) (.app (.var 0) .tru) .nul))))

/-- The same program with the code as a term, run by the machine. -/
private def executed : ControlFlow.Program :=
  [⟨.alloc .nul,.bind 1,none⟩,
   ⟨.funE body,.bind 2,none⟩,
   ⟨.write (.var 1) (.var 0),.effect 3,none⟩,
   ⟨.app (.var 0) .nul,.ret,none⟩]

private def cell : Tm := .obj 0 .absent
private def fn : Tm := .fn 1 (.letE (.read cell) dispatch)
private def loopHeap : Heap := [fn,.nul]
private def loopState : State :=
  .eval (.app fn .nul) (push fn (push cell (fun _ => .nul))) .ret none

/-- Every recursive round pays beta, a heap read, a binding, a tag test, and
branch selection. It returns to precisely the same allocated state. -/
theorem cycles (n : Nat) : Execution executed (5*n) loopHeap loopState loopHeap loopState := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    rw [Nat.mul_succ]
    apply Execution.next (.expr (.beta rfl))
    apply Execution.next (.expr (.letC (.readV rfl)))
    apply Execution.next (.expr (.letV rfl))
    apply Execution.next (.expr (.iteC (.testV rfl)))
    apply Execution.next (.expr .iteT)
    exact ih

/-- Source allocation and the self-write reach that cycle from the empty heap.
No special recursion rule or preexisting runtime identity is assumed. -/
theorem from_entry (n : Nat) : Execution executed (5*n+10) []
    (.at 0 (fun _ => .nul)) loopHeap loopState := by
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.makeV rfl))
  apply Execution.next (.bind rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.makeV rfl))
  apply Execution.next (.bind rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.writeV rfl (by decide)))
  apply Execution.next (.effect rfl)
  apply Execution.next (.enter rfl)
  exact cycles n

private theorem terminal_bound {P n m h s h' s' h'' s''}
    (a : Execution P n h s h' s')
    (terminal : ∀ hnext snext, ¬ Transition P h' s' hnext snext)
    (b : Execution P m h s h'' s'') : m ≤ n := by
  induction a generalizing m h'' s'' with
  | refl =>
    cases b with
    | refl => exact Nat.le_refl _
    | next step _ => exact False.elim (terminal _ _ step)
  | next step rest ih =>
    cases b with
    | refl => exact Nat.zero_le _
    | next step' rest' =>
      obtain ⟨rfl,rfl⟩ := Transition.det step step'
      exact Nat.succ_le_succ (ih terminal rest')

/-- Determinism and arbitrarily long cycles rule out every returning run. -/
theorem never_returns {k h v}
    (run : Execution executed k [] (.at 0 (fun _ => .nul)) h (.done v)) : False := by
  have bound := terminal_bound run (fun _ _ step => by cases step) (from_entry k)
  omega

#print axioms cycles
#print axioms from_entry
#print axioms never_returns
end Verification.Model.CallableRecursionTests
