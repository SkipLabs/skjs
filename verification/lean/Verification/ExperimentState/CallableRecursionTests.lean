import Verification.ExperimentState.CallableGraphTests

/-! A recursive invocation is tied through an allocated cell, rather than a
runtime identity embedded in source syntax. Safety permits this infinite run. -/
namespace Verification.ExperimentState.CallableRecursionTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ControlFlow
open CertificateProducer RequestJson ProgramCertificates

private def types : List (List (Clause (List Nat))) :=
  [[.nul],[.arrs [([0],[0])]], [.refs [0,1] []]]
private def G : NormalGraph Nat := fun i => types[i]?.getD []
private def labels := List.range types.length
private def dispatch : Tm := .ite (.test .isFun (.var 0)) (.app (.var 0) .nul) .nul
private def body : Tm := .letE (.read (.var 1)) dispatch
private def program : Program :=
  [⟨.alloc .nul,.bind 1⟩,
   ⟨.funE body,.bind 2⟩,
   ⟨.write (.var 1) (.var 0),.effect 3⟩,
   ⟨.app (.var 0) .nul,.ret⟩]
private def claims : List (PointClaim Nat) :=
  [⟨[],[2]⟩,⟨[[2]],[1]⟩,⟨[[1],[2]],[0]⟩,⟨[[1],[2]],[0]⟩]
private def request : Request := ⟨types,program,claims,[0],0,[]⟩
-- Keep the small checked witness explicit: the kernel validates evidence,
-- while the separate JSON regression exercises automatic proof search.
private def node (Γ : List (Ty Nat)) (t : Tm) (A : Ty Nat) (r : Rule Nat)
    (ps : List (Evidence Nat) := []) : Evidence Nat := .node ⟨Γ,t,A⟩ r ps
private def readEvidence : Evidence Nat :=
  node [[0],[2]] (.read (.var 1)) [0,1] .read [node [[0],[2]] (.var 1) [2] .var]
private def nullBranch : Evidence Nat :=
  node [[0],[0],[2]] dispatch [0] .ifFalse [node [[0],[0],[2]] .nul [0] .nul]
private def callBranch : Evidence Nat :=
  node [[1],[0],[2]] dispatch [0] .ifTrue
    [node [[1],[0],[2]] (.app (.var 0) .nul) [0] .app
      [node [[1],[0],[2]] (.var 0) [1] .var, node [[1],[0],[2]] .nul [0] .nul]]
private def closureEvidence : Evidence Nat :=
  node [[2]] (.funE body) [1] .funE
    [node [[0],[2]] body [0] .letE
      [readEvidence,node [[0,1],[0],[2]] dispatch [0] (.unionVar 0) [nullBranch,callBranch]]]
private def certificate : ControlFlow.Certificate Nat :=
  [{expression := node [] (.alloc .nul) [2] .alloc
      [node [] .nul [0,1] (.sub .subset) [node [] .nul [0] .nul]], edges := [[.subset]]},
   {expression := closureEvidence, edges := [[.subset,.subset]]},
   {expression := node [[1],[2]] (.write (.var 1) (.var 0)) [0] .write
      [node [[1],[2]] (.var 1) [2] .var,
       node [[1],[2]] (.var 0) [0,1] (.sub .subset) [node [[1],[2]] (.var 0) [1] .var]],
    edges := [[.subset,.subset]]},
   {expression := node [[1],[2]] (.app (.var 0) .nul) [0] .app
      [node [[1],[2]] (.var 0) [1] .var,node [[1],[2]] .nul [0] .nul], edges := []}]

theorem checked : checkClosed G [0] program certificate 0 = true := by cbv
#guard match (do
    let response ← produceJson (Lean.toJson request) 10
    verifyJson (Lean.toJson request) response) with
  | .ok _ => true | .error _ => false

-- The nullable cell must be guarded on every invocation, and the recursive
-- call's argument must satisfy its contract. Current contents are not captures.
private def pool := vocabulary G labels claims []
#guard !(expression G pool 10 [[2]] (.funE (.app (.read (.var 1)) .nul)) [1]).isSome
#guard !(expression G pool 10 [[2]]
  (.funE (.letE (.read (.var 1))
    (.ite (.test .isFun (.var 0)) (.app (.var 0) .tru) .nul))) [1]).isSome

private def cell : Tm := .obj 0 .absent
private def fn : Tm := .fn 1 (.letE (.read cell) dispatch)
private def loopHeap : Heap := [fn,.nul]
private def loopState : State :=
  .eval (.app fn .nul) (push fn (push cell (fun _ => .nul))) .ret

/-- Every recursive round pays beta, a heap read, a binding, a tag test, and
branch selection. It returns to precisely the same allocated state. -/
theorem cycles (n : Nat) : Execution program (5*n) loopHeap loopState loopHeap loopState := by
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
theorem from_entry (n : Nat) : Execution program (5*n+10) []
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
    (run : Execution program k [] (.at 0 (fun _ => .nul)) h (.done v)) : False := by
  have bound := terminal_bound run (fun _ _ step => by cases step) (from_entry k)
  omega

theorem safe (n : Nat) : SafeGraph program (meaning G [0]) n (ofList []) []
    (.at 0 (fun _ => .nul)) := accepted_closed_safe checked n

theorem coherent {k h s} (run : Execution program k [] (.at 0 (fun _ => .nul)) h s) :
    ∃ D, ObjectCoherence.HeapOk D h ∧ GraphCoherence.StateCoherent D s :=
  GraphCoherence.accepted_closed_coherent checked run

#print axioms checked
#print axioms cycles
#print axioms from_entry
#print axioms never_returns
#print axioms safe
#print axioms coherent
end Verification.ExperimentState.CallableRecursionTests
