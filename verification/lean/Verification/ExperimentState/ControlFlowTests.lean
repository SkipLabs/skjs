import Verification.ExperimentState.ControlFlow
import Verification.ExperimentState.ProgramCertificateTests

namespace Verification.ExperimentState.ControlFlowTests
open ProgramTyping ProgramTypingTests ProgramCertificates ControlFlow

private def leaf (Γ : List (Ty (Fin 6))) (t : Tm) (A : Ty (Fin 6)) (r : Rule (Fin 6)) : Evidence (Fin 6) :=
  .node ⟨Γ,t,A⟩ r []

def callCaptured : Tm := .app (.var 0) .nul

def callEvidence : Evidence (Fin 6) := .node ⟨[[3],[2]],callCaptured,[1]⟩ .app
  [leaf [[3],[2]] (.var 0) [3] .var, leaf [[3],[2]] .nul [0] .nul]

/-- The same closure survives a write through the original reference. Node 2
is reached after closure creation and again through the back edge from node 3. -/
def loop : Program :=
  [⟨.alloc .tru, .bind 1⟩,
   ⟨dispatch, .bind 2⟩,
   ⟨callCaptured, .branch 3 4⟩,
   ⟨.write (.var 1) .fls, .effect 2⟩,
   ⟨callCaptured, .ret⟩]

def loopEvidence : ControlFlow.Certificate (Fin 6) :=
  [{expression := .node ⟨[], .alloc .tru, [2]⟩ .alloc [leaf [] .tru [1] .tru], edges :=  [[.subset]]},
   {expression := ProgramCertificateTests.dispatchEvidence, edges :=  [[.subset,.subset]]},
   {expression := callEvidence, edges :=  [[.subset,.subset],[.subset,.subset]]},
   {expression := .node ⟨[[3],[2]], .write (.var 1) .fls, [0]⟩ .write
     [leaf [[3],[2]] (.var 1) [2] .var, leaf [[3],[2]] .fls [1] .fls], edges :=  [[.subset,.subset]]},
   {expression := callEvidence, edges :=  []}]

#guard checkClosed G [1] loop loopEvidence 0

theorem loop_checked : checkClosed G [1] loop loopEvidence 0 = true := by cbv

theorem loop_safe (n : Nat) : SafeGraph loop (PositiveRules.meaning G [1]) n
    (ofList []) [] (.at 0 (fun _ => .nul)) := accepted_closed_safe loop_checked n

/-- The trace actually traverses the back edge, then returns the changed value.
The global safety proof is independent of this terminating example's trace. -/
theorem loop_returns_false : Execution loop 27 [] (.at 0 (fun _ => .nul)) [.fls,.nul] (.done .fls) := by
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.allocV rfl))
  apply Execution.next (.bind rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.attachV rfl))
  apply Execution.next (.bind rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.beta rfl))
  apply Execution.next (.expr (.iteC (.testV rfl)))
  apply Execution.next (.expr .iteT)
  apply Execution.next (.expr (.readV rfl))
  apply Execution.next .yes
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.writeV rfl (by decide)))
  apply Execution.next (.effect rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.beta rfl))
  apply Execution.next (.expr (.iteC (.testV rfl)))
  apply Execution.next (.expr .iteT)
  apply Execution.next (.expr (.readV rfl))
  apply Execution.next .no
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.beta rfl))
  apply Execution.next (.expr (.iteC (.testV rfl)))
  apply Execution.next (.expr .iteT)
  apply Execution.next (.expr (.readV rfl))
  apply Execution.next (.ret rfl)
  exact .refl

-- Both predecessors justify the supplied union at the shared node 3.
def diamond : Program :=
  [⟨.tru, .branch 1 2⟩, ⟨.nul, .bind 3⟩, ⟨.fls, .bind 3⟩, ⟨.var 0, .ret⟩]
def diamondEvidence : ControlFlow.Certificate (Fin 6) :=
  [{expression := leaf [] .tru [1] .tru, edges :=  [[],[]]},
   {expression := leaf [] .nul [0] .nul, edges :=  [[.subset]]},
   {expression := leaf [] .fls [1] .fls, edges :=  [[.subset]]},
   {expression := leaf [[0,1]] (.var 0) [0,1] .var, edges :=  []}]
#guard checkClosed G [0,1] diamond diamondEvidence 0

-- The false edge is still checked when the condition is literally true.
#guard !(checkClosed G [0,1] (diamond.set 0 ⟨.tru, .branch 1 99⟩) diamondEvidence 0)
#guard !(checkClosed G [0,1] diamond
  (diamondEvidence.set 0 {expression := leaf [] .tru [1] .tru, edges :=  [[]]}) 0)
-- Narrowing the supplied merge claim rejects the boolean predecessor.
#guard !(checkClosed G [0] diamond
  (diamondEvidence.set 3 {expression := leaf [[0]] (.var 0) [0] .var, edges :=  []}) 0)
-- Omitted/extra node evidence, changed code and invalid entry points fail.
#guard !(checkClosed G [1] loop loopEvidence.tail 0)
#guard !(checkClosed G [1] loop (loopEvidence ++ loopEvidence) 0)
#guard !(checkClosed G [1] (loop.set 3 ⟨.write (.var 1) .nul, .effect 2⟩) loopEvidence 0)
#guard !(checkClosed G [1] loop loopEvidence 99)
#guard !(checkClosed G [1] loop loopEvidence 1)
#guard !(checkClosed G [1] [] [] 0)

-- A genuinely nonterminating cycle is accepted without a return requirement.
def forever : Program := [⟨.nul, .effect 0⟩]
def foreverEvidence : ControlFlow.Certificate (Fin 6) := [{expression := leaf [] .nul [0] .nul, edges :=  [[]]}]
theorem forever_safe (n : Nat) : SafeGraph forever (PositiveRules.meaning G []) n
    (ofList []) [] (.at 0 (fun _ => .nul)) :=
  accepted_closed_safe (by cbv : checkClosed G [] forever foreverEvidence 0 = true) n

#print axioms loop_safe
#print axioms loop_returns_false
#print axioms forever_safe
end Verification.ExperimentState.ControlFlowTests
