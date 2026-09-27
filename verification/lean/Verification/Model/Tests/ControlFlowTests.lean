import Verification.Model.Programs.ControlFlow
import Verification.Model.Tests.ProgramCertificateTests
import Verification.Model.Tests.GraphCodeFixtures

set_option maxHeartbeats 3200000

namespace Verification.Model.ControlFlowTests
open ProgramTyping ProgramTypingTests ProgramCertificates ControlFlow

private def leaf (Γ : List (Ty (Fin 7))) (t : Tm) (A : Ty (Fin 7)) (r : Rule (Fin 7)) : Evidence (Fin 7) :=
  .node ⟨Γ,t,A⟩ r []

def callCaptured : Tm := .app (.var 0) .nul

/-- The callee, the `undefined` receiver at label 6, the actual. -/
def callEvidence : Evidence (Fin 7) := .node ⟨[[3],[2]],callCaptured,[1]⟩ (.app .unrestricted)
  [leaf [[3],[2]] (.var 0) [3] .var, leaf [[3],[2]] .undef [6] .undef, leaf [[3],[2]] .nul [0] .nul]

/-- The dispatching closure's graph code: one node, run from the frame of the
receiver, the parameter, then the captured cell. -/
def dispatchCode : CallCode :=
  .graph 1 [.ite (.test .isNul (.var 1)) (.read (.var 2)) .nul] [(.ret, none)] 0 [.var 0]

/-- The same closure survives a write through the original reference. Node 2
is reached after closure creation and again through the back edge from node 3. -/
def loop : Program :=
  [⟨.alloc .tru, .bind 1,none⟩,
   ⟨.make dispatchCode .nul, .bind 2,none⟩,
   ⟨callCaptured, .branch 3 4,none⟩,
   ⟨.write (.var 1) .fls, .effect 2,none⟩,
   ⟨callCaptured, .ret,none⟩]

/-- Every code admitted: whether the code meets its signatures is its table's
question, not its creation's. -/
private def admitted : CodeEntry (Fin 7) → Bool := fun _ => true

def loopEvidence : ControlFlow.Certificate (Fin 7) :=
  [{expression := .node ⟨[], .alloc .tru, [2]⟩ .alloc [leaf [] .tru [1] .tru], edges :=  [[.subset]]},
   {expression := .node ⟨[[2]], .make dispatchCode .nul, [3]⟩ (.funGraph []) [leaf [[2]] (.var 0) [2] .var],
    edges :=  [[.subset,.subset]]},
   {expression := callEvidence, edges :=  [[.subset,.subset],[.subset,.subset]]},
   {expression := .node ⟨[[3],[2]], .write (.var 1) .fls, [0]⟩ .write
     [leaf [[3],[2]] (.var 1) [2] .var, leaf [[3],[2]] .fls [1] .fls], edges :=  [[.subset,.subset]]},
   {expression := callEvidence, edges :=  []}]

#guard checkEntry G [1] loop loopEvidence 0 [] admitted
-- The creation names code the table must hold.
#guard !checkClosed G [1] loop loopEvidence 0

/-- The trace actually traverses the back edge, then returns the changed value.
The global safety proof is independent of this terminating example's trace. -/
theorem loop_returns_false : Execution loop 33 [] (.at 0 (fun _ => .nul)) [.fls,.nul] (.done .fls) := by
  run_machine

-- Both predecessors justify the supplied union at the shared node 3.
def diamond : Program :=
  [⟨.tru, .branch 1 2,none⟩, ⟨.nul, .bind 3,none⟩, ⟨.fls, .bind 3,none⟩, ⟨.var 0, .ret,none⟩]
def diamondEvidence : ControlFlow.Certificate (Fin 7) :=
  [{expression := leaf [] .tru [1] .tru, edges :=  [[],[]]},
   {expression := leaf [] .nul [0] .nul, edges :=  [[.subset]]},
   {expression := leaf [] .fls [1] .fls, edges :=  [[.subset]]},
   {expression := leaf [[0,1]] (.var 0) [0,1] .var, edges :=  []}]
#guard checkClosed G [0,1] diamond diamondEvidence 0

-- The false edge is still checked when the condition is literally true.
#guard !(checkClosed G [0,1] (diamond.set 0 ⟨.tru, .branch 1 99,none⟩) diamondEvidence 0)
#guard !(checkClosed G [0,1] diamond
  (diamondEvidence.set 0 {expression := leaf [] .tru [1] .tru, edges :=  [[]]}) 0)
-- Narrowing the supplied merge claim rejects the boolean predecessor.
#guard !(checkClosed G [0] diamond
  (diamondEvidence.set 3 {expression := leaf [[0]] (.var 0) [0] .var, edges :=  []}) 0)
-- Omitted/extra node evidence, changed code and invalid entry points fail.
#guard !(checkEntry G [1] loop loopEvidence.tail 0 [] admitted)
#guard !(checkEntry G [1] loop (loopEvidence ++ loopEvidence) 0 [] admitted)
#guard !(checkEntry G [1] (loop.set 3 ⟨.write (.var 1) .nul, .effect 2,none⟩) loopEvidence 0 [] admitted)
#guard !(checkEntry G [1] loop loopEvidence 99 [] admitted)
#guard !(checkEntry G [1] loop loopEvidence 1 [] admitted)
#guard !(checkClosed G [1] [] [] 0)

-- A genuinely nonterminating cycle is accepted without a return requirement.
def forever : Program := [⟨.nul, .effect 0,none⟩]
def foreverEvidence : ControlFlow.Certificate (Fin 7) := [{expression := leaf [] .nul [0] .nul, edges :=  [[]]}]
#guard checkClosed G [] forever foreverEvidence 0

#print axioms loop_returns_false
end Verification.Model.ControlFlowTests
