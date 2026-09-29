import Verification.Model.Tests.CallableGraphTests
import Verification.Model.Tests.GraphCodeFixtures

/-! The same heap evidence rules track callable and plain bags. Creating code
with an effect does not execute that effect; invoking it remains ordinary and
invalidates current-content facts. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

namespace Verification.Model.CallableEffectTests
open ProgramTyping ProgramCertificates PositiveGraphs PositiveRules HeapExpressionRules
open ControlFlow CertificateProducer RequestJson

/-- Labels 9 and 10 extend the shared table; label 7 there is unknown, every
signature's receiver. -/
private def types := CallableGraphTests.types ++
  [[PositiveNormalization.Clause.boolLit false], [.callable [(valueField, [1])] [] [⟨[7], [[0]], [0], .unrestricted⟩] []]]
private def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
private def labels := List.range types.length
private def pool := vocabulary G labels [] [[1],[2],[5],[10]]
private def k : HeapKnowledge.Knowledge := ⟨[⟨1,[.fls],valueField⟩],[⟨0,[.tru],valueField⟩],[]⟩
/-- The code writes the captured cell, its frame's slot 2, past its receiver
and parameter. -/
private def writer : CallCode := .graph 1 [.write (.var 2) .tru] [(.ret, none)] 0 [.var 1]
private def creation : Sequent Nat :=
  ⟨[[1],[5]],.makeAt writer [valueField] [.var 0],[10]⟩
private def proof (j : Sequent Nat) : Evidence Nat :=
  (expression G pool 8 j.context j.term j.type).getD (.node j .nul [])
/-- Every code admitted: whether the code meets its signature is the unit's
code table's question, not the creation's. -/
private def admitted : CodeEntry Nat → Bool := fun _ => true

-- The potentially mutating code is not run by creation. Both the fresh bag's
-- initial contents and the old cell's false contents survive.
#guard checkTree G (proof creation) admitted
#guard checkStep G creation k (.allocated (proof creation)) admitted ==
  some (allocOutput k [(valueField, [.tru])] (contractFields G creation.context))
#guard (allocOutput k [(valueField, [.tru])]).cells == [⟨0,[.tru],valueField⟩,⟨2,[.fls],valueField⟩]
#guard checkStep G {creation with term := .alloc (.var 0)} k
  (.allocated (proof creation)) admitted == none
#guard checkStep G {creation with term := .makeAt writer [valueField] [.nul]} k
  (.allocated (proof creation)) admitted == none
#guard allocationSlot (.makeAt writer [valueField] [.nul]) == none

-- Empty overloads cannot hide out-of-scope captures behind allocation evidence.
private def emptyG : NormalGraph Nat := .ofRows fun i => if i == 11 then [.callable [(valueField, [1])] [] [] []] else G i
private def escaped : Sequent Nat :=
  ⟨[[1]],.makeAt (.graph 1 [] [] 0 [.var 3]) [valueField] [.var 0],[11]⟩
private def escapedProof : Evidence Nat := .node escaped (.callableGraph [])
  [.node ⟨[[1]],.var 0,[1]⟩ .var [], .node ⟨[[1]],.var 3,[1]⟩ .var []]
#guard !checkTree emptyG escapedProof admitted
#guard checkStep emptyG escaped k (.allocated escapedProof) admitted == none

-- A typed read needs no transient contents fact. Its link records the same
-- callable value; a plain-reference view has no bag operand.
private def readClaim : Sequent Nat := ⟨[[2]],.read (.var 0),[1]⟩
#guard checkStep G readClaim ⟨[],[],[]⟩ (.typedRead 0 (proof readClaim)) ==
  some (readFrame ⟨[],[],[]⟩ 0 valueField)
#guard bagOperand (expand G [3]) == none

-- Producer selection uses the maintained allocation/read evidence constructors.
#guard match expressionEffect G pool 8 creation k [] [] admitted with
  | some (_, .allocated _, out) => out == allocOutput k [(valueField, [.tru])] (contractFields G creation.context)
  | _ => false
#guard match expressionEffect G pool 8 readClaim ⟨[],[],[]⟩ [] [] with
  | some (_, .typedRead 0 _, out) => out == readFrame ⟨[],[],[]⟩ 0 valueField
  | _ => false

/-- The graph requires a precise false return even though the bag and its read
have Boolean contracts. A call invalidates cell facts, but keeps the immutable
snapshot of the preceding read. The callable's code returns its parameter. -/
private def program : Program :=
  [⟨.tru,.bind 1,none⟩,
   ⟨.makeAt CallableGraphTests.code [valueField] [.var 0],.bind 2,none⟩,
   ⟨.read (.var 0),.bind 3,none⟩,
   ⟨.fls,.bind 4,none⟩,
   ⟨.write (.var 2) (.var 0),.effect 5,none⟩,
   ⟨.read (.var 2),.bind 6,none⟩,
   ⟨.app (.var 3) .nul,.effect 7,none⟩,
   ⟨.var 0,.ret,none⟩]
private def claims : List (PointClaim Nat) :=
  [⟨[],[1]⟩,⟨[[1]],[2]⟩,⟨[[2],[1]],[1]⟩,⟨[[1],[2],[1]],[1]⟩,
   ⟨[[1],[1],[2],[1]],[0]⟩,⟨[[1],[1],[2],[1]],[1]⟩,
   ⟨[[1],[1],[1],[2],[1]],[0]⟩,⟨[[1],[1],[1],[2],[1]],[9]⟩]
private def request : Request RequestJson.Table Nat := ⟨types,program,claims,[9],0,[],CallableGraphTests.codes⟩
#guard match (do
    let response ← produceJson RequestJson.Table (Lean.toJson request) 10
    verifyJson RequestJson.Table (Lean.toJson request) response) with
  | .ok _ => true | .error _ => false

/-- The precise return is the saved read value; invocation does not erase it. -/
theorem returns_false : Execution program 23 [] (.at 0 (fun _ => .nul)) [.fls] (.done .fls) := by
  run_machine

#print axioms returns_false
end Verification.Model.CallableEffectTests
