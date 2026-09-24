import Verification.Model.Tests.CallableGraphTests

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
  [[PositiveNormalization.Clause.boolLit false], [.callable [(valueField, [1])] [] [([7],[[0]],[0])] []]]
private def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
private def labels := List.range types.length
private def pool := vocabulary G labels [] [[1],[2],[5],[10]]
private def k : HeapKnowledge.Knowledge := ⟨[⟨1,[.fls],valueField⟩],[⟨0,[.tru],valueField⟩],[]⟩
/-- The body writes the captured cell, past its parameter and receiver. -/
private def creation : Sequent Nat :=
  ⟨[[1],[5]],.attach (.write (.var 3) .tru) (.var 0),[10]⟩
private def proof (j : Sequent Nat) : Evidence Nat :=
  (expression G pool 8 j.context j.term j.type).getD (.node j .nul [])

-- The potentially mutating body is not run by creation. Both the fresh bag's
-- initial contents and the old cell's false contents survive.
#guard checkTree G (proof creation)
#guard checkStep G creation k (.allocated (proof creation)) ==
  some (allocOutput k [(valueField, [.tru])] (contractFields G creation.context))
#guard (allocOutput k [(valueField, [.tru])]).cells == [⟨0,[.tru],valueField⟩,⟨2,[.fls],valueField⟩]
#guard checkStep G {creation with term := .alloc (.var 0)} k
  (.allocated (proof creation)) == none
#guard checkStep G {creation with term := .attach .nul (.var 0)} k
  (.allocated (proof creation)) == none
#guard allocationSlot (.attach .nul (.write (.var 1) .tru)) == none

-- Empty overloads cannot hide out-of-scope captures behind allocation evidence.
private def emptyG : NormalGraph Nat := .ofRows fun i => if i == 11 then [.callable [(valueField, [1])] [] [] []] else G i
private def escaped : Sequent Nat := ⟨[[1]],.attach (.var 3) (.var 0),[11]⟩
private def escapedProof : Evidence Nat := .node escaped .makeCallable
  [.node ⟨[[1]],.var 0,[1]⟩ .var []]
#guard checkTree emptyG escapedProof
#guard checkStep emptyG escaped k (.allocated escapedProof) == none

-- A typed read needs no transient contents fact. Its link records the same
-- callable value; neither a plain-reference view nor an invented operand works.
private def readClaim : Sequent Nat := ⟨[[2]],.read (.var 0),[1]⟩
#guard checkStep G readClaim ⟨[],[],[]⟩ (.typedRead 0 [(valueField, [1])] (proof readClaim)) ==
  some (readFrame ⟨[],[],[]⟩ 0 valueField)
#guard checkStep G readClaim ⟨[],[],[]⟩ (.typedRead 0 [(valueField, [0])] (proof readClaim)) == none
#guard bagOperand (expand G [3]) == none

-- Producer selection uses the maintained allocation/read evidence constructors.
#guard match expressionEffect G pool 8 creation k [] [] with
  | some (_, .allocated _, out) => out == allocOutput k [(valueField, [.tru])] (contractFields G creation.context)
  | _ => false
#guard match expressionEffect G pool 8 readClaim ⟨[],[],[]⟩ [] [] with
  | some (_, .typedRead 0 [(valueField, [1])] _, out) => out == readFrame ⟨[],[],[]⟩ 0 valueField
  | _ => false

/-- The graph requires a precise false return even though the bag and its read
have Boolean contracts. A call invalidates cell facts, but keeps the immutable
snapshot of the preceding read. -/
private def program : Program :=
  [⟨.tru,.bind 1⟩,
   ⟨.attach (.var 1) (.var 0),.bind 2⟩,
   ⟨.read (.var 0),.bind 3⟩,
   ⟨.fls,.bind 4⟩,
   ⟨.write (.var 2) (.var 0),.effect 5⟩,
   ⟨.read (.var 2),.bind 6⟩,
   ⟨.app (.var 3) .nul,.effect 7⟩,
   ⟨.var 0,.ret⟩]
private def claims : List (PointClaim Nat) :=
  [⟨[],[1]⟩,⟨[[1]],[2]⟩,⟨[[2],[1]],[1]⟩,⟨[[1],[2],[1]],[1]⟩,
   ⟨[[1],[1],[2],[1]],[0]⟩,⟨[[1],[1],[2],[1]],[1]⟩,
   ⟨[[1],[1],[1],[2],[1]],[0]⟩,⟨[[1],[1],[1],[2],[1]],[9]⟩]
private def request : Request := ⟨types,program,claims,[9],0,[]⟩
private def certificate : ControlFlow.Certificate Nat :=
  match produce G labels 10 [9] program claims 0 with | .ok c => c | .error _ => []

#guard checkClosed G [9] program certificate 0
#guard match (do
    let response ← produceJson (Lean.toJson request) 10
    verifyJson (Lean.toJson request) response) with
  | .ok _ => true | .error _ => false

/-- The precise return is the saved read value; invocation does not erase it. -/
theorem returns_false : Execution program 21 [] (.at 0 (fun _ => .nul)) [.fls] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.readV rfl))
    | apply Execution.next (.expr (.writeV rfl (by decide)))
    | apply Execution.next (.expr (.beta rfl))
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.ret rfl)

#print axioms returns_false
end Verification.Model.CallableEffectTests
