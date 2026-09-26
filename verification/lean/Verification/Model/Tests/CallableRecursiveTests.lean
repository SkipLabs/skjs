import Verification.Model.Tests.CallableGraphTests
import Verification.Model.Tests.GraphCodeFixtures

/-! Recursive callable bags exercise the existing recursive graph interpretation,
producer, consumer, and machine together. The heap may contain the very callable
whose contract describes that heap cell. -/
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace Verification.Model.CallableRecursiveTests
open Lean PositiveNormalization PositiveGraphs ProgramTyping ControlFlow CertificateProducer RequestJson
open GraphCodeFixtures

-- R = { bag: null | R; call: Boolean → Boolean }. A second label describes
-- the same recursive contract independently, to exercise cyclic subtyping.
private def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.callable [(valueField, [0,2])] [] [([7],[[1]],[1])] []],
   [.callable [(valueField, [0,3])] [] [([7],[[1]],[1])] []],
   [.callable [(valueField, [0,2,1])] [] [([7],[[1]],[1])] []],
   [.arrs [([7],[[2]],[2])] []], [.arrs [([7],[[1]],[0,2])] []], [.top], [.undef]]
private def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
private def labels := List.range types.length
private def pool := vocabulary G labels [] [[0,2],[0,3]]

/-- The callable's identity code and its code requests: empty context. -/
private def identity : Tm := .makeAt (oneNode 1 (.var 1) 0) [valueField] [.nul]
private def identityCodes : List CodeRequest := oneNodeCodes 1 (.var 1) [] [([7],[[1]],[1])]
private def program : Program :=
  [⟨identity,.bind 1,none⟩,
   ⟨.write (.var 0) (.var 0),.effect 2,none⟩,
   ⟨.read (.var 0),.bind 3,none⟩,
   ⟨.ite (.test .isFun (.var 0)) (.app (.var 0) .fls) .tru,.ret,none⟩]
private def claims : List (PointClaim Nat) :=
  [⟨[],[2]⟩,⟨[[2]],[0]⟩,⟨[[2]],[0,2]⟩,⟨[[0,2],[2]],[1]⟩]
private def request : Request := ⟨types,program,claims,[1],0,[],identityCodes⟩
private def certificate : ControlFlow.Certificate Nat :=
  match produce G labels 10 [1] program claims 0 (codes := admitted) with | .ok c => c | .error _ => []

#guard checkEntry G [1] program certificate 0 [] admitted
#guard match (do
    let response ← produceJson (toJson request) 10
    verifyJson (toJson request) response) with
  | .ok _ => true | .error _ => false

-- Independent recursive labels may be equivalent; adding Boolean to the
-- invariant bag is unsafe even though it widens a read result.
#guard (subtype G pool [2] [3]).isSome
#guard (subtype G pool [3] [2]).isSome
#guard !(subtype G pool [2] [4]).isSome
#guard !(expression G pool 10 [[2]] (.write (.var 0) .tru) [0]).isSome
#guard !(expression G pool 10 [[0,2]] (.app (.var 0) .fls) [1]).isSome

-- Recursive callable values can be higher-order arguments and results.
#guard match expression G pool 10 [] (.make (oneNode 1 (.var 1) 0) .nul) [5] with
  | some e => ProgramCertificates.checkTree G e admitted
  | none => false
#guard (expression G pool 10 [[5],[2]] (.app (.var 0) (.var 1)) [2]).isSome

/-- The same program with the code as a term, run by the machine. -/
private def executed : Program := program.set 0 ⟨.attach (.var 1) .nul,.bind 1,none⟩

/-- Reading the cyclic bag returns the same callable; its descriptor still
executes identity code. No recursive unfolding is performed by the machine. -/
theorem returns_false : Execution executed 14 [] (.at 0 (fun _ => .nul))
    [.fn 0 (.var 1)] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.writeV rfl (by decide)))
    | apply Execution.next (.expr (.readV rfl))
    | apply Execution.next (.expr (.iteC (.testV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr (.beta rfl))
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.ret rfl)

/-- The getter captures the callable before its bag contains a callable. Calling
it after the self-write observes the updated heap and returns a callable value. -/
private def getter : Tm := .read (.var 2)
private def capturedProgram : Program :=
  [⟨identity,.bind 1,none⟩,
   ⟨.make (oneNode 1 getter 1) .nul,.bind 2,none⟩,
   ⟨.write (.var 1) (.var 1),.effect 3,none⟩,
   ⟨.app (.var 0) .tru,.bind 4,none⟩,
   ⟨.ite (.test .isFun (.var 0)) (.app (.var 0) .fls) .tru,.ret,none⟩]
private def capturedClaims : List (PointClaim Nat) :=
  [⟨[],[2]⟩,⟨[[2]],[6]⟩,⟨[[6],[2]],[0]⟩,⟨[[6],[2]],[0,2]⟩,
   ⟨[[0,2],[6],[2]],[1]⟩]
private def capturedRequest : Request := ⟨types,capturedProgram,capturedClaims,[1],0,[],
  identityCodes ++ oneNodeCodes 1 getter [[2]] [([7],[[1]],[0,2])]⟩
#guard match (do
    let response ← produceJson (toJson capturedRequest) 10
    verifyJson (toJson capturedRequest) response) with
  | .ok _ => true | .error _ => false

-- The capture does not freeze the initial null bag. Treating the getter as
-- always returning null must fail its ordinary closure-body obligation.
private def nullGetterRequest : Request :=
  ⟨RequestJson.rows (types ++ [[Clause.arrs [([7],[[1]],[0])] []]]),
   [⟨identity,.bind 1,none⟩, ⟨.make (oneNode 1 getter 1) .nul,.bind 2,none⟩, ⟨.nul,.ret,none⟩],
   [⟨[],[2]⟩,⟨[[2]],[9]⟩,⟨[[9],[2]],[0]⟩],[0],0,[],
   identityCodes ++ oneNodeCodes 1 getter [[2]] [([7],[[1]],[0])]⟩
#guard !ok (roundtrip nullGetterRequest)

/-- The same program with the codes as terms, run by the machine. -/
private def capturedExecuted : Program :=
  (capturedProgram.set 0 ⟨.attach (.var 1) .nul,.bind 1,none⟩).set 1 ⟨.funE (.read (.var 2)),.bind 2,none⟩

theorem captured_returns_false : Execution capturedExecuted 18 [] (.at 0 (fun _ => .nul))
    [.fn 0 (.var 1),.nul] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.writeV rfl (by decide)))
    | apply Execution.next (.expr (.readV rfl))
    | apply Execution.next (.expr (.iteC (.testV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr (.beta rfl))
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.ret rfl)

#print axioms captured_returns_false
#print axioms returns_false
end Verification.Model.CallableRecursiveTests
