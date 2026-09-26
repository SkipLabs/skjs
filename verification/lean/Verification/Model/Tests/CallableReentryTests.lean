import Verification.Model.Tests.CallableGraphTests
import Verification.Model.Tests.GraphCodeFixtures

/-! Higher-order reentry through a callback: the outer call saves a bag read,
then its callback mutates that bag and invokes the same function again. -/
namespace Verification.Model.CallableReentryTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ControlFlow
open CertificateProducer RequestJson GraphCodeFixtures

private def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.refs [(valueField, [1])] [] []],[.callable [(valueField, [1])] [] [] []],
   [.arrs [([7],[[0]],[1])] []], [.arrs [([7],[[4]],[1])] []], [.boolLit false], [.top], [.undef]]
private def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
private def labels := List.range types.length

-- At entry: receiver, callback, captured bag. The two lets save a read, then a
-- callback result. Returning the saved read and rereading the bag are different
-- programs.
private def body (fresh : Bool) : Tm :=
  .letE (.read (.var 2))
    (.letE (.app (.var 2) .nul) (if fresh then .read (.var 4) else .var 1))
-- At entry: receiver, null argument, captured function, captured bag. The
-- nested callback returns false and performs no reentry, so the complete
-- invocation terminates.
private def callback : Tm :=
  .letE (.write (.var 3) .tru) (.app (.var 3) (.make (oneNode 1 .fls 0) .nul))
private def program (callable fresh : Bool) : Program :=
  [⟨if callable then .makeAt (oneNode 1 (.var 1) 0) [valueField] [.fls] else .alloc .fls,.bind 1,none⟩,
   ⟨.make (oneNode 1 (body fresh) 1) .nul,.bind 2,none⟩,
   ⟨.make (oneNode 1 callback 2) .nul,.bind 3,none⟩,
   ⟨.app (.var 1) (.var 0),.ret,none⟩]
private def claims : List (PointClaim Nat) :=
  [⟨[],[2,3]⟩,⟨[[2,3]],[5]⟩,⟨[[5],[2,3]],[4]⟩,⟨[[4],[5],[2,3]],[1]⟩]
/-- The codes: the reentrant function's, the callback's, and the inner
callback's, created inside the callback's code and checked before it. -/
private def codes (fresh : Bool) : List CodeRequest :=
  oneNodeCodes 1 .fls [] [([7],[[0]],[1])] ++
  oneNodeCodes 1 (body fresh) [[2,3]] [([7],[[4]],[1])] ++
  oneNodeCodes 1 callback [[5],[2,3]] [([7],[[0]],[1])]
private def request (callable fresh : Bool) : Request :=
  ⟨types,program callable fresh,claims,[1],0,[],codes fresh⟩

#guard [false,true].all fun callable => [false,true].all fun fresh =>
  ok (roundtrip (request callable fresh) 12)

-- Neither an entry-time read nor the current heap becomes a permanent false
-- result contract for the function; every invocation checks only the invariant.
private def badRequest (fresh : Bool) : Request :=
  ⟨RequestJson.rows (types ++ [[Clause.arrs [([7],[[4]],[6])] []]]),
   [⟨.alloc .fls,.bind 1,none⟩, ⟨.make (oneNode 1 (body fresh) 1) .nul,.bind 2,none⟩, ⟨.nul,.ret,none⟩],
   [⟨[],[2,3]⟩,⟨[[2,3]],[9]⟩,⟨[[9],[2,3]],[0]⟩],[0],0,[],
   oneNodeCodes 1 (body fresh) [[2,3]] [([7],[[4]],[6])]⟩
#guard [false,true].all fun fresh => !ok (roundtrip (badRequest fresh) 12)
-- The reentrant function requires a Boolean-returning callback.
private def nullCallback : Request :=
  ⟨types,[⟨.app (.var 0) (.make (oneNode 1 .nul 0) .nul),.ret,none⟩],[⟨[[5]],[1]⟩],[1],0,[[5]],
   oneNodeCodes 1 .nul [] [([7],[[0]],[1])]⟩
#guard !ok (roundtrip nullCallback)

/-- Reentry writes true while the outer frame retains its saved false value.
The fourth heap cell is allocated for the terminating inner callback. -/
theorem returns_expected (callable fresh : Bool) :
    Execution (program callable fresh) (if fresh then 34 else 32) []
      (.at 0 (fun _ => .nul)) [.tru,.nul,.nul,.nul]
      (.done (if fresh then .tru else .fls)) := by
  cases callable <;> cases fresh <;> run_machine

#print axioms returns_expected
end Verification.Model.CallableReentryTests
