import Verification.Model.Tests.CallableGraphTests

/-! A closure mutates a captured neutral bag. Invocation invalidates current
contents and read links while preserving immutable snapshots. -/
namespace Verification.Model.CallableMutationTests
open PositiveNormalization PositiveGraphs PositiveRules ProgramTyping ProgramCertificates
open CertificateProducer ControlFlow RequestJson HeapExpressionRules

private def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.refs [(valueField, [1])] [] []],[.callable [(valueField, [1])] [] [] []],
   [.boolLit false],[.arrs [([6],[[0]],[0])] []],[.top],[.undef]]
private def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
private def labels := List.range types.length
private def program (callable fresh : Bool) : Program :=
  [⟨.fls,.bind 1⟩,
   ⟨if callable then .attach (.var 0) (.var 0) else .alloc (.var 0),.bind 2⟩,
   ⟨.read (.var 0),.bind 3⟩,
   ⟨.funE (.write (.var 3) .tru),.bind 4⟩,
   ⟨.app (.var 0) .nul,.effect 5⟩,
   ⟨if fresh then .read (.var 2) else .var 1,.ret⟩]
private def claims (R : List Nat) : List (PointClaim Nat) :=
  [⟨[],[1]⟩,⟨[[1]],[2,3]⟩,⟨[[2,3],[1]],[1]⟩,
   ⟨[[1],[2,3],[1]],[5]⟩,⟨[[5],[1],[2,3],[1]],[0]⟩,
   ⟨[[5],[1],[2,3],[1]],R⟩]
private def request (callable fresh : Bool) (R : List Nat) : Request :=
  ⟨types,program callable fresh,claims R,R,0,[]⟩
private def certificate (callable fresh : Bool) (R : List Nat) : ControlFlow.Certificate Nat :=
  match produce G labels 10 R (program callable fresh) (claims R) 0 with
  | .ok c => c | .error _ => []

-- The saved false value survives a real write, for both allocation descriptors.
-- Fresh reads still have their invariant Boolean type after the call.
#guard [false,true].all fun callable => [false,true].all fun fresh => match (do
    let r := Lean.toJson (request callable fresh (if fresh then [1] else [4]))
    let response ← produceJson r 10
    verifyJson r response) with
  | .ok _ => true | .error _ => false

-- A fresh read cannot reuse the old false fact after the mutating invocation.
#guard [false,true].all fun callable => match
    produceJson (Lean.toJson (request callable true [4])) 10 with
  | .ok _ => false | .error _ => true

-- Ordinary call evidence discards actual nonempty contents/read-link inputs.
-- Forge those stale outputs to ensure the consumer checks the effect frame.
#guard [false,true].all fun callable => Id.run do
  let P := program callable false
  let C := certificate callable false [4]
  let some c := C[4]? | return false
  let some node := P[4]? | return false
  if c.knowledge.cells.isEmpty || !(c.knowledge.links.any fun l => !l.alias) then return false
  if !c.output.cells.isEmpty || !(c.output.links.all fun l => l.alias) then return false
  let shifted := HeapKnowledge.shift c.knowledge
  let staleCells := {c with output := {c.output with cells := shifted.cells}}
  let staleLinks := {c with output := {c.output with links := shifted.links}}
  return checkNode G [4] P C node c &&
    !checkNode G [4] P C node staleCells && !checkNode G [4] P C node staleLinks

/-- The heap really changes to true; a saved immutable value remains false.
Creation of the mutator accounts for the second, null-initialized heap cell. -/
theorem returns_expected (callable fresh : Bool) :
    Execution (program callable fresh) (if fresh then 18 else 17) []
      (.at 0 (fun _ => .nul)) [.tru,.nul] (.done (if fresh then .tru else .fls)) := by
  cases callable <;> cases fresh <;>
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

#print axioms returns_expected
end Verification.Model.CallableMutationTests
