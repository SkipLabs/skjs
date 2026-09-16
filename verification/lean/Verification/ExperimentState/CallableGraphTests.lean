import Verification.ExperimentState.RequestJson
import Verification.ExperimentState.DirectProof
import Verification.ExperimentState.GraphCoherence

/-! A single allocated value supports overloaded calls and mutable bag access
through the maintained graph producer, consumer, and JSON protocol. -/
namespace Verification.ExperimentState.CallableGraphTests
open Lean PositiveNormalization PositiveGraphs ProgramTyping ControlFlow CertificateProducer RequestJson

private def signatures : List (List (List Nat) × List Nat) := [([[1]],[1]),([[0]],[0])]
def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.callable [(valueField, [1])] [] signatures],[.arrs signatures],
   [.callable [(valueField, [1])] [[(valueField,[1])]] signatures],[.refs [(valueField, [1])] []],[.callable [(valueField, [0,1])] [] signatures]]
def G : NormalGraph Nat := fun i => types[i]?.getD []
def labels := List.range types.length

def program : Program :=
  [⟨.attach (.var 0) .tru,.bind 1⟩,
   ⟨.var 0,.bind 2⟩,
   ⟨.write (.var 1) .fls,.effect 3⟩,
   ⟨.read (.var 0),.bind 4⟩,
   ⟨.app (.var 1) (.var 0),.ret⟩]
def claims : List (PointClaim Nat) :=
  [⟨[],[2]⟩,⟨[[2]],[2]⟩,⟨[[2],[2]],[0]⟩,⟨[[2],[2]],[1]⟩,⟨[[1],[2],[2]],[1]⟩]
def request : Request := ⟨types,program,claims,[1],0,[]⟩
def certificate : ControlFlow.Certificate Nat :=
  match produce G labels 8 [1] program claims 0 with
  | .ok c => c
  | .error _ => []

set_option maxHeartbeats 800000 in
theorem checked : checkClosed G [1] program certificate 0 = true := by cbv

private def ok (x : Except String α) : Bool := match x with | .ok _ => true | .error _ => false
#guard ok (do
  let r ← Json.parse (toJson request).compress
  let c ← produceJson r 8
  verifyJson r (← Json.parse c.compress))

/-- One allocation, then an alias write, bag read, and call on the same identity. -/
theorem returns_false : Execution program 14 [] (.at 0 (fun _ => .nul)) [.fls] (.done .fls) := by
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.makeV rfl))
  apply Execution.next (.bind rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.bind rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.writeV rfl (by decide)))
  apply Execution.next (.effect rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.readV rfl))
  apply Execution.next (.bind rfl)
  apply Execution.next (.enter rfl)
  apply Execution.next (.expr (.beta rfl))
  apply Execution.next (.ret rfl)
  exact .refl

theorem coherent {k h s} (run : Execution program k [] (.at 0 (fun _ => .nul)) h s) :
    ∃ D, ObjectCoherence.HeapOk D h ∧ GraphCoherence.StateCoherent D s :=
  GraphCoherence.accepted_closed_coherent checked run

private def pool := vocabulary G labels claims []
-- Properties may be forgotten for calls; they cannot be widened covariantly or
-- converted to plain-reference shape. Duplicate invariant constraints are safe.
#guard (subtype G pool [2] [3]).isSome
#guard (subtype G pool [2] [4]).isSome
#guard !(subtype G pool [2] [5]).isSome
#guard !(subtype G pool [2] [6]).isSome
#guard !(subtype G pool [3] [2]).isSome

-- Normalization merges property constraints and overloads without allocation.
#guard meet (.callable [(valueField, [1])] [] signatures) (.arrs [([[1]],[1])]) ==
  [.callable [(valueField, [1])] [] (signatures ++ [([[1]],[1])])]
#guard meet (.callable [(valueField, [1])] [] signatures) (.callable [(valueField, [1])] [] signatures) ==
  [.callable [(valueField, [1])] [[(valueField,[1])]] (signatures ++ signatures)]
#guard meet (.refs [(valueField, [1])] []) (.callable [(valueField, [1])] [] signatures) == []

-- Unsafe code, invalid bag writes, and plain-object calls cannot acquire evidence.
#guard !(expression G pool 8 [] (.attach (.app .nul .nul) .tru) [2]).isSome
#guard !(expression G pool 8 [[2]] (.write (.var 0) .nul) [0]).isSome
#guard !(expression G pool 8 [[5]] (.app (.var 0) .tru) [1]).isSome

-- Direct-proof rendering reinstates the argument binder for each overload.
private def creation := expression G pool 8 [] (.attach (.var 0) .tru) [2]
#guard creation.isSome
private def creationPlan : DirectProof.Plan :=
  .rule ⟨[],.attach (.var 0) .tru,[2]⟩ .makeCallable
    [.rule ⟨[],.tru,[1]⟩ .tru [],
     .rule ⟨[[1]],.var 0,[1]⟩ .var [],
     .rule ⟨[[0]],.var 0,[0]⟩ .var []]
#guard match DirectProof.render G pool [] creationPlan with
  | none => false
  | some e => ProgramCertificates.check G (.attach (.var 0) .tru) [2] e

-- Labels in the new clause's bag and arrow operands remain range checked.
#guard !validRequest {request with types := types ++ [[.callable [(valueField, [99])] [] signatures]]}
#guard !validRequest {request with types := types ++ [[.callable [(valueField, [1])] [[(valueField,[99])]] signatures]]}
#guard !validRequest {request with types := types ++ [[.callable [(valueField, [1])] [] [([[1]],[99])]]]}

-- Native certificates split the middle parameter while fixing both neighbors.
-- These are certificate checks, not executions of extracted source programs.
namespace ArgumentCertificates
open PositiveCertificates
private def table : PositiveRules.Table Nat := [([0],[0]),([1],[1])]
private def overloads : List (List (List Nat) × List Nat) :=
  [([[0],[0],[1]],[1]), ([[0],[1],[1]],[1])]
private def split : ArrowCert Nat :=
  .union [[0]] [0] [1] [[1]]
    (.source ([[0],[0],[1]],[1])) (.source ([[0],[1],[1]],[1]))
#guard checkArrow G table overloads [[0],[0,1],[1]] [1] split
#guard !(checkArrow G table overloads [[1],[0,1],[1]] [1] split)
-- Selection cannot silently drop a target argument or ignore a source argument.
#guard !(checkArrow G table [([[0]],[1])] [[0],[1]] [1] (.source ([[0]],[1])))
#guard !(checkArrow G table [([[0],[1]],[1])] [[0]] [1] (.source ([[0],[1]],[1])))
-- Zero arguments have a real call obligation; a bottom parameter is uninhabited.
#guard !(checkArrow G table [] [] [1] .empty)
#guard checkArrow G table [] [[0],[]] [1] .empty
#guard checkArrow G table [([],[1])] [] [1] (.source ([],[1]))
#guard match fromJson? (toJson split) with
  | .error _ => false
  | .ok (decoded : ArrowCert Nat) =>
      decoded == split && checkArrow G table overloads [[0],[0,1],[1]] [1] decoded
-- An out-of-range label in a preserved suffix must fail the outer evidence gate.
private def badSuffix : ArrowCert Nat :=
  .union [[0]] [0] [1] [[99]] .empty .empty
#guard !validEvidence types.length (.node ⟨[],.nul,[0]⟩
  (.sub (.core ⟨table,[([], (([[0]],[1]),badSuffix))]⟩)) [])
end ArgumentCertificates

-- Graph creation, subtype search, and JSON consumption now share native lists.
namespace ArgumentGraphs
private def rows : List (List (Clause (List Nat))) := types ++
  [[.arrs [([[0],[0],[1]],[1]),([[0],[1],[1]],[1])]],
   [.arrs [([[0],[0,1],[1]],[1])]], [.arrs [([],[0])]]]
private def graph : NormalGraph Nat := fun i => rows[i]?.getD []
private def body := Tm.make (.closure 3 (.var 2)) .nul
private def req : Request := ⟨rows,[⟨body,.bind 1⟩,⟨.var 0,.ret⟩],[⟨[],[7]⟩,⟨[[7]],[8]⟩],[8],0,[]⟩
#guard ok (do
  let r ← Json.parse (toJson req).compress
  let c ← produceJson r 8
  verifyJson r (← Json.parse c.compress))
-- A descriptor with an extra parameter is scoped but violates creation's arity premise.
#guard !ProgramCertificates.check graph (.make (.closure 4 (.var 2)) .nul) [7]
  (.node ⟨[],.make (.closure 4 (.var 2)) .nul,[7]⟩ .funE
    [.node ⟨[[0],[0],[1]],.var 2,[1]⟩ .var [],
     .node ⟨[[0],[1],[1]],.var 2,[1]⟩ .var []])
private def zeroReq : Request := ⟨rows,[⟨.make (.closure 0 .nul) .nul,.ret⟩],[⟨[],[9]⟩],[9],0,[]⟩
#guard ok (do
  let r := toJson zeroReq
  verifyJson r (← produceJson r 8))
#guard (subtype graph (List.range rows.length |>.map fun i => [i]) [7] [9]).isNone
#guard !validRequest {req with types := rows ++ [[.arrs [([[0],[99]],[1])]]]}
-- Native invocation reaches the same producer/JSON consumer as unary calls.
private def callReq : Request :=
  {req with
    program := [⟨body,.bind 1⟩,⟨.call (.var 0) [.nul,.tru,.fls],.ret⟩],
    claims := [⟨[],[7]⟩,⟨[[7]],[1]⟩], result := [1]}
#guard ok (do
  let r := toJson callReq
  verifyJson r (← produceJson r 8))
private def zeroCallReq : Request :=
  {zeroReq with
    program := [⟨.call (.make (.closure 0 .nul) .nul) [],.ret⟩],
    claims := [⟨[],[0]⟩], result := [0]}
#guard ok (do
  let r := toJson zeroCallReq
  verifyJson r (← produceJson r 8))

-- A callable's cell is updated by the first operand and read by the second.
-- This exercises effectful operands through the callable-object application rule.
private def cellRows := rows ++ [[.callable [(valueField, [1])] [] [([[0],[1]],[1])]]]
private def cellCallReq : Request :=
  ⟨cellRows,
   [⟨.make (.closure 2 (.var 1)) .tru,.bind 1⟩,
    ⟨.call (.var 0) [.write (.var 0) .fls,.read (.var 0)],.ret⟩],
   [⟨[],[10]⟩,⟨[[10]],[1]⟩],[1],0,[]⟩
#guard ok (do
  let r := toJson cellCallReq
  verifyJson r (← produceJson r 8))

private def argPool := List.range rows.length |>.map fun i => [i]
-- Search may neither truncate extra actuals nor supply missing ones silently.
#guard (expression graph argPool 8 [[7]] (.call (.var 0) [.nul,.tru]) [1]).isNone
#guard (expression graph argPool 8 [[9]] (.call (.var 0) [.nul]) [0]).isNone
#guard (expression graph argPool 8 [[7]] (.call (.var 0) [.nul,.tru,.nul]) [1]).isNone
-- Even valid operand derivations cannot certify a differently ordered call.
private def callClaim : ProgramCertificates.Sequent Nat :=
  ⟨[[7]],.call (.var 0) [.nul,.tru,.fls],[1]⟩
private def callPremises : List (ProgramCertificates.Evidence Nat) :=
  [.node ⟨[[7]],.var 0,[7]⟩ .var [],
   .node ⟨[[7]],.nul,[0]⟩ .nul [],
   .node ⟨[[7]],.tru,[1]⟩ .tru [],
   .node ⟨[[7]],.fls,[1]⟩ .fls []]
#guard ProgramCertificates.checkTree graph (.node callClaim .app callPremises)
#guard !ProgramCertificates.checkTree graph (.node callClaim .app (callPremises.take 3))
#guard !ProgramCertificates.checkTree graph
  (.node callClaim .app (callPremises.set 2 callPremises[3] |>.set 3 callPremises[2]))

end ArgumentGraphs

#print axioms checked
#print axioms returns_false
#print axioms coherent
end Verification.ExperimentState.CallableGraphTests
