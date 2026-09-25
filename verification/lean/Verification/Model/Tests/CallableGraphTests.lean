import Verification.Model.Source.RequestJson
import Verification.Model.Programs.DirectProof
import Verification.Model.Semantics.GraphCoherence

/-! A single allocated value supports overloaded calls and mutable bag access
through the maintained graph producer, consumer, and JSON protocol. -/
namespace Verification.Model.CallableGraphTests
open Lean PositiveNormalization PositiveGraphs ProgramTyping ControlFlow CertificateProducer RequestJson

/-- Every signature here takes any receiver: label 7 is unknown, and label 8
`undefined`, the receiver a plain call passes. -/
private def signatures : List (List Nat × List (List Nat) × List Nat) :=
  [([7],[[1]],[1]),([7],[[0]],[0])]
def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.callable [(valueField, [1])] [] signatures []],[.arrs signatures []],
   [.callable [(valueField, [1])] [[(valueField,[1])]] signatures []],[.refs [(valueField, [1])] [] []],[.callable [(valueField, [0,1])] [] signatures []],
   [.top],[.undef]]
def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
def labels := List.range types.length

def program : Program :=
  [⟨.attach (.var 1) .tru,.bind 1,none⟩,
   ⟨.var 0,.bind 2,none⟩,
   ⟨.write (.var 1) .fls,.effect 3,none⟩,
   ⟨.read (.var 0),.bind 4,none⟩,
   ⟨.app (.var 1) (.var 0),.ret,none⟩]
def claims : List (PointClaim Nat) :=
  [⟨[],[2]⟩,⟨[[2]],[2]⟩,⟨[[2],[2]],[0]⟩,⟨[[2],[2]],[1]⟩,⟨[[1],[2],[2]],[1]⟩]
def request : Request := ⟨types,program,claims,[1],0,[], []⟩
def certificate : ControlFlow.Certificate Nat :=
  match produce G labels 8 [1] program claims 0 with
  | .ok c => c
  | .error _ => []

#guard checkClosed G [1] program certificate 0

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

private def pool := vocabulary G labels claims []
-- Properties may be forgotten for calls; they cannot be widened covariantly or
-- converted to plain-reference shape. Duplicate invariant constraints are safe.
#guard (subtype G pool [2] [3]).isSome
#guard (subtype G pool [2] [4]).isSome
#guard !(subtype G pool [2] [5]).isSome
#guard !(subtype G pool [2] [6]).isSome
#guard !(subtype G pool [3] [2]).isSome

-- Normalization merges property constraints and overloads without allocation.
#guard meet (.callable [(valueField, [1])] [] signatures []) (.arrs [([7],[[1]],[1])] []) ==
  [.callable [(valueField, [1])] [] (signatures ++ [([7],[[1]],[1])]) []]
#guard meet (.callable [(valueField, [1])] [] signatures []) (.callable [(valueField, [1])] [] signatures []) ==
  [.callable [(valueField, [1])] [[(valueField,[1])]] (signatures ++ signatures) []]
#guard meet (.refs [(valueField, [1])] [] []) (.callable [(valueField, [1])] [] signatures []) == []

-- Unsafe code, invalid bag writes, and plain-object calls cannot acquire evidence.
#guard !(expression G pool 8 [] (.attach (.app .nul .nul) .tru) [2]).isSome
#guard !(expression G pool 8 [[2]] (.write (.var 0) .nul) [0]).isSome
#guard !(expression G pool 8 [[5]] (.app (.var 0) .tru) [1]).isSome

-- Direct-proof rendering reinstates the argument binder for each overload.
private def creation := expression G pool 8 [] (.attach (.var 1) .tru) [2]
#guard creation.isSome
private def creationPlan : DirectProof.Plan :=
  .rule ⟨[],.attach (.var 1) .tru,[2]⟩ .makeCallable
    [.rule ⟨[],.tru,[1]⟩ .tru [],
     .rule ⟨[[7],[1]],.var 1,[1]⟩ .var [],
     .rule ⟨[[7],[0]],.var 1,[0]⟩ .var []]
#guard match DirectProof.render G pool [] creationPlan with
  | none => false
  | some e => ProgramCertificates.check G (.attach (.var 1) .tru) [2] e

-- Labels in the new clause's bag and arrow operands remain range checked.
#guard !validRequest {request with types := RequestJson.rows (types ++ [[.callable [(valueField, [99])] [] signatures []]])}
#guard !validRequest {request with types := RequestJson.rows (types ++ [[.callable [(valueField, [1])] [[(valueField,[99])]] signatures []]])}
#guard !validRequest {request with types := RequestJson.rows (types ++ [[.callable [(valueField, [1])] [] [([7],[[1]],[99])] []]])}
#guard !validRequest {request with types := RequestJson.rows (types ++ [[.callable [(valueField, [1])] [] [([99],[[1]],[1])] []]])}

-- Native certificates split the middle parameter while fixing both neighbors.
-- These are certificate checks, not executions of extracted source programs.
namespace ArgumentCertificates
open PositiveCertificates
private def table : PositiveRules.Table Nat := [([0],[0]),([1],[1]),([7],[7])]
private def overloads : List (List Nat × List (List Nat) × List Nat) :=
  [([7],[[0],[0],[1]],[1]), ([7],[[0],[1],[1]],[1])]
private def split : ArrowCert Nat :=
  .union [[0]] [0] [1] [[1]]
    (.source ([7],[[0],[0],[1]],[1])) (.source ([7],[[0],[1],[1]],[1]))
#guard checkArrow G table overloads [] [7] [[0],[0,1],[1]] [1] split
#guard !(checkArrow G table overloads [] [7] [[1],[0,1],[1]] [1] split)
-- Selection cannot silently drop a target argument or ignore a source argument.
#guard !(checkArrow G table [([7],[[0]],[1])] [] [7] [[0],[1]] [1] (.source ([7],[[0]],[1])))
#guard !(checkArrow G table [([7],[[0],[1]],[1])] [] [7] [[0]] [1] (.source ([7],[[0],[1]],[1])))
-- Zero arguments have a real call obligation; a bottom parameter is uninhabited.
#guard !(checkArrow G table [] [] [7] [] [1] .empty)
#guard checkArrow G table [] [] [7] [[0],[]] [1] .empty
#guard checkArrow G table [([7],[],[1])] [] [7] [] [1] (.source ([7],[],[1]))
-- A receiver no value meets names no call; a receiver the source does not
-- accept is not covered.
#guard checkArrow G table [] [] [] [[0]] [1] .emptyRecv
#guard !(checkArrow G table [([0],[],[1])] [] [7] [] [1] (.source ([0],[],[1])))
#guard match fromJson? (toJson split) with
  | .error _ => false
  | .ok (decoded : ArrowCert Nat) =>
      decoded == split && checkArrow G table overloads [] [7] [[0],[0,1],[1]] [1] decoded
-- An out-of-range label in a preserved suffix must fail the outer evidence gate.
private def badSuffix : ArrowCert Nat :=
  .union [[0]] [0] [1] [[99]] .empty .empty
#guard !validEvidence types.length (.node ⟨[],.nul,[0]⟩
  (.sub (.core ⟨table,[([], (([7],[[0]],[1]),badSuffix))]⟩)) [])
end ArgumentCertificates

-- Graph creation, subtype search, and JSON consumption now share native lists.
namespace ArgumentGraphs
private def rows : List (List (Clause (List Nat))) := types ++
  [[.arrs [([7],[[0],[0],[1]],[1]),([7],[[0],[1],[1]],[1])] []],
   [.arrs [([7],[[0],[0,1],[1]],[1])] []], [.arrs [([7],[],[0])] []]]
private def graph : NormalGraph Nat := .ofRows fun i => rows[i]?.getD []
private def body := Tm.make (.closure 3 (.var 3)) .nul
private def req : Request := ⟨rows,[⟨body,.bind 1,none⟩,⟨.var 0,.ret,none⟩],[⟨[],[9]⟩,⟨[[9]],[10]⟩],[10],0,[], []⟩
#guard ok (do
  let r ← Json.parse (toJson req).compress
  let c ← produceJson r 8
  verifyJson r (← Json.parse c.compress))
-- A descriptor with an extra parameter is scoped but violates creation's arity premise.
#guard !ProgramCertificates.check graph (.make (.closure 4 (.var 3)) .nul) [9]
  (.node ⟨[],.make (.closure 4 (.var 3)) .nul,[9]⟩ .funE
    [.node ⟨[[7],[0],[0],[1]],.var 3,[1]⟩ .var [],
     .node ⟨[[7],[0],[1],[1]],.var 3,[1]⟩ .var []])
-- With the right arity it is accepted: each body sees the receiver, which it
-- does not read, then its parameters.
#guard ProgramCertificates.check graph body [9]
  (.node ⟨[],body,[9]⟩ .funE
    [.node ⟨[[7],[0],[0],[1]],.var 3,[1]⟩ .var [],
     .node ⟨[[7],[0],[1],[1]],.var 3,[1]⟩ .var []])
private def zeroReq : Request := ⟨rows,[⟨.make (.closure 0 .nul) .nul,.ret,none⟩],[⟨[],[11]⟩],[11],0,[], []⟩
#guard ok (do
  let r := toJson zeroReq
  verifyJson r (← produceJson r 8))
#guard (subtype graph (List.range rows.length |>.map fun i => [i]) [9] [11]).isNone
#guard !validRequest {req with types := RequestJson.rows (rows ++ [[.arrs [([7],[[0],[99]],[1])] []]])}
-- Native invocation reaches the same producer/JSON consumer as unary calls.
private def callReq : Request :=
  {req with
    program := [⟨body,.bind 1,none⟩,⟨.call (.var 0) [.nul,.tru,.fls],.ret,none⟩],
    claims := [⟨[],[9]⟩,⟨[[9]],[1]⟩], result := [1]}
#guard ok (do
  let r := toJson callReq
  verifyJson r (← produceJson r 8))
private def zeroCallReq : Request :=
  {zeroReq with
    program := [⟨.call (.make (.closure 0 .nul) .nul) [],.ret,none⟩],
    claims := [⟨[],[0]⟩], result := [0]}
#guard ok (do
  let r := toJson zeroCallReq
  verifyJson r (← produceJson r 8))

-- A callable's cell is updated by the first operand and read by the second.
-- This exercises effectful operands through the callable-object application rule.
private def cellRows := rows ++ RequestJson.rows [[.callable [(valueField, [1])] [] [([7],[[0],[1]],[1])] []]]
private def cellCallReq : Request :=
  ⟨cellRows,
   [⟨.make (.closure 2 (.var 2)) .tru,.bind 1,none⟩,
    ⟨.call (.var 0) [.write (.var 0) .fls,.read (.var 0)],.ret,none⟩],
   [⟨[],[12]⟩,⟨[[12]],[1]⟩],[1],0,[], []⟩
#guard ok (do
  let r := toJson cellCallReq
  verifyJson r (← produceJson r 8))

private def argPool := List.range rows.length |>.map fun i => [i]
-- Search may neither truncate extra actuals nor supply missing ones silently.
#guard (expression graph argPool 8 [[9]] (.call (.var 0) [.nul,.tru]) [1]).isNone
#guard (expression graph argPool 8 [[11]] (.call (.var 0) [.nul]) [0]).isNone
#guard (expression graph argPool 8 [[9]] (.call (.var 0) [.nul,.tru,.nul]) [1]).isNone
-- Even valid operand derivations cannot certify a differently ordered call.
private def callClaim : ProgramCertificates.Sequent Nat :=
  ⟨[[9]],.call (.var 0) [.nul,.tru,.fls],[1]⟩
private def callPremises : List (ProgramCertificates.Evidence Nat) :=
  [.node ⟨[[9]],.var 0,[9]⟩ .var [],
   .node ⟨[[9]],.undef,[7]⟩ (.sub (.core ⟨[([8],[7])],[]⟩)) [.node ⟨[[9]],.undef,[8]⟩ .undef []],
   .node ⟨[[9]],.nul,[0]⟩ .nul [],
   .node ⟨[[9]],.tru,[1]⟩ .tru [],
   .node ⟨[[9]],.fls,[1]⟩ .fls []]
#guard ProgramCertificates.checkTree graph (.node callClaim .app callPremises)
#guard !ProgramCertificates.checkTree graph (.node callClaim .app (callPremises.take 4))
#guard !ProgramCertificates.checkTree graph
  (.node callClaim .app (callPremises.set 3 callPremises[4] |>.set 4 callPremises[3]))
-- The receiver premise is not optional, and must type the receiver term.
#guard !ProgramCertificates.checkTree graph (.node callClaim .app (callPremises.eraseIdx 1))
#guard !ProgramCertificates.checkTree graph
  (.node callClaim .app (callPremises.set 1 (.node ⟨[[9]],.nul,[0]⟩ .nul [])))

end ArgumentGraphs

#print axioms returns_false
end Verification.Model.CallableGraphTests
