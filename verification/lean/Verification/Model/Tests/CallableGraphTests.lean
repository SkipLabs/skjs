import Verification.Model.Source.RequestJson
import Verification.Model.Programs.DirectProof
import Verification.Model.Semantics.GraphCoherence

/-! A single allocated value supports overloaded calls and mutable bag access
through the maintained graph producer, consumer, and JSON protocol. -/
namespace Verification.Model.CallableGraphTests
open Lean PositiveNormalization PositiveGraphs ProgramTyping ControlFlow CertificateProducer RequestJson

/-- Every signature here takes any receiver: label 7 is unknown, and label 8
`undefined`, the receiver a plain call passes. -/
private def signatures : List (CallEffects.Arrow (List Nat)) :=
  [⟨[7],[[1]],[1],.unrestricted⟩,⟨[7],[[0]],[0],.unrestricted⟩]
def types : List (List (Clause (List Nat))) :=
  [[.nul],[.bool],[.callable [(valueField, [1])] [] signatures []],[.arrs signatures []],
   [.callable [(valueField, [1])] [[(valueField,[1])]] signatures []],[.refs [(valueField, [1])] [] []],[.callable [(valueField, [0,1])] [] signatures []],
   [.top],[.undef]]
def G : NormalGraph Nat := .ofRows fun i => types[i]?.getD []
def labels := List.range types.length

/-- The callable's code: one node returning its parameter, frame slot 1, past
the receiver. -/
def code : CallCode := .graph 1 [.var 1] [(.ret, none)] 0 []
/-- The code at each signature it offers, from the frame the signature
describes: the receiver, then the parameter. -/
def codes : List CodeRequest :=
  signatures.map fun s => ⟨⟨1, [.var 1], [(.ret, none)], 0, [], s, none⟩, [⟨s.receiver :: s.arguments, s.result⟩]⟩
def program : Program :=
  [⟨.makeAt code [valueField] [.tru],.bind 1,none⟩,
   ⟨.var 0,.bind 2,none⟩,
   ⟨.write (.var 1) .fls,.effect 3,none⟩,
   ⟨.read (.var 0),.bind 4,none⟩,
   ⟨.app (.var 1) (.var 0),.ret,none⟩]
def claims : List (PointClaim Nat) :=
  [⟨[],[2]⟩,⟨[[2]],[2]⟩,⟨[[2],[2]],[0]⟩,⟨[[2],[2]],[1]⟩,⟨[[1],[2],[2]],[1]⟩]
def request : Request := ⟨types,program,claims,[1],0,[],codes⟩

private def ok (x : Except String α) : Bool := match x with | .ok _ => true | .error _ => false
private def roundtrip (r : Request) : Except String Unit := do
  let r ← Json.parse (toJson r).compress
  let c ← produceJson r 8
  verifyJson r (← Json.parse c.compress)
#guard ok (roundtrip request)
-- Each advertised overload needs its own entry of the code table.
#guard !ok (roundtrip {request with codes := codes.take 1})
-- Unsafe code cannot acquire a table entry, whatever its creation's evidence.
#guard !ok (roundtrip {request with codes := codes.map fun q =>
  {q with entry := {q.entry with exprs := [.app .nul .nul]}}})

/-- One allocation, then an alias write, bag read, and call on the same identity. -/
theorem returns_false : Execution program 16 [] (.at 0 (fun _ => .nul)) [.fls] (.done .fls) := by
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
  apply Execution.next (.expr (.callGraph rfl (by decide)))
  apply Execution.next (.expr (.gotoEnter rfl rfl))
  apply Execution.next (.expr (.frameRet rfl))
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
#guard meet (.callable [(valueField, [1])] [] signatures []) (.arrs [⟨[7], [[1]], [1], .unrestricted⟩] []) ==
  [.callable [(valueField, [1])] [] (signatures ++ [⟨[7],[[1]],[1],.unrestricted⟩]) []]
#guard meet (.callable [(valueField, [1])] [] signatures []) (.callable [(valueField, [1])] [] signatures []) ==
  [.callable [(valueField, [1])] [[(valueField,[1])]] (signatures ++ signatures) []]
#guard meet (.refs [(valueField, [1])] [] []) (.callable [(valueField, [1])] [] signatures []) == []

-- Invalid bag writes and plain-object calls cannot acquire evidence.
#guard !(expression G pool 8 [[2]] (.write (.var 0) .nul) [0]).isSome
#guard !(expression G pool 8 [[5]] (.app (.var 0) .tru) [1]).isSome

-- A creation's evidence names the bag's fields, then the code's captures; its
-- code is the table's question, so every code is admitted here.
private def creationTerm : Tm := .makeAt code [valueField] [.tru]
private def creation := expression G pool 8 [] creationTerm [2]
#guard match creation with
  | some e => ProgramCertificates.check G creationTerm [2] e (fun _ => true)
  | none => false
private def creationPlan : DirectProof.Plan :=
  .rule ⟨[],creationTerm,[2]⟩ (.callableGraph []) [.rule ⟨[],.tru,[1]⟩ .tru []]
#guard match DirectProof.render G pool [] creationPlan with
  | none => false
  | some e => ProgramCertificates.check G creationTerm [2] e (fun _ => true)
-- A plain object's type is no callable's, and the bag's field is claimed.
#guard !(expression G pool 8 [] (.makeAt code [valueField] [.nul]) [2]).isSome

-- Labels in the new clause's bag and arrow operands remain range checked.
#guard !validRequest {request with types := RequestJson.rows (types ++ [[.callable [(valueField, [99])] [] signatures []]])}
#guard !validRequest {request with types := RequestJson.rows (types ++ [[.callable [(valueField, [1])] [[(valueField,[99])]] signatures []]])}
#guard !validRequest {request with types := RequestJson.rows (types ++ [[.callable [(valueField, [1])] [] [⟨[7], [[1]], [99], .unrestricted⟩] []]])}
#guard !validRequest {request with types := RequestJson.rows (types ++ [[.callable [(valueField, [1])] [] [⟨[99], [[1]], [1], .unrestricted⟩] []]])}

-- Native certificates split the middle parameter while fixing both neighbors.
-- These are certificate checks, not executions of extracted source programs.
namespace ArgumentCertificates
open PositiveCertificates
private def table : PositiveRules.Table Nat := [([0],[0]),([1],[1]),([7],[7])]
private def overloads : List (CallEffects.Arrow (List Nat)) :=
  [⟨[7],[[0],[0],[1]],[1],.unrestricted⟩, ⟨[7],[[0],[1],[1]],[1],.unrestricted⟩]
private def split : ArrowCert Nat :=
  .union [[0]] [0] [1] [[1]]
    (.source ⟨[7], [[0],[0],[1]], [1], .unrestricted⟩) (.source ⟨[7], [[0],[1],[1]], [1], .unrestricted⟩)
#guard checkArrow G table overloads [] ⟨[7], [[0],[0,1],[1]], [1], .unrestricted⟩ split
#guard !(checkArrow G table overloads [] ⟨[7], [[1],[0,1],[1]], [1], .unrestricted⟩ split)
-- Selection cannot silently drop a target argument or ignore a source argument.
#guard !(checkArrow G table [⟨[7], [[0]], [1], .unrestricted⟩] [] ⟨[7], [[0],[1]], [1], .unrestricted⟩ (.source ⟨[7], [[0]], [1], .unrestricted⟩))
#guard !(checkArrow G table [⟨[7], [[0],[1]], [1], .unrestricted⟩] [] ⟨[7], [[0]], [1], .unrestricted⟩ (.source ⟨[7], [[0],[1]], [1], .unrestricted⟩))
-- Zero arguments have a real call obligation; a bottom parameter is uninhabited.
#guard !(checkArrow G table [] [] ⟨[7], [], [1], .unrestricted⟩ .empty)
#guard checkArrow G table [] [] ⟨[7], [[0],[]], [1], .unrestricted⟩ .empty
#guard checkArrow G table [⟨[7], [], [1], .unrestricted⟩] [] ⟨[7], [], [1], .unrestricted⟩ (.source ⟨[7], [], [1], .unrestricted⟩)
-- A receiver no value meets names no call; a receiver the source does not
-- accept is not covered.
#guard checkArrow G table [] [] ⟨[], [[0]], [1], .unrestricted⟩ .emptyRecv
#guard !(checkArrow G table [⟨[0], [], [1], .unrestricted⟩] [] ⟨[7], [], [1], .unrestricted⟩ (.source ⟨[0], [], [1], .unrestricted⟩))
#guard match fromJson? (toJson split) with
  | .error _ => false
  | .ok (decoded : ArrowCert Nat) =>
      decoded == split && checkArrow G table overloads [] ⟨[7], [[0],[0,1],[1]], [1], .unrestricted⟩ decoded
-- An out-of-range label in a preserved suffix must fail the outer evidence gate.
private def badSuffix : ArrowCert Nat :=
  .union [[0]] [0] [1] [[99]] .empty .empty
#guard !validEvidence types.length (.node ⟨[],.nul,[0]⟩
  (.sub (.core ⟨table,[([], (⟨[7], [[0]], [1], .unrestricted⟩,badSuffix))]⟩)) [])
end ArgumentCertificates

-- Graph creation, subtype search, and JSON consumption now share native lists.
namespace ArgumentGraphs
private def rows : List (List (Clause (List Nat))) := types ++
  [[.arrs [⟨[7], [[0],[0],[1]], [1], .unrestricted⟩,⟨[7], [[0],[1],[1]], [1], .unrestricted⟩] []],
   [.arrs [⟨[7], [[0],[0,1],[1]], [1], .unrestricted⟩] []], [.arrs [⟨[7], [], [0], .unrestricted⟩] []]]
private def graph : NormalGraph Nat := .ofRows fun i => rows[i]?.getD []
/-- One-node code of `arity` returning `e`, and its entry at each signature of
row 9 or of `sigs`, each from the frame the signature describes. -/
private def oneNode (arity : Nat) (e : Tm) : CallCode := .graph arity [e] [(.ret, none)] 0 []
private def entries (arity : Nat) (e : Tm) (sigs : List (CallEffects.Arrow (List Nat))) :
    List CodeRequest :=
  sigs.map fun s => ⟨⟨arity, [e], [(.ret, none)], 0, [], s, none⟩, [⟨s.receiver :: s.arguments.take arity, s.result⟩]⟩
private def overloads : List (CallEffects.Arrow (List Nat)) :=
  [⟨[7],[[0],[0],[1]],[1],.unrestricted⟩,⟨[7],[[0],[1],[1]],[1],.unrestricted⟩]
private def body := Tm.make (oneNode 3 (.var 3)) .nul
private def req : Request := ⟨rows,[⟨body,.bind 1,none⟩,⟨.var 0,.ret,none⟩],[⟨[],[9]⟩,⟨[[9]],[10]⟩],[10],0,[],
  entries 3 (.var 3) overloads⟩
private def roundtrip (r : Request) : Except String Unit := do
  let r ← Json.parse (toJson r).compress
  let c ← produceJson r 8
  verifyJson r (← Json.parse c.compress)
-- Each code sees the receiver, which it does not read, then its parameters.
#guard ok (roundtrip req)
-- Code taking more parameters than a signature offers is no entry of it.
private def wideProgram : Program := [⟨.make (oneNode 4 (.var 3)) .nul,.bind 1,none⟩,⟨.var 0,.ret,none⟩]
private def wideReq : Request := ⟨rows,wideProgram,req.claims,[10],0,[],entries 4 (.var 3) overloads⟩
#guard !ok (roundtrip wideReq)
private def zeroReq : Request := ⟨rows,[⟨.make (oneNode 0 .nul) .nul,.ret,none⟩],[⟨[],[11]⟩],[11],0,[],
  entries 0 .nul [⟨[7], [], [0], .unrestricted⟩]⟩
#guard ok (do
  let r := toJson zeroReq
  verifyJson r (← produceJson r 8))
#guard (subtype graph (List.range rows.length |>.map fun i => [i]) [9] [11]).isNone
#guard !validRequest {req with types := RequestJson.rows (rows ++ [[.arrs [⟨[7], [[0],[99]], [1], .unrestricted⟩] []]])}
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
    program := [⟨.call (.make (oneNode 0 .nul) .nul) [],.ret,none⟩],
    claims := [⟨[],[0]⟩], result := [0]}
#guard ok (do
  let r := toJson zeroCallReq
  verifyJson r (← produceJson r 8))

-- A callable's cell is updated by the first operand and read by the second.
-- This exercises effectful operands through the callable-object application rule.
private def cellRows := rows ++ RequestJson.rows [[.callable [(valueField, [1])] [] [⟨[7], [[0],[1]], [1], .unrestricted⟩] []]]
private def cellCallReq : Request :=
  ⟨cellRows,
   [⟨.make (oneNode 2 (.var 2)) .tru,.bind 1,none⟩,
    ⟨.call (.var 0) [.write (.var 0) .fls,.read (.var 0)],.ret,none⟩],
   [⟨[],[12]⟩,⟨[[12]],[1]⟩],[1],0,[], entries 2 (.var 2) [⟨[7], [[0],[1]], [1], .unrestricted⟩]⟩
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
#guard ProgramCertificates.checkTree graph (.node callClaim (.app .unrestricted) callPremises)
#guard !ProgramCertificates.checkTree graph (.node callClaim (.app .unrestricted) (callPremises.take 4))
#guard !ProgramCertificates.checkTree graph
  (.node callClaim (.app .unrestricted) (callPremises.set 3 callPremises[4] |>.set 4 callPremises[3]))
-- The receiver premise is not optional, and must type the receiver term.
#guard !ProgramCertificates.checkTree graph (.node callClaim (.app .unrestricted) (callPremises.eraseIdx 1))
#guard !ProgramCertificates.checkTree graph
  (.node callClaim (.app .unrestricted) (callPremises.set 1 (.node ⟨[[9]],.nul,[0]⟩ .nul [])))

end ArgumentGraphs

#print axioms returns_false
end Verification.Model.CallableGraphTests
