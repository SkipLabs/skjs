import Verification.Model.Source.RequestJson
import Verification.Model.Tests.CertificateProducerTests
import Verification.Model.Tests.GraphCodeFixtures

namespace Verification.Model.RequestJsonTests
open Lean ProgramTyping ControlFlow CertificateProducer RequestJson

private def toNatClause : PositiveNormalization.Clause (List (Fin 7)) → PositiveNormalization.Clause (List Nat) :=
  PositiveNormalization.Clause.map (List.map Fin.val)

def types : List (List (PositiveNormalization.Clause (List Nat))) :=
  (List.finRange 7).map (fun i => (ProgramTypingTests.G i).map toNatClause)

def natClaim (c : PointClaim (Fin 7)) : PointClaim Nat :=
  ⟨c.context.map (List.map Fin.val), c.type.map Fin.val⟩

/-- The dispatching closure's code at both signatures of label 3, capturing
one cell of label 2. -/
def dispatchCodes : List (CodeRequest Nat) :=
  GraphCodeFixtures.oneNodeCodes 1 (.ite (.test .isNul (.var 1)) (.read (.var 2)) .nul) [[2]]
    [⟨[6], [[0]], [1], .unrestricted⟩, ⟨[6], [[1]], [0], .unrestricted⟩]

def mappedRequest : Request RequestJson.Table Nat := ⟨types, CertificateProducerTests.mapped,
  CertificateProducerTests.mappedClaims.map natClaim, [1], 0, [], dispatchCodes⟩

def loopRequest : Request RequestJson.Table Nat := ⟨types, ControlFlowTests.loop,
  CertificateProducerTests.loopClaims.map natClaim, [1], 0, [], dispatchCodes⟩

def diamondRequest : Request RequestJson.Table Nat := ⟨types, CertificateProducerTests.mappedDiamond,
  CertificateProducerTests.mappedDiamondClaims.map natClaim, [0,1], 0, [], []⟩

/-- This request forces a structural overload subsumption certificate, including
its cyclic relation table and union-domain arrow evidence, through JSON. -/
def overloadRequest : Request RequestJson.Table Nat := ⟨types,
  [⟨.alloc .tru, .bind 1,none⟩, ⟨.make ControlFlowTests.dispatchCode .nul, .bind 2,none⟩,
   ⟨.var 0, .bind ⟨3,some [0,2]⟩,none⟩, ⟨.app (.var 0) .nul, .ret,none⟩],
  [⟨[],[2]⟩, ⟨[[2]],[3]⟩, ⟨[[3],[2]],[4]⟩, ⟨[[4],[2]],[0,1]⟩], [0,1], 0, [], dispatchCodes⟩

def ok (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

def roundtrip (r : Request RequestJson.Table Nat) : Except String Unit := do
  let request ← Json.parse (toJson r).compress
  let response ← produceJson RequestJson.Table request 12
  let evidence ← Json.parse response.compress
  verifyJson RequestJson.Table request evidence

-- A string key keeps its JSON string; a symbol key is `{"symbol": id}`, and
-- the two never decode to each other.
#guard toJson (PropKey.str "a") == Json.str "a"
#guard toJson (PropKey.sym 3) == Json.mkObj [("symbol", toJson (3 : Nat))]
#guard (fromJson? (toJson (PropKey.sym 3)) : Except String PropKey).toOption == some (.sym 3)
#guard (fromJson? (Json.str "3") : Except String PropKey).toOption == some (.str "3")
#guard !(ok (fromJson? (Json.mkObj [("symbol", toJson (3 : Nat)), ("x", Json.null)]) : Except String PropKey))
#guard ok (roundtrip mappedRequest)
#guard ok (roundtrip loopRequest)
#guard ok (roundtrip diamondRequest)
#guard ok (roundtrip overloadRequest)
-- The created code must be in the table.
#guard !ok (roundtrip { mappedRequest with codes := [] })
#guard !ok (roundtrip { mappedRequest with codes := dispatchCodes.take 1 })
-- `codes` is left out when empty: absence decodes as none, and an explicit
-- empty list, a second spelling, is refused.
#guard ((toJson diamondRequest).getObjVal? "codes").toOption.isNone
#guard ok (decodeRequest RequestJson.Table (toJson diamondRequest))
#guard !ok (decodeRequest RequestJson.Table ((toJson diamondRequest).setObjVal! "codes" (Json.arr #[])))

-- A response contains evidence only: the request is supplied independently.
def response : Json := match produceJson RequestJson.Table (toJson mappedRequest) 12 with
  | .ok j => j
  | .error _ => .null

-- Changed requirements, source code and bindings are checked again.
#guard !(ok (verifyJson RequestJson.Table (toJson { mappedRequest with result := [0] }) response))
#guard !(ok (verifyJson RequestJson.Table (toJson { mappedRequest with start := 99 }) response))
#guard !(ok (verifyJson RequestJson.Table (toJson { mappedRequest with claims := [] }) response))
#guard !(ok (verifyJson RequestJson.Table (toJson { mappedRequest with program := (mappedRequest.program.set 3 ⟨.write (.var 1) .nul, .effect ⟨4,some [0,2]⟩,none⟩) }) response))
#guard !(ok (verifyJson RequestJson.Table (toJson { mappedRequest with program := (mappedRequest.program.set 0 ⟨.alloc .tru, .bind ⟨1,some [0,99]⟩,none⟩) }) response))

-- Reject dangling labels even in unused type definitions.
#guard !(ok (decodeRequest RequestJson.Table (toJson { mappedRequest with types := (mappedRequest.types ++ RequestJson.rows [[PositiveNormalization.Clause.refs [(valueField, [99])] [] []]]) })))
#guard ok (decodeRequest RequestJson.Table (toJson { mappedRequest with types :=
  mappedRequest.types ++ (RequestJson.rows [[PositiveNormalization.Clause.dict [] [] [] [(.strings, [1])]]]) }))
#guard !(ok (decodeRequest RequestJson.Table (toJson { mappedRequest with types :=
  mappedRequest.types ++ (RequestJson.rows [[PositiveNormalization.Clause.dict [] [] [] [(.strings, [99])]]]) })))
#guard !(ok (decodeRequest RequestJson.Table (toJson { mappedRequest with result := [99] })))
#guard !(ok (decodeRequest RequestJson.Table (toJson { mappedRequest with claims := [⟨[[99]],[1]⟩] })))
#guard !(ok (produceJson RequestJson.Table (toJson mappedRequest) 0))

private def changeField (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .obj kvs => Json.mkObj ((kvs.toList.filter (fun p => p.1 != key)) ++ [(key,value)])
  | _ => j
private def omitField (j : Json) (key : String) : Json :=
  match j with
  | .obj kvs => Json.mkObj (kvs.toList.filter (fun p => p.1 != key))
  | _ => j

-- Schema typos and future flags cannot disappear during decoding.
#guard !(ok (decodeRequest RequestJson.Table (changeField (toJson mappedRequest) "unsupported" (.bool true))))
#guard !(ok (decodeRequest RequestJson.Table (omitField (toJson mappedRequest) "claims")))
#guard !(ok (decodeRequest RequestJson.Table (changeField (toJson mappedRequest) "start" (.str "0"))))
#guard !(ok (verifyJson RequestJson.Table (toJson mappedRequest) (changeField response "certificate" (toJson ([] : List Nat)))))
#guard !(ok (verifyJson RequestJson.Table (toJson mappedRequest) (changeField response "unchecked" (.bool true))))
#guard !(ok (verifyJson RequestJson.Table (toJson mappedRequest) (.str "accept")))

-- Reject labels hidden in evidence, including transitivity intermediates.
#guard !(validResponse mappedRequest ⟨[{expression := .node ⟨[],.nul,[0]⟩ (.sub (.trans [99] .subset .subset)) [], edges := []}], []⟩)

-- Defaults and unsupported source refinements cannot silently enter the format.
#guard !(ok (decodeStrict (α := Target) (Json.mkObj [("label",toJson (0 : Nat))])))
#guard !(ok (decodeRequest RequestJson.Table (changeField (toJson mappedRequest) "types"
  (toJson ([["tru"]] : List (List String))))))

-- Field order is immaterial, including at nested object positions.
private def reverseFields : Json → Json
  | .obj kvs => Json.mkObj kvs.toList.reverse
  | j => j
#guard ok (verifyJson RequestJson.Table (reverseFields (toJson mappedRequest)) (reverseFields response))
#guard !(sameJson (Json.mkObj [("x",toJson (0 : Nat))])
  (Json.mkObj [("x",toJson (0 : Nat)),("y",toJson (1 : Nat))]))

-- External inputs are checked independently of the entry point claim.
def inputRequest : Request RequestJson.Table Nat := ⟨RequestJson.rows [[.bool]], [⟨.var 0,.ret,none⟩], [⟨[[0]],[0]⟩], [0],0,[[0]], []⟩
#guard ok (roundtrip inputRequest)
#guard !ok (roundtrip { inputRequest with inputs := [] })
#guard !ok (roundtrip { inputRequest with inputs := [[0],[0]] })
#guard !ok (decodeRequest RequestJson.Table (toJson { inputRequest with inputs := [[99]] }))
#guard !ok (decodeRequest RequestJson.Table (omitField (toJson inputRequest) "inputs"))
-- The generalized theorem also covers stateful arguments, not just primitive
-- source parameters. The input reference may belong to any satisfying heap.
def referenceInput : Request RequestJson.Table Nat := ⟨RequestJson.rows [[.bool],[.refs [(valueField, [0])] [] []]],
  [⟨.read (.var 0),.ret,none⟩], [⟨[[1]],[0]⟩], [0],0,[[1]], []⟩
#guard ok (roundtrip referenceInput)
#guard !ok (roundtrip { referenceInput with inputs := [[0]] })

end Verification.Model.RequestJsonTests
