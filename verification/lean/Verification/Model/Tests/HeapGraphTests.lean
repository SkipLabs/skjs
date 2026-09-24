import Verification.Model.Source.RequestJson
import Verification.Model.Source.SourceTypes

/-! Heap postconditions through the maintained graph checker. The graph uses
source-style operand temporaries, an effect-only write and an explicit slot map.
The wider Boolean read claim remains intact; its result fact proves true. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

namespace Verification.Model.HeapGraphTests
open ProgramTyping ProgramCertificates ControlFlow HeapKnowledge HeapExpressionRules

private def T : SourceTypes.Table := SourceTypes.initial ++ RequestJson.rows [[.refs [(valueField, [1,2])] [] []]]
private def G := SourceTypes.graph T
private def leaf (Γ : List (List Nat)) (t : Tm) (A : List Nat) (r : Rule Nat) : Evidence Nat :=
  .node ⟨Γ,t,A⟩ r []
private def widen (e : Evidence Nat) : Evidence Nat :=
  .node {(claim e) with type := [1,2]} (.sub .subset) [e]

def program : Program :=
  [⟨.fls,.bind 1⟩,⟨.alloc (.var 0),.bind 2⟩,⟨.tru,.bind 3⟩,
   ⟨.write (.var 1) (.var 0),.effect ⟨4,some [1]⟩⟩,
   ⟨.read (.var 0),.bind 5⟩,⟨.var 0,.ret⟩]

private def allocProof : Evidence Nat := .node ⟨[[2]],.alloc (.var 0),[4]⟩ .alloc
  [widen (leaf [[2]] (.var 0) [2] .var)]
private def writeProof : Evidence Nat := .node ⟨[[1],[4],[2]],.write (.var 1) (.var 0),[0]⟩ .write
  [leaf [[1],[4],[2]] (.var 1) [4] .var, widen (leaf [[1],[4],[2]] (.var 0) [1] .var)]
private def allocated : Knowledge := allocOutput ⟨[],[],[]⟩ [(valueField, [.fls])]
private def beforeWrite := pureOutput allocated .tru
private def written := writeOutput beforeWrite 1 valueField [.tru]
private def beforeRead : Knowledge := ⟨[⟨0,[.tru],valueField⟩],[],[]⟩
private def readResult := readOutput beforeRead 0 valueField [.tru]

def certificate : ControlFlow.Certificate Nat :=
  [{expression := leaf [] .fls [2] .flsLit, edges := [[.subset]]},
   {expression := allocProof, edges := [[.subset,.subset]],
    effect := some (.allocated allocProof), output := allocated},
   {expression := leaf [[4],[2]] .tru [1] .truLit, edges := [[.subset,.subset,.subset]],
    knowledge := allocated, effect := some (.pure (leaf [[4],[2]] .tru [1] .truLit)), output := beforeWrite},
   {expression := writeProof, edges := [[.subset]], knowledge := beforeWrite,
    effect := some (.written 1 0 [.tru] writeProof), output := written},
   {expression := leaf [[4]] (.read (.var 0)) [1,2] .read, edges := [[.subset,.subset]],
    knowledge := beforeRead, effect := some (.observedRead 0 [.tru]), output := readResult},
   {expression := leaf [[1,2],[4]] (.var 0) [1] .var, edges := [], knowledge := readResult,
    effect := some (.knownValue 0 [.tru]), output := withResult (copy readResult 0) [.tru]}]

#guard checkClosed G [1] program certificate 0

theorem checked : checkClosed G [1] program certificate 0 = true := by decide +kernel

theorem safe (n : Nat) : SafeGraph program (PositiveRules.meaning G [1]) n
    (ofList []) [] (.at 0 (fun _ => .nul)) := accepted_closed_safe checked n

-- A false observation cannot be preserved through the checked true write.
#guard !(checkClosed G [1] program
  (certificate.set 4 {certificate[4] with knowledge := ⟨[⟨0,[.fls],valueField⟩],[],[]⟩}) 0)
-- Local facts cannot simply be assumed at the external entry.
#guard !(checkClosed G [1] program
  (certificate.set 0 {certificate[0] with knowledge := ⟨[],[⟨0,[.tru],valueField⟩],[]⟩}) 0)
-- Nor can evidence invent its own postcondition or change the actual slot map.
#guard !(checkClosed G [1] program
  (certificate.set 3 {certificate[3] with output := ⟨[⟨2,[.fls],valueField⟩],[],[]⟩}) 0)
#guard !(checkClosed G [1] (program.set 3 ⟨.write (.var 1) (.var 0),.effect ⟨4,some [0]⟩⟩) certificate 0)

-- A back edge must re-establish the head's facts just like the first edge.
private def cycleProgram := program.set 5 ⟨.var 0,.effect ⟨4,some [1]⟩⟩
private def cycleValue := leaf [[1,2],[4]] (.var 0) [1,2] .var
private def cycleCertificate := certificate.set 5
  {expression := cycleValue, edges := [[.subset]], knowledge := readResult,
   effect := some (.pure cycleValue), output := copy readResult 0}
#guard checkClosed G [1] cycleProgram cycleCertificate 0
-- The ordinary rule is locally valid but discards the cell observation, so
-- its back edge fails; an initial incoming edge alone cannot justify a loop.
#guard (checkStep G (claim cycleValue) readResult (.ordinary cycleValue)).isSome
#guard !(checkClosed G [1] cycleProgram (cycleCertificate.set 5
  {cycleCertificate[5] with effect := some (.ordinary cycleValue), output := ordinaryOutput readResult}) 0)

-- The external checker consumes the same facts and effects through strict JSON.
private def request : RequestJson.Request :=
  ⟨T,program,certificate.map CertificateProducer.signature,[1],0,[]⟩
private def response : RequestJson.Response := ⟨certificate⟩
#guard RequestJson.verify request response
#guard match RequestJson.verifyJson (Lean.toJson request) (Lean.toJson response) with
  | .ok _ => true
  | .error _ => false
-- All nested effect evidence is bounds checked, not only the root header.
private def badEffect : HeapExpressionRules.StepEvidence Nat := .ordinary
  (.node ⟨[],.nul,[0]⟩ (.sub (.trans [999] .subset .subset)) [])
#guard !(RequestJson.validResponse request {response with certificate := certificate.set 0 {certificate[0] with effect := some badEffect}})

#print axioms safe
end Verification.Model.HeapGraphTests
