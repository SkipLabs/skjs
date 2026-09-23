import Verification.Model.Source.SourceTypes
import Verification.Model.Source.RequestJson

/-! A Boolean read, copied through a temporary, refines its cell on each
branch. The independent graph checker validates the read relation and transfer.
No current-content fact is assumed at the function's external entry. -/
set_option maxRecDepth 65536
namespace Verification.Model.HeapGuardTests
open ProgramTyping ProgramCertificates ControlFlow HeapKnowledge HeapExpressionRules
private def T : SourceTypes.Table := SourceTypes.initial ++ [[.refs [(valueField, [1,2])] [] []]]
private def G := SourceTypes.graph T
private def R : List HeapFacts.Atom := [.tru,.fls]
private def empty : Knowledge := ⟨[],[],[]⟩
private def leaf (Γ : List (List Nat)) (t : Tm) (A : List Nat) (r : Rule Nat) : Evidence Nat :=
  .node ⟨Γ,t,A⟩ r []
private def allocProof : Evidence Nat := .node ⟨[[1,2]],.alloc (.var 0),[4]⟩ .alloc
  [leaf [[1,2]] (.var 0) [1,2] .var]
private def allocated := allocOutput empty [(valueField, R)]
private def readResult := readOutput allocated 0 valueField R
private def copyProof := leaf [[1,2],[4],[1,2]] (.var 0) [1,2] .var
private def copied := copy readResult 0
private def yes : Knowledge := ⟨[⟨0,[.tru],valueField⟩],[],[]⟩
private def no : Knowledge := ⟨[⟨0,[.fls],valueField⟩],[],[]⟩

def program : Program :=
  [⟨.alloc (.var 0),.bind 1⟩,⟨.read (.var 0),.bind 2⟩,
   ⟨.var 0,.branchBind ⟨3,some [2]⟩ ⟨4,some [2]⟩⟩,
   ⟨.read (.var 0),.bind ⟨5,some [0]⟩⟩,
   ⟨.read (.var 0),.bind ⟨5,some [0]⟩⟩,⟨.var 0,.ret⟩]

def certificate : ControlFlow.Certificate Nat :=
  [{expression := allocProof, edges := [[.subset,.subset]],
    effect := some (.allocated allocProof), output := allocated},
   {expression := leaf [[4],[1,2]] (.read (.var 0)) [1,2] .read,
    edges := [[.subset,.subset,.subset]], knowledge := allocated,
    effect := some (.observedRead 0 R), output := readResult},
   {expression := copyProof, edges := [[.subset],[.subset]], knowledge := readResult,
    effect := some (.pure copyProof), output := copied},
   {expression := leaf [[4]] (.read (.var 0)) [1] .read, edges := [[.subset]],
    knowledge := yes, effect := some (.observedRead 0 [.tru]), output := readOutput yes 0 valueField [.tru]},
   {expression := leaf [[4]] (.read (.var 0)) [2] .read, edges := [[.subset]],
    knowledge := no, effect := some (.observedRead 0 [.fls]), output := readOutput no 0 valueField [.fls]},
   {expression := leaf [[1,2]] (.var 0) [1,2] .var, edges := []}]

#guard checkEntry G [1,2] program certificate 0 [[1,2]]
theorem checked : checkEntry G [1,2] program certificate 0 [[1,2]] = true := by decide +kernel

theorem safe (n W h ρ) (he : EnvOk G [[1,2]] ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafeGraph program (PositiveRules.meaning G [1,2]) n W h (.at 0 ρ) :=
  accepted_inputs_safe checked n W h ρ he hw hh

-- A Boolean snapshot is insufficient after a call has discarded its read link.
#guard (ordinaryOutput readResult).links == []
#guard !(HeapKnowledge.check (observeBoolean (ordinaryOutput readResult) 1 true) yes (some [2]))
-- Writes discard the old relation even when the immutable value remains true.
#guard (writeOutput readResult 1 valueField [.fls]).links == []
#guard !(HeapKnowledge.check (observeBoolean (writeOutput readResult 1 valueField [.fls]) 1 true) yes (some [2]))
-- Without a checked read link, the broad cell fact cannot justify either branch.
#guard !(HeapKnowledge.check (observeBoolean {copied with links := []} 0 true) yes (some [2]))
#guard !(checkEntry G [1,2] program (certificate.set 3 {certificate[3] with knowledge := no}) 0 [[1,2]])

-- The untrusted producer discovers the same proof from ordinary point types.
#guard (CertificateProducer.produce G (List.range 11) 8 [1,2] program
  (certificate.map CertificateProducer.signature) 0 [] [[1,2]]).isOk

#print axioms safe
end Verification.Model.HeapGuardTests
