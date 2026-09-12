import Verification.ExperimentState.GraphCoherence
import Verification.ExperimentState.CertificateProducerTests

namespace Verification.ExperimentState.CoherenceTests
open ObjectCoherence GraphCoherence ControlFlow ProgramCertificates

/-- Matching identities cannot acquire different callability or different code. -/
example {D l b} (h : Names D (.obj l .absent)) (h' : Names D (.fn l b)) : False := by
  have he := descriptor_unique h h'
  cases he

example {D l b b'} (h : Names D (.fn l b)) (h' : Names D (.fn l b')) : b = b' := by
  have he := descriptor_unique h h'
  cases he
  rfl

/-- Scope at the enclosing binder is insufficient for an existing object.
Its descriptor must already be closed, so substitution cannot change it. -/
example : Scoped 1 (.fn 0 (.var 1)) := by simp [Scoped]
example (D : Registry) : ¬ Names D (.fn 0 (.var 1)) := by simp [Names, Scoped]

/-- An object hidden inside captured code is checked against the same registry. -/
example : ¬ Names [.absent, .closure (.fn 0 (.var 0))] (.fn 1 (.fn 0 (.var 0))) := by
  simp [Names]

/- Source functions may capture variables, but may not spell allocated identities. -/
#guard sourceTerm (.funE (.var 1))
#guard !sourceTerm (.funE (.obj 0 .absent))
#guard !sourceTerm (.ite .tru .nul (.obj 0 .absent))

/-- Empty overloads have no body typing premises. The graph consumer must still
reject forged identities in their bodies, independently of that typing rule. -/
private def G : PositiveGraphs.NormalGraph Nat := fun _ => [.arrs []]
private def forged : Tm := .funE (.obj 0 .absent)
private def forgedEvidence : Evidence Nat := .node ⟨[],forged,[0]⟩ .funE []
private def forgedNode : Node := ⟨forged,.ret⟩
private def forgedCertificate : ControlFlow.Certificate Nat :=
  [{expression := forgedEvidence, edges := []}]

#guard checkTree G forgedEvidence
#guard checkScope 0 forged
#guard checkNode G [0] [forgedNode] forgedCertificate forgedNode forgedCertificate[0]
#guard !checkClosed G [0] [forgedNode] forgedCertificate 0

/-- The maintained producer's captured closure, alias write, and mapped slots
satisfy coherence at every finite prefix, without a second typing derivation. -/
theorem mapped_coherent {k h s}
    (run : Execution CertificateProducerTests.mapped k [] (.at 0 (fun _ => .nul)) h s) :
    ∃ D, ObjectCoherence.HeapOk D h ∧ StateCoherent D s := by
  apply accepted_closed_coherent (G := ProgramTypingTests.G)
    (R := [1]) (C := CertificateProducerTests.mappedCertificate) _ run
  have hc := CertificateProducerTests.mapped_accepted
  simp only [CertificateProducer.accept, Bool.and_eq_true] at hc
  exact hc.2

example : ∃ D, ObjectCoherence.HeapOk D [.fls,.nul] ∧ StateCoherent D (.done .fls) :=
  mapped_coherent CertificateProducerTests.mapped_returns_false

/-- Capturing an allocated object preserves its registered descriptor. -/
private def captured : Tm := .read (.obj 0 .absent)
private def initial : Registry := [.absent]
private theorem initial_ok : ObjectCoherence.HeapOk initial [.tru] := by
  simp [ObjectCoherence.HeapOk,initial,TermOk,Scoped,Names,isVal]

example : ∃ D, Extends initial D ∧ ObjectCoherence.HeapOk D [.tru,.nul] ∧
    TermOk D (.fn 1 captured) :=
  step_preserves (.makeV rfl : Step [.tru] (.funE captured) [.tru,.nul] (.fn 1 captured))
    initial initial_ok (by simp [TermOk,Scoped,Names,captured,initial])

/-- A write can create a heap cycle through captured code while retaining both
identities' descriptors. The invariant does not forbid mutable heap cycles. -/
example : ∃ E, Extends [.absent,.closure captured] E ∧
    ObjectCoherence.HeapOk E [.fn 1 captured,.fn 1 captured] ∧ TermOk E .nul :=
  step_preserves (.writeV rfl (by decide) :
    Step [.tru,.fn 1 captured] (.write (.obj 0 .absent) (.fn 1 captured))
      [.fn 1 captured,.fn 1 captured] .nul)
    [.absent,.closure captured]
    (by simp [ObjectCoherence.HeapOk,TermOk,Scoped,Names,isVal,captured])
    (by simp [TermOk,Scoped,Names,captured])

#print axioms mapped_coherent
end Verification.ExperimentState.CoherenceTests
