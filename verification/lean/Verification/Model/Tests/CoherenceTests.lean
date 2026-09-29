import Verification.Model.Semantics.GraphCoherence

namespace Verification.Model.CoherenceTests
open ObjectCoherence GraphCoherence ControlFlow ProgramCertificates

/-- Code of one node returning its capture, frame slot 2, past the receiver
and the parameter. -/
private def code (caps : List Tm) : CallCode := .graph 1 [.var 2] [(.ret, none)] 0 caps

/-- Matching identities cannot acquire different callability or different code. -/
example {D l} (h : Names D (.obj l .absent)) (h' : Names D (.obj l (code []))) : False := by
  have he := descriptor_unique (l := l) (by simp [locs]) h h'
  cases he

example {D l c c'} (h : Names D (.obj l (code [c]))) (h' : Names D (.obj l (code [c']))) :
    c = c' := by
  have he := descriptor_unique (l := l) (by simp [locs]) h h'
  simpa [code] using he

/-- Scope at the enclosing binder is insufficient for an existing object.
Its captures must already be closed, so substitution cannot change them. -/
example : Scoped 1 (.obj 0 (code [.var 0])) := by simp [Scoped, code]
example (D : Registry) : ¬ Names D (.obj 0 (code [.var 0])) := by simp [Names, Scoped, code]

/-- An object captured by code is checked against the same registry. -/
example : ¬ Names [.absent, code [.obj 0 (code [])]] (.obj 1 (code [.obj 0 (code [])])) := by
  simp [Names, locs, code]

/- Native call lists must not hide malformed syntax after the first argument.
These check syntax traversal; non-singleton source calls remain gated. -/
#guard !checkScope 0 (.call .nul [.tru, .var 0])
#guard !sourceTerm (.call .nul [.tru, .obj 0 .absent])

/- Source functions may capture variables, but may not spell allocated identities. -/
#guard sourceTerm (.makeFn (code [.var 1]) .nul)
#guard !sourceTerm (.makeFn (code [.obj 0 .absent]) .nul)
#guard !sourceTerm (.ite .tru .nul (.obj 0 .absent))

/-- Empty overloads name no code of the table. The graph consumer must still
reject forged identities in the code's nodes, independently of that typing rule. -/
private def G : PositiveGraphs.NormalGraph Nat := .ofRows fun _ => [.arrs [] []]
private def forged : Tm := .makeFn (.graph 1 [.obj 0 .absent] [(.ret, none)] 0 []) .nul
private def forgedEvidence : Evidence Nat := .node ⟨[],forged,[0]⟩ (.funGraph []) []
private def forgedNode : Node := ⟨forged,.ret,none⟩
private def forgedCertificate : ControlFlow.Certificate Nat :=
  [{expression := forgedEvidence, edges := []}]

#guard checkTree G forgedEvidence
#guard checkScope 0 forged
#guard checkNode G [0] [forgedNode] forgedCertificate forgedNode forgedCertificate[0]
#guard !checkClosed G [0] [forgedNode] forgedCertificate 0

/-- Capturing an allocated object preserves its registered descriptor. -/
private def captured : Tm := .read (.obj 0 .absent)
private def initial : Registry := [.absent]
private theorem initial_ok : ObjectCoherence.HeapOk initial [.tru] := by
  simp [ObjectCoherence.HeapOk,initial,TermOk,Scoped,Names,locs,isVal]

example : ∃ D, Extends initial D ∧ ObjectCoherence.HeapOk D [.tru,.nul] ∧
    TermOk D (.fnObj 1 (code [captured])) :=
  step_preserves (.makeFnV rfl : Step [.tru] (.makeFn (code [captured]) .nul) [.tru,.nul]
      (.fnObj 1 (code [captured])))
    initial initial_ok (by simp [TermOk,Scoped,Names,locs,captured,initial,code])

/-- A write can create a heap cycle through captured code while retaining both
identities' descriptors. The invariant does not forbid mutable heap cycles. -/
example : ∃ E, Extends [.absent,code [captured]] E ∧
    ObjectCoherence.HeapOk E [.obj 1 (code [captured]),.obj 1 (code [captured])] ∧ TermOk E .nul :=
  step_preserves (.writeV rfl (by decide) :
    Step [.tru,.obj 1 (code [captured])] (.write (.obj 0 .absent) (.obj 1 (code [captured])))
      [.obj 1 (code [captured]),.obj 1 (code [captured])] .nul)
    [.absent,code [captured]]
    (by simp [ObjectCoherence.HeapOk,TermOk,Scoped,Names,locs,isVal,captured,code])
    (by simp [TermOk,Scoped,Names,locs,captured,code])

end Verification.Model.CoherenceTests
