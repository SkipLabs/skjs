import Verification.Model.Programs.CertificateProducer

namespace Verification.Model.LetTests
open PositiveGraphs PositiveNormalization ProgramTyping ProgramCertificates CertificateProducer

/-- An initializer's effects happen before its body. No body step is allowed
while the initializer is stuck, even when the body itself could allocate. -/
example (h : Heap) : ¬ Step h (.letE (.app .nul .nul) (.alloc .tru)) h' t' := by
  intro hs
  cases hs with
  | letC hs => exact stuck_no_step hs
  | letV hv => simp [isVal] at hv

end Verification.Model.LetTests
