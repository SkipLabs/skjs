import Verification.ExperimentState.DirectProof

/-! Explicit binding is nonallocating, scopes only its body, and has its own
certificate rule. These examples need no function label in the type graph. -/
namespace Verification.ExperimentState.LetTests
open PositiveGraphs PositiveNormalization ProgramTyping ProgramCertificates CertificateProducer

private def G : NormalGraph Nat := fun _ => [.bool]
private def term : Tm := .letE .tru (.var 0)
private def evidence : Evidence Nat :=
  .node ⟨[],term,[0]⟩ .letE
    [.node ⟨[],.tru,[0]⟩ .tru [], .node ⟨[[0]],.var 0,[0]⟩ .var []]

#guard check G term [0] evidence
#guard (expressionWith G [[0]] [] 3 [] term [0]).isSome

/- The consumer no longer accepts lambda application as a binding certificate. -/
#guard !checkTree G (.node ⟨[],.app (.lam (.var 0)) .tru,[0]⟩ .letE
  [.node ⟨[],.tru,[0]⟩ .tru [], .node ⟨[[0]],.var 0,[0]⟩ .var []])

/- The producer cannot use the removed shortcut to avoid a function type. -/
#guard !(expressionWith G [[0]] [] 3 [] (.app (.lam (.var 0)) .tru) [0]).isSome

/- The binder scopes the body, not its initializer. -/
#guard checkScope 0 term
#guard !checkScope 0 (.letE (.var 0) (.var 0))
#guard !checkScope 0 (.letE .tru (.var 1))

/-- Once its initializer is a value, binding cannot change the heap. -/
theorem binding_no_allocation {h h' t'} (hs : Step h term h' t') :
    h' = h ∧ t' = .tru :=
  let_step_inv rfl hs

/-- An initializer's effects happen before its body. No body step is allowed
while the initializer is stuck, even when the body itself could allocate. -/
example (h : Heap) : ¬ Step h (.letE (.app .nul .nul) (.alloc .tru)) h' t' := by
  intro hs
  cases hs with
  | letC hs => exact stuck_no_step hs
  | letV hv => simp [isVal] at hv

example : Step [.tru] (.letE (.write (.obj 0 .nul) .fls) (.read (.obj 0 .nul)))
    [.fls] (.letE .nul (.read (.obj 0 .nul))) :=
  .letC (.writeV rfl (by decide))

/-- Closing substitution respects the additional binder only in the body. -/
example : instantiate 0 (fun _ => .fls) (.letE (.var 0) (.var 1)) =
    .letE .fls .fls := by simp [instantiate]

theorem accepted_binding_safe (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (PositiveRules.meaning G [0]) n W h term :=
  (check_sound (by cbv : check G term [0] evidence = true)).2.closed_safe
    (by simp [term, Scoped]) n W h hw hh

#print axioms binding_no_allocation
#print axioms accepted_binding_safe

end Verification.ExperimentState.LetTests
