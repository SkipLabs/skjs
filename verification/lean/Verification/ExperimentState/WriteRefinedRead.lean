import Verification.ExperimentState.HeapObservations

/-! Semantic proof for tests/skjs-incomplete/write-refined-read.ts.
The term is the ordinary let/sequence encoding of the complete source body:
allocate false, write true, read the same location. This is a proof in the
existing calculus using the new observation rules, not a certificate accepted
by the current source checker and not a source-compilation correspondence proof. -/
namespace Verification.ExperimentState.WriteRefinedRead
open HeapObservations

-- Outer binder: cell. Inner binder: unused result of the write; cell shifts to 1.
def body : Tm := .app (.lam (.read (.var 1))) (.write (.var 0) .tru)
def program : Tm := .app (.lam body) (.alloc .fls)

/-- All ambient admissible heaps are allowed; the proof assumes neither an
empty heap nor absence of other aliases elsewhere in it. -/
theorem program_post {n W h} (hw : WorldAdm W) (hh : HeapOk n W h) :
    SafePost (exact .tru) (fun h' v => Observes h' h.length .tru ∧ v = .tru)
      n W h program := by
  apply bind (fun t => .app (.lam body) t) (fun hs => .appR rfl hs)
    n W h (.alloc .fls) hw hh (alloc_observed boolT_adm hw hh rfl (Or.inr rfl))
  intro j hj U hx hu h' v hh' hval hr hp
  have he : v = .loc h.length := hp.2
  subst v
  cases j with
  | zero => trivial
  | succ p =>
    apply beta rfl hu hh'
    change SafePost _ _ p _ h'
      (.app (.lam (.read (.loc h.length))) (.write (.loc h.length) .tru))
    exact write_then_read boolT_adm (WorldAdm_trunc _ hu) (HeapOk_trunc p U h' hh')
      ((refT_adm boolT).down p U _ hr) rfl (Or.inl rfl)

theorem program_safe {n W h} (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (exact .tru) n W h program := erase (program_post hw hh)

/-- Unary null is the semantic wrapper for a source function with no inputs.
The unused argument has no effect on the proved body or return guarantee. -/
theorem function_arrow (n : Nat) (W : WorldT n) :
    arrowT nulT (exact .tru) n W (.lam program) := by
  apply lam_intro _ _ _ (by simp [program,body,Scoped])
  intro j hj U hx hu h hh a ha
  simpa [program,body,subst] using program_safe hu hh

/-- The actual finite execution witnesses termination and the returned value;
program_post establishes safety independently by composition of general rules. -/
theorem program_runs (h : Heap) :
    Steps 5 h program ((h ++ [Tm.fls]).set h.length .tru) .tru := by
  apply Steps.next (.appR rfl (.allocV rfl))
  apply Steps.next (.beta rfl)
  apply Steps.next (.appR rfl (.writeV rfl (by simp)))
  apply Steps.next (.beta rfl)
  exact Steps.next (.readV (by simp [subst])) .refl

#print axioms program_post
#print axioms function_arrow
#print axioms program_runs
end Verification.ExperimentState.WriteRefinedRead
