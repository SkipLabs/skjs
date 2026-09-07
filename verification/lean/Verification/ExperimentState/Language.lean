/-!
# The object language

A design investigation, not part of the verifier. Built so it cannot rot,
imported by nothing.

An untyped call-by-value calculus with a mutable heap: lambda, application, two
constants, and allocate/read/write. Values are terms, so worlds, heaps and the
operational semantics all speak about the same objects.

Substitution is written for *closed* arguments, which is all the semantics ever
substitutes; a general binding discipline is deliberately not attempted here.

The step relation is small-step and total in the sense that matters: a term
that is not a value and cannot step is **stuck**, and the safety predicate in
`Safety.lean` rules that out.
-/
namespace Verification
namespace ExperimentState

/-- Terms. Values are terms too, so worlds and the operational semantics speak
about the same objects. -/
inductive Tm where
  | var (i : Nat)
  | lam (b : Tm)
  | app (f a : Tm)
  | nul
  | tru
  | fls
  | loc (l : Nat)
  | alloc (a : Tm)
  | read (a : Tm)
  | write (a b : Tm)
  deriving Repr, DecidableEq

abbrev Val := Tm

/-! ## Values and substitution -/


def isVal : Tm → Bool
  | .lam _ => true | .nul => true | .tru => true | .fls => true | .loc _ => true
  | _ => false

def subst (j : Nat) (a : Tm) : Tm → Tm
  | .var i => if i == j then a else if j < i then .var (i - 1) else .var i
  | .lam b => .lam (subst (j + 1) a b)
  | .app f x => .app (subst j a f) (subst j a x)
  | .nul => .nul
  | .tru => .tru
  | .fls => .fls
  | .loc l => .loc l
  | .alloc x => .alloc (subst j a x)
  | .read x => .read (subst j a x)
  | .write x y => .write (subst j a x) (subst j a y)

abbrev Heap := List Val

/-! ## One small step, threading the heap -/


inductive Step : Heap → Tm → Heap → Tm → Prop where
  | appL : Step h f h' f' → Step h (.app f a) h' (.app f' a)
  | appR : isVal f = true → Step h a h' a' → Step h (.app f a) h' (.app f a')
  | beta : isVal a = true → Step h (.app (.lam b) a) h (subst 0 a b)
  | allocC : Step h a h' a' → Step h (.alloc a) h' (.alloc a')
  | allocV : isVal v = true → Step h (.alloc v) (h ++ [v]) (.loc h.length)
  | readC : Step h a h' a' → Step h (.read a) h' (.read a')
  | readV : h[l]? = some v → Step h (.read (.loc l)) h v
  | writeC1 : Step h a h' a' → Step h (.write a b) h' (.write a' b)
  | writeC2 : isVal a = true → Step h b h' b' → Step h (.write a b) h' (.write a b')
  | writeV : isVal v = true → l < h.length → Step h (.write (.loc l) v) (h.set l v) .nul

theorem lam_no_step {h b h' t} : ¬ Step h (.lam b) h' t := by intro s; cases s

theorem nul_no_step {h h' t} : ¬ Step h .nul h' t := by intro s; cases s
theorem tru_no_step {h h' t} : ¬ Step h .tru h' t := by intro s; cases s
theorem fls_no_step {h h' t} : ¬ Step h .fls h' t := by intro s; cases s
theorem loc_no_step {h l h' t} : ¬ Step h (.loc l) h' t := by intro s; cases s

/-! ## Divergence

`omegaTm` steps to itself forever. It is the inhabitant of last resort: safe at
every budget, since safety asks for progress and not termination. -/

def delta : Tm := .lam (.app (.var 0) (.var 0))
def omegaTm : Tm := .app delta delta

theorem omega_step (h : Heap) : Step h omegaTm h omegaTm := Step.beta rfl

/-! ### Closed values, and inverting the steps a separating value takes

A value is closed when substitution cannot touch it; the values used to tell two
types apart are closed, so they mean the same thing under every binder. The
inversion lemmas say what a redex *must* do, which is how a proof that a term
is unsafe gets started. -/

def Closed (v : Val) : Prop := ∀ k a, subst k a v = v

/-- Write the argument through a captured reference, then diverge. There is no
runtime type test, and no returned value that could inspect the codomain. -/
def tester (l : Nat) : Tm := .lam (.app (.lam omegaTm) (.write (.loc l) (.var 0)))

/-- A function that gets stuck the moment it is applied. It inhabits an arrow
whose domain is empty, since such an arrow is never applied, and no other. -/
def stuckFn : Tm := .lam (.app .nul .nul)

theorem closed_stuck : Closed stuckFn := by
  intro k a
  simp [stuckFn, subst]

theorem stuck_no_step {h h' t} : ¬ Step h (.app .nul .nul) h' t := by
  intro hs
  cases hs with
  | appL hs => exact nul_no_step hs
  | appR _ hs => exact nul_no_step hs

/-- Write the argument into one cell, then return the contents of another. This
is the value that observes an arrow on both sides at once: the write fails on an
argument the first cell cannot hold, and the result is whatever the second cell
holds — which, since an arrow quantifies over every satisfying heap, an observer
gets to choose. -/
def probe (l r : Nat) : Tm := .lam (.app (.lam (.read (.loc r))) (.write (.loc l) (.var 0)))

theorem closed_probe (l r : Nat) : Closed (probe l r) := by
  intro k a
  simp [probe, subst]

theorem closed_omega : Closed omegaTm := by
  intro k a
  simp [omegaTm, delta, subst]

theorem closed_tester (l : Nat) : Closed (tester l) := by
  intro k a
  simp [tester, subst, omegaTm, delta]

theorem value_no_step {v : Val} (hv : isVal v = true) {h h' t} : ¬ Step h v h' t := by
  intro hs
  cases v <;> simp [isVal] at hv <;> cases hs

theorem beta_inv {b a : Tm} (ha : isVal a = true) {h h' t}
    (hs : Step h (.app (.lam b) a) h' t) : h' = h ∧ t = subst 0 a b := by
  cases hs with
  | appL hs => cases hs
  | appR _ hs => exact False.elim (value_no_step ha hs)
  | beta => exact ⟨rfl, rfl⟩

theorem probe_step_inv {l r : Nat} {v : Val} (hv : isVal v = true) {h h' t}
    (hs : Step h (.app (probe l r) v) h' t) :
    h' = h ∧ t = .app (.lam (.read (.loc r))) (.write (.loc l) v) := by
  cases hs with
  | appL hs => cases hs
  | appR _ hs => exact False.elim (value_no_step hv hs)
  | beta => exact ⟨rfl, rfl⟩

theorem read_step_inv {r : Nat} {h h' t} (hs : Step h (.read (.loc r)) h' t) :
    h' = h ∧ h[r]? = some t := by
  cases hs with
  | readC hs => exact False.elim (loc_no_step hs)
  | readV he => exact ⟨rfl, he⟩

theorem tester_step_inv {l : Nat} {v : Val} (hv : isVal v = true) {h h' t}
    (hs : Step h (.app (tester l) v) h' t) :
    h' = h ∧ t = .app (.lam omegaTm) (.write (.loc l) v) := by
  cases hs with
  | appL hs => cases hs
  | appR _ hs => exact False.elim (value_no_step hv hs)
  | beta => exact ⟨rfl, rfl⟩

theorem write_step_inv {f : Tm} {l : Nat} {v : Val} (hv : isVal v = true) {h h' t}
    (hs : Step h (.app (.lam f) (.write (.loc l) v)) h' t) :
    h' = h.set l v ∧ t = .app (.lam f) .nul ∧ l < h.length := by
  cases hs with
  | appL hs => cases hs
  | beta hv => simp [isVal] at hv
  | appR _ hs =>
    cases hs with
    | writeC1 hs => cases hs
    | writeC2 _ hs => exact False.elim (value_no_step hv hs)
    | writeV _ hlt => exact ⟨rfl, rfl, hlt⟩

end ExperimentState
end Verification
