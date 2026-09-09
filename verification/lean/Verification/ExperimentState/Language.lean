/-!
# The object language

The operational foundation of the stateful type development. It is compiled
and tested, and is the current verifier's language.

An untyped call-by-value calculus with a mutable heap: lambda, application, two
constants, and allocate/read/write. Values are terms, so worlds, heaps and the
operational semantics all speak about the same objects.

Substitution is written for *closed* arguments. `Bindings.lean` proves its
closing-substitution laws; `ProgramTyping.lean` ensures typed positive values
are closed. The untyped step relation itself imposes no scope check.

The step relation is small-step and total in the sense that matters: a term
that is not a value and cannot step is **stuck**, and the safety predicate in
`Safety.lean` rules that out.
-/
namespace Verification
namespace ExperimentState

/-- The shapes a value can have, and so the tests a program can make of one.
There is one per type constructor, which is what a `typeof` in the source
language amounts to. -/
inductive Tag where
  | isNul | isBool | isRef | isFun
  deriving Repr, DecidableEq

/-- Terms. Values are terms too, so worlds and the operational semantics speak
about the same objects. -/
inductive Tm where
  | var (i : Nat)
  | lam (b : Tm)
  | app (f a : Tm)
  | nul
  /-- The value a body produces by completing rather than returning. -/
  | undef
  | tru
  | fls
  | loc (l : Nat)
  | alloc (a : Tm)
  | read (a : Tm)
  | write (a b : Tm)
  | test (k : Tag) (a : Tm)
  | ite (c t e : Tm)
  deriving Repr, DecidableEq

abbrev Val := Tm

/-! ## Values and substitution -/


def isVal : Tm → Bool
  | .lam _ => true | .nul => true | .undef => true | .tru => true
  | .fls => true | .loc _ => true
  | _ => false

/-- What a test of a value answers. A test is total on values: every value has
exactly one shape, which is the fact the shape lemmas of the type semantics
record on the other side. -/
def tagHolds : Tag → Val → Bool
  | .isNul, .nul => true
  | .isBool, .tru => true
  | .isBool, .fls => true
  | .isRef, .loc _ => true
  | .isFun, .lam _ => true
  | _, _ => false

def subst (j : Nat) (a : Tm) : Tm → Tm
  | .var i => if i == j then a else if j < i then .var (i - 1) else .var i
  | .lam b => .lam (subst (j + 1) a b)
  | .app f x => .app (subst j a f) (subst j a x)
  | .nul => .nul
  | .undef => .undef
  | .tru => .tru
  | .fls => .fls
  | .loc l => .loc l
  | .alloc x => .alloc (subst j a x)
  | .read x => .read (subst j a x)
  | .write x y => .write (subst j a x) (subst j a y)
  | .test k x => .test k (subst j a x)
  | .ite c x y => .ite (subst j a c) (subst j a x) (subst j a y)

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
  | testC : Step h a h' a' → Step h (.test k a) h' (.test k a')
  | testV : isVal v = true →
      Step h (.test k v) h (if tagHolds k v then .tru else .fls)
  | iteC : Step h c h' c' → Step h (.ite c t e) h' (.ite c' t e)
  | iteT : Step h (.ite .tru t e) h t
  | iteF : Step h (.ite .fls t e) h e

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

/-! ### Closed values and operational inversion lemmas -/

def Closed (v : Val) : Prop := ∀ k a, subst k a v = v

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

theorem closed_omega : Closed omegaTm := by
  intro k a
  simp [omegaTm, delta, subst]

theorem value_no_step {v : Val} (hv : isVal v = true) {h h' t} : ¬ Step h v h' t := by
  intro hs
  cases v <;> simp [isVal] at hv <;> cases hs

theorem beta_inv {b a : Tm} (ha : isVal a = true) {h h' t}
    (hs : Step h (.app (.lam b) a) h' t) : h' = h ∧ t = subst 0 a b := by
  cases hs with
  | appL hs => cases hs
  | appR _ hs => exact False.elim (value_no_step ha hs)
  | beta => exact ⟨rfl, rfl⟩

/-- **Evaluation is deterministic.** One term in one heap has at most one next
state. Nothing in the safety definition says so — it quantifies existentially
over the world a step lands in — so this has to be proved, and it is what lets
two independent runs of the same program be compared. -/
theorem Step_det {h t h1 t1 h2 t2} (s1 : Step h t h1 t1) (s2 : Step h t h2 t2) :
    h1 = h2 ∧ t1 = t2 := by
  induction s1 generalizing h2 t2 with
  | appL s ih =>
    cases s2 with
    | appL s' => exact (ih s').imp id (congrArg (Tm.app · _))
    | appR hv s' => exact absurd s (by intro hs; exact value_no_step hv hs)
    | beta => exact absurd s lam_no_step
  | appR hv s ih =>
    cases s2 with
    | appL s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | appR _ s' => exact (ih s').imp id (congrArg (Tm.app _ ·))
    | beta hv' => exact absurd s (by intro hs; exact value_no_step hv' hs)
  | beta hv =>
    cases s2 with
    | appL s' => exact absurd s' lam_no_step
    | appR _ s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | beta => exact ⟨rfl, rfl⟩
  | allocC s ih =>
    cases s2 with
    | allocC s' => exact (ih s').imp id (congrArg Tm.alloc)
    | allocV hv => exact absurd s (by intro hs; exact value_no_step hv hs)
  | allocV hv =>
    cases s2 with
    | allocC s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | allocV => exact ⟨rfl, rfl⟩
  | readC s ih =>
    cases s2 with
    | readC s' => exact (ih s').imp id (congrArg Tm.read)
    | readV _ => exact absurd s loc_no_step
  | readV he =>
    cases s2 with
    | readC s' => exact absurd s' loc_no_step
    | readV he' => exact ⟨rfl, Option.some.inj (he.symm.trans he')⟩
  | writeC1 s ih =>
    cases s2 with
    | writeC1 s' => exact (ih s').imp id (congrArg (Tm.write · _))
    | writeC2 hv s' => exact absurd s (by intro hs; exact value_no_step hv hs)
    | writeV _ _ => exact absurd s loc_no_step
  | writeC2 hv s ih =>
    cases s2 with
    | writeC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | writeC2 _ s' => exact (ih s').imp id (congrArg (Tm.write _ ·))
    | writeV hv' _ => exact absurd s (by intro hs; exact value_no_step hv' hs)
  | writeV hv hlt =>
    cases s2 with
    | writeC1 s' => exact absurd s' loc_no_step
    | writeC2 _ s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | writeV _ _ => exact ⟨rfl, rfl⟩
  | testC s ih =>
    cases s2 with
    | testC s' => exact (ih s').imp id (congrArg (Tm.test _))
    | testV hv => exact absurd s (by intro hs; exact value_no_step hv hs)
  | testV hv =>
    cases s2 with
    | testC s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | testV _ => exact ⟨rfl, rfl⟩
  | iteC s ih =>
    cases s2 with
    | iteC s' => exact (ih s').imp id (congrArg (Tm.ite · _ _))
    | iteT => exact absurd s tru_no_step
    | iteF => exact absurd s fls_no_step
  | iteT =>
    cases s2 with
    | iteC s' => exact absurd s' tru_no_step
    | iteT => exact ⟨rfl, rfl⟩
  | iteF =>
    cases s2 with
    | iteC s' => exact absurd s' fls_no_step
    | iteF => exact ⟨rfl, rfl⟩

theorem alloc_step_inv {v : Val} (hv : isVal v = true) {h h' t}
    (hs : Step h (.alloc v) h' t) : h' = h ++ [v] ∧ t = .loc h.length := by
  cases hs with
  | allocC hs => exact False.elim (value_no_step hv hs)
  | allocV => exact ⟨rfl, rfl⟩

theorem read_step_inv {r : Nat} {h h' t} (hs : Step h (.read (.loc r)) h' t) :
    h' = h ∧ h[r]? = some t := by
  cases hs with
  | readC hs => exact False.elim (loc_no_step hs)
  | readV he => exact ⟨rfl, he⟩

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
