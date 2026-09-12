/-!
# The object language

The operational foundation of the stateful type development. It is compiled
and tested, and is the current verifier's language.

An untyped call-by-value calculus with a mutable heap: closures, application,
explicit binding, primitive values, and object allocation/read/write. Values are terms, so worlds, heaps and the
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
Nullishness groups null and undefined for source coalescing; the other tests
distinguish individual runtime shapes. -/
inductive Tag where
  | isNul | isBool | isRef | isFun | isUndef | isNullish
  deriving Repr, DecidableEq

mutual
/-- Terms. Values are terms too, so worlds and the operational semantics speak
about the same objects. -/
inductive Tm where
  | var (i : Nat)
  | app (f a : Tm)
  /-- Evaluate `a`, then substitute its value into `b`. Binding allocates no object. -/
  | letE (a b : Tm)
  | nul
  /-- The value a body produces by completing rather than returning. -/
  | undef
  | tru
  | fls
  /-- An object identity with an optional, immutable invocation descriptor. -/
  | obj (l : Nat) (call : CallCode)
  /-- Allocate a function object with body `b` and initial bag contents `a`.
  The body is code under one binder, not a term evaluated at creation. -/
  | attach (b a : Tm)
  | alloc (a : Tm)
  | read (a : Tm)
  | write (a b : Tm)
  | test (k : Tag) (a : Tm)
  | ite (c t e : Tm)
  deriving Repr, DecidableEq

/-- Invocation code is not a runtime value. A plain object has no call code. -/
inductive CallCode where
  | absent
  | closure (body : Tm)
  deriving Repr, DecidableEq
end

/-- Source function creation starts with an empty one-cell property bag. -/
@[match_pattern] abbrev Tm.funE (b : Tm) : Tm := .attach b .nul

/-- Notation for an already allocated function object, used in semantic lemmas. -/
@[match_pattern] abbrev Tm.fn (l : Nat) (b : Tm) : Tm := .obj l (.closure b)

/-- Term induction exposing the body stored inside a call descriptor. -/
@[elab_as_elim] theorem Tm.induct {P : Tm → Prop}
    (var : ∀ i, P (.var i))
    (app : ∀ f a, P f → P a → P (.app f a))
    (letE : ∀ a b, P a → P b → P (.letE a b))
    (nul : P .nul) (undef : P .undef) (tru : P .tru) (fls : P .fls)
    (objAbsent : ∀ l, P (.obj l .absent))
    (objClosure : ∀ l b, P b → P (.obj l (.closure b)))
    (attach : ∀ b a, P b → P a → P (.attach b a))
    (alloc : ∀ a, P a → P (.alloc a))
    (read : ∀ a, P a → P (.read a))
    (write : ∀ a b, P a → P b → P (.write a b))
    (test : ∀ k a, P a → P (.test k a))
    (ite : ∀ c a b, P c → P a → P b → P (.ite c a b)) (t : Tm) : P t := by
  apply Tm.rec (motive_1 := P)
    (motive_2 := fun c => match c with | .absent => True | .closure b => P b)
    var app letE nul undef tru fls ?_ attach alloc read write test ite
    True.intro (fun _ h => h) t
  intro l c ih
  cases c with
  | absent => exact objAbsent l
  | closure b => exact objClosure l b ih



abbrev Val := Tm

/-! ## Values and substitution -/


def isVal : Tm → Bool
  | .nul | .undef | .tru | .fls | .obj .. => true
  | _ => false

/-- What a test of a value answers. A test is total on values: every value has
exactly one shape, which is the fact the shape lemmas of the type semantics
record on the other side. -/
def tagHolds : Tag → Val → Bool
  | .isNul, .nul => true
  | .isUndef, .undef => true
  | .isNullish, .nul | .isNullish, .undef => true
  | .isBool, .tru => true
  | .isBool, .fls => true
  | .isRef, .obj _ .absent => true
  | .isFun, .obj _ (.closure _) => true
  | _, _ => false

def subst (j : Nat) (a : Tm) : Tm → Tm
  | .var i => if i == j then a else if j < i then .var (i - 1) else .var i
  | .app f x => .app (subst j a f) (subst j a x)
  | .letE x b => .letE (subst j a x) (subst (j + 1) a b)
  | .nul => .nul
  | .undef => .undef
  | .tru => .tru
  | .fls => .fls
  | .obj l .absent => .obj l .absent
  | .obj l (.closure b) => .obj l (.closure (subst (j + 1) a b))
  | .attach b x => .attach (subst (j + 1) a b) (subst j a x)
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
  | letC : Step h a h' a' → Step h (.letE a b) h' (.letE a' b)
  | letV : isVal a = true → Step h (.letE a b) h (subst 0 a b)
  /-- Invocation executes the object's stored code in one step. -/
  | beta : isVal a = true → Step h (.app (.obj l (.closure b)) a) h (subst 0 a b)
  | attachC : Step h a h' a' → Step h (.attach b a) h' (.attach b a')
  | attachV : isVal v = true → Step h (.attach b v) (h ++ [v]) (.obj h.length (.closure b))
  | allocC : Step h a h' a' → Step h (.alloc a) h' (.alloc a')
  | allocV : isVal v = true → Step h (.alloc v) (h ++ [v]) (.obj h.length .absent)
  | readC : Step h a h' a' → Step h (.read a) h' (.read a')
  /-- Reading and writing an object go to its bag, whatever its code. -/
  | readV : h[l]? = some v → Step h (.read (.obj l c)) h v
  | writeC1 : Step h a h' a' → Step h (.write a b) h' (.write a' b)
  | writeC2 : isVal a = true → Step h b h' b' → Step h (.write a b) h' (.write a b')
  | writeV : isVal v = true → l < h.length → Step h (.write (.obj l c) v) (h.set l v) .nul
  | testC : Step h a h' a' → Step h (.test k a) h' (.test k a')
  | testV : isVal v = true →
      Step h (.test k v) h (if tagHolds k v then .tru else .fls)
  | iteC : Step h c h' c' → Step h (.ite c t e) h' (.ite c' t e)
  | iteT : Step h (.ite .tru t e) h t
  | iteF : Step h (.ite .fls t e) h e


theorem nul_no_step {h h' t} : ¬ Step h .nul h' t := by intro s; cases s
theorem tru_no_step {h h' t} : ¬ Step h .tru h' t := by intro s; cases s
theorem fls_no_step {h h' t} : ¬ Step h .fls h' t := by intro s; cases s
theorem obj_no_step {h l c h' t} : ¬ Step h (.obj l c) h' t := by intro s; cases s

/-! ## Divergence

`omegaTm` steps to itself forever. It is the inhabitant of last resort: safe at
every budget, since safety asks for progress and not termination. -/

def delta : Tm := .fn 0 (.app (.var 0) (.var 0))
def omegaTm : Tm := .app delta delta

theorem omega_step (h : Heap) : Step h omegaTm h omegaTm := Step.beta rfl

/-! ### Closed values and operational inversion lemmas -/

def Closed (v : Val) : Prop := ∀ k a, subst k a v = v

/-- A function that gets stuck the moment it is applied. It inhabits an arrow
whose domain is empty, since such an arrow is never applied, and no other. -/
def stuckFn : Tm := .fn 0 (.app .nul .nul)

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
    | beta => exact absurd s obj_no_step
  | appR hv s ih =>
    cases s2 with
    | appL s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | appR _ s' => exact (ih s').imp id (congrArg (Tm.app _ ·))
    | beta hv' => exact absurd s (by intro hs; exact value_no_step hv' hs)
  | letC hs ih =>
    cases s2 with
    | letC hs' => exact (ih hs').imp id (congrArg (Tm.letE · _))
    | letV hv => exact absurd hs (value_no_step hv)
  | letV hv =>
    cases s2 with
    | letC hs => exact absurd hs (value_no_step hv)
    | letV => exact ⟨rfl, rfl⟩
  | beta hv =>
    cases s2 with
    | appL hs => exact absurd hs obj_no_step
    | appR _ hs => exact absurd hs (value_no_step hv)
    | beta => exact ⟨rfl, rfl⟩
  | attachC hs ih =>
    cases s2 with
    | attachC hs' => exact (ih hs').imp id (congrArg (Tm.attach _))
    | attachV hv => exact absurd hs (value_no_step hv)
  | attachV hv =>
    cases s2 with
    | attachC hs => exact absurd hs (value_no_step hv)
    | attachV => exact ⟨rfl, rfl⟩
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
    | readV _ => exact absurd s obj_no_step
  | readV he =>
    cases s2 with
    | readC s' => exact absurd s' obj_no_step
    | readV he' => exact ⟨rfl, Option.some.inj (he.symm.trans he')⟩
  | writeC1 s ih =>
    cases s2 with
    | writeC1 s' => exact (ih s').imp id (congrArg (Tm.write · _))
    | writeC2 hv s' => exact absurd s (by intro hs; exact value_no_step hv hs)
    | writeV _ _ => exact absurd s obj_no_step
  | writeC2 hv s ih =>
    cases s2 with
    | writeC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | writeC2 _ s' => exact (ih s').imp id (congrArg (Tm.write _ ·))
    | writeV hv' _ => exact absurd s (by intro hs; exact value_no_step hv' hs)
  | writeV hv hlt =>
    cases s2 with
    | writeC1 s' => exact absurd s' obj_no_step
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
    (hs : Step h (.alloc v) h' t) : h' = h ++ [v] ∧ t = .obj h.length .absent := by
  cases hs with
  | allocC hs => exact False.elim (value_no_step hv hs)
  | allocV => exact ⟨rfl, rfl⟩

theorem beta_inv {b a : Tm} {l : Nat} (ha : isVal a = true) {h h' t}
    (hs : Step h (.app (.obj l (.closure b)) a) h' t) : h' = h ∧ t = subst 0 a b := by
  cases hs with
  | appL hs => cases hs
  | appR _ hs => exact False.elim (value_no_step ha hs)
  | beta => exact ⟨rfl, rfl⟩

/-- Binding a value spends one step and leaves the heap unchanged. -/
theorem let_step_inv {b a : Tm} (ha : isVal a = true) {h h' t}
    (hs : Step h (.letE a b) h' t) : h' = h ∧ t = subst 0 a b := by
  cases hs with
  | letC hs => exact False.elim (value_no_step ha hs)
  | letV => exact ⟨rfl, rfl⟩

theorem attach_step_inv {b : Tm} {v : Val} (hv : isVal v = true) {h h' t}
    (hs : Step h (.attach b v) h' t) : h' = h ++ [v] ∧ t = .obj h.length (.closure b) := by
  cases hs with
  | attachC hs => exact False.elim (value_no_step hv hs)
  | attachV => exact ⟨rfl, rfl⟩

theorem read_step_inv {r : Nat} {c : CallCode} {h h' t} (hs : Step h (.read (.obj r c)) h' t) :
    h' = h ∧ h[r]? = some t := by
  cases hs with
  | readC hs => exact False.elim (obj_no_step hs)
  | readV he => exact ⟨rfl, he⟩


end ExperimentState
end Verification
