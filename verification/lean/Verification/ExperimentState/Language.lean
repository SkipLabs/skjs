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
  | call (f : Tm) (args : List Tm)
  /-- Evaluate `a`, then substitute its value into `b`. Binding allocates no object. -/
  | letE (a b : Tm)
  | nul
  /-- The value a body produces by completing rather than returning. -/
  | undef
  | tru
  | fls
  /-- An object identity with an optional, immutable invocation descriptor. -/
  | obj (l : Nat) (call : CallCode)
  /-- Allocate one object with immutable call code and initial bag contents `a`.
  Only the initializer is evaluated; code binds its declared parameter count. -/
  | make (call : CallCode) (a : Tm)
  | read (a : Tm)
  | write (a b : Tm)
  | test (k : Tag) (a : Tm)
  | ite (c t e : Tm)
  deriving Repr

/-- Invocation code is not a runtime value. A plain object has no call code. -/
inductive CallCode where
  | absent
  | closure (arity : Nat) (body : Tm)
  deriving Repr
end

/-! Executable structural equality, kept explicit because Lean's deriving
handler does not support nested mutual types such as list-valued applications.
Each recursive comparison visits a strict subterm; no classical decision is used. -/
mutual
def tmDecEq (a b : Tm) : Decidable (a = b) := by
  cases a <;> cases b <;> try (solve | apply isFalse; intro h; cases h)
  case var.var a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.var.injEq])
  case call.call a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := argsDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.call.injEq])
  case letE.letE a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.letE.injEq])
  case nul.nul =>
    exact isTrue rfl
  case undef.undef =>
    exact isTrue rfl
  case tru.tru =>
    exact isTrue rfl
  case fls.fls =>
    exact isTrue rfl
  case obj.obj a0 a1 b0 b1 =>
    haveI : Decidable (a1 = b1) := callCodeDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.obj.injEq])
  case make.make a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := callCodeDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.make.injEq])
  case read.read a0 b0 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.read.injEq])
  case write.write a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.write.injEq])
  case test.test a0 a1 b0 b1 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.test.injEq])
  case ite.ite a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := tmDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.ite.injEq])
termination_by sizeOf a

def callCodeDecEq (a b : CallCode) : Decidable (a = b) := by
  cases a <;> cases b <;> try (solve | apply isFalse; intro h; cases h)
  case absent.absent =>
    exact isTrue rfl
  case closure.closure a0 a1 b0 b1 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [CallCode.closure.injEq])
termination_by sizeOf a
def argsDecEq (a b : List Tm) : Decidable (a = b) := by
  cases a <;> cases b <;> try (solve | apply isFalse; intro h; cases h)
  case nil.nil => exact isTrue rfl
  case cons.cons a as b bs =>
    haveI : Decidable (a = b) := tmDecEq a b
    haveI : Decidable (as = bs) := argsDecEq as bs
    exact decidable_of_iff (a = b ∧ as = bs) (by simp only [List.cons.injEq])
termination_by sizeOf a
end

instance : DecidableEq Tm := tmDecEq
instance : DecidableEq CallCode := callCodeDecEq

#print axioms tmDecEq
#print axioms callCodeDecEq

/-- Unary application is the singleton case of the argument-list constructor. -/
@[match_pattern] abbrev Tm.app (f a : Tm) : Tm := .call f [a]

/-- Plain-object allocation is the absent-descriptor case of `make`. -/
@[match_pattern] abbrev Tm.alloc (a : Tm) : Tm := .make .absent a

/-- Function-object allocation is the closure-descriptor case of `make`. -/
@[match_pattern] abbrev Tm.attach (b a : Tm) : Tm := .make (.closure 1 b) a

/-- Source function creation starts with an empty one-cell property bag. -/
@[match_pattern] abbrev Tm.funE (b : Tm) : Tm := .attach b .nul

/-- Notation for an already allocated function object, used in semantic lemmas. -/
@[match_pattern] abbrev Tm.fn (l : Nat) (b : Tm) : Tm := .obj l (.closure 1 b)

/-- Term induction exposing the body stored inside a call descriptor. -/
@[elab_as_elim] theorem Tm.induct {P : Tm → Prop}
    (var : ∀ i, P (.var i))
    (call : ∀ f args, P f → (∀ a ∈ args, P a) → P (.call f args))
    (letE : ∀ a b, P a → P b → P (.letE a b))
    (nul : P .nul) (undef : P .undef) (tru : P .tru) (fls : P .fls)
    (objAbsent : ∀ l, P (.obj l .absent))
    (objClosure : ∀ l n b, P b → P (.obj l (.closure n b)))
    (attach : ∀ n b a, P b → P a → P (.make (.closure n b) a))
    (alloc : ∀ a, P a → P (.alloc a))
    (read : ∀ a, P a → P (.read a))
    (write : ∀ a b, P a → P b → P (.write a b))
    (test : ∀ k a, P a → P (.test k a))
    (ite : ∀ c a b, P c → P a → P b → P (.ite c a b)) (t : Tm) : P t := by
  apply Tm.rec (motive_1 := P)
    (motive_2 := fun c => match c with | .absent => True | .closure _ b => P b)
    (motive_3 := fun args => ∀ a ∈ args, P a)
    var call letE nul undef tru fls ?_ ?_ read write test ite
    True.intro (fun _ _ h => h) (by simp) (by
      intro a args ha ih v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ha
      · exact ih v hv) t
  · intro l c ih
    cases c with
    | absent => exact objAbsent l
    | closure n b => exact objClosure l n b ih
  · intro c a ihc iha
    cases c with
    | absent => exact alloc a iha
    | closure n b => exact attach n b a ihc iha



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
  | .isFun, .obj _ (.closure _ _) => true
  | _, _ => false

mutual
def subst (j : Nat) (a : Tm) : Tm → Tm
  | .var i => if i == j then a else if j < i then .var (i - 1) else .var i
  | .call f args => .call (subst j a f) (substArgs j a args)
  | .letE x b => .letE (subst j a x) (subst (j + 1) a b)
  | .nul => .nul
  | .undef => .undef
  | .tru => .tru
  | .fls => .fls
  | .obj l .absent => .obj l .absent
  | .obj l (.closure n b) => .obj l (.closure n (subst (j + n) a b))
  | .make (.closure n b) x => .make (.closure n (subst (j + n) a b)) (subst j a x)
  | .alloc x => .alloc (subst j a x)
  | .read x => .read (subst j a x)
  | .write x y => .write (subst j a x) (subst j a y)
  | .test k x => .test k (subst j a x)
  | .ite c x y => .ite (subst j a c) (subst j a x) (subst j a y)

termination_by structural t => t

def substArgs (j : Nat) (a : Tm) : List Tm → List Tm
  | [] => []
  | x :: xs => subst j a x :: substArgs j a xs
termination_by structural xs => xs
end

@[simp] theorem substArgs_eq_map (j : Nat) (a : Tm) (args : List Tm) :
    substArgs j a args = args.map (subst j a) := by
  induction args <;> simp_all [substArgs]

@[simp] theorem subst_app (j : Nat) (a f x : Tm) :
    subst j a (.app f x) = .app (subst j a f) (subst j a x) := rfl

/-- Substitute the highest parameter slots first. All replacements are closed;
no argument is evaluated by binding, and nested body binders remain intact. -/
def bindArgs (d : Nat) : List Tm → Tm → Tm
  | [], t => t
  | a::args, t => subst d a (bindArgs (d + 1) args t)

@[simp] theorem bindArgs_singleton (d : Nat) (a body : Tm) :
    bindArgs d [a] body = subst d a body := rfl

namespace CallArguments

/-- Runtime parameter binding pads missing arguments with undefined and ignores
extra values. Preparation still evaluates the entire actual list first. -/
def parameters : Nat → List Tm → List Tm
  | 0, _ => []
  | n+1, [] => .undef :: parameters n []
  | n+1, a::args => a :: parameters n args

/-- Bind a prepared argument list without evaluating or allocating anything. -/
def bindParameters (arity : Nat) (args : List Tm) (body : Tm) : Tm :=
  bindArgs 0 (parameters arity args) body

end CallArguments

abbrev Heap := List Val

/-! ## One small step, threading the heap -/


inductive Step : Heap → Tm → Heap → Tm → Prop where
  | appL : Step h f h' f' → Step h (.app f a) h' (.app f' a)
  | appR : isVal f = true → Step h a h' a' → Step h (.app f a) h' (.app f a')
  | letC : Step h a h' a' → Step h (.letE a b) h' (.letE a' b)
  | letV : isVal a = true → Step h (.letE a b) h (subst 0 a b)
  /-- Invocation executes the object's stored code in one step. -/
  | callV : (∀ a ∈ args, isVal a = true) →
      Step h (.call (.obj l (.closure n b)) args) h (CallArguments.bindParameters n args b)
  | makeC : Step h a h' a' → Step h (.make c a) h' (.make c a')
  | makeV : isVal v = true → Step h (.make c v) (h ++ [v]) (.obj h.length c)
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


/-- The existing unary beta rule is a specialization of list dispatch. -/
theorem Step.beta (ha : isVal a = true) :
    Step h (.app (.obj l (.closure n b)) a) h (CallArguments.bindParameters n [a] b) :=
  .callV (by simpa using ha)

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
    | callV => exact absurd s obj_no_step
  | appR hv s ih =>
    cases s2 with
    | appL s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | appR _ s' => exact (ih s').imp id (congrArg (Tm.app _ ·))
    | callV hv' => exact absurd s (by intro hs; exact value_no_step (hv' _ (by simp)) hs)
  | letC hs ih =>
    cases s2 with
    | letC hs' => exact (ih hs').imp id (congrArg (Tm.letE · _))
    | letV hv => exact absurd hs (value_no_step hv)
  | letV hv =>
    cases s2 with
    | letC hs => exact absurd hs (value_no_step hv)
    | letV => exact ⟨rfl, rfl⟩
  | callV hv =>
    cases s2 with
    | appL hs => exact absurd hs obj_no_step
    | appR _ hs => exact absurd hs (value_no_step (hv _ (by simp)))
    | callV => exact ⟨rfl, rfl⟩
  | makeC hs ih =>
    cases s2 with
    | makeC hs' => exact (ih hs').imp id (congrArg (Tm.make _))
    | makeV hv => exact absurd hs (value_no_step hv)
  | makeV hv =>
    cases s2 with
    | makeC hs => exact absurd hs (value_no_step hv)
    | makeV => exact ⟨rfl, rfl⟩
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

theorem make_step_inv {c : CallCode} {v : Val} (hv : isVal v = true) {h h' t}
    (hs : Step h (.make c v) h' t) : h' = h ++ [v] ∧ t = .obj h.length c := by
  cases hs with
  | makeC hs => exact False.elim (value_no_step hv hs)
  | makeV => exact ⟨rfl, rfl⟩

theorem beta_inv {b a : Tm} {l : Nat} (ha : isVal a = true) {h h' t}
    (hs : Step h (.app (.obj l (.closure 1 b)) a) h' t) : h' = h ∧ t = subst 0 a b := by
  cases hs with
  | appL hs => cases hs
  | appR _ hs => exact False.elim (value_no_step ha hs)
  | callV => exact ⟨rfl, rfl⟩

/-- Binding a value spends one step and leaves the heap unchanged. -/
theorem let_step_inv {b a : Tm} (ha : isVal a = true) {h h' t}
    (hs : Step h (.letE a b) h' t) : h' = h ∧ t = subst 0 a b := by
  cases hs with
  | letC hs => exact False.elim (value_no_step ha hs)
  | letV => exact ⟨rfl, rfl⟩

theorem read_step_inv {r : Nat} {c : CallCode} {h h' t} (hs : Step h (.read (.obj r c)) h' t) :
    h' = h ∧ h[r]? = some t := by
  cases hs with
  | readC hs => exact False.elim (obj_no_step hs)
  | readV he => exact ⟨rfl, he⟩


end ExperimentState
end Verification
