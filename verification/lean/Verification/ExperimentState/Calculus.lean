import Lean.Data.Json

/-!
# The object language

The operational foundation of the stateful type development. It is compiled
and tested, and is the current verifier's language.

An untyped call-by-value calculus with a mutable heap: closures, application,
explicit binding, primitive values, and object allocation/read/write. Values are terms, so worlds, heaps and the
operational semantics all speak about the same objects.

An object is a finite map from field names to heap locations, fixed at
allocation. Each location still holds one value under one contract, so worlds,
heap satisfaction and the write rule are unchanged; what a field name buys is
that one object can own several of them, and that two contracts naming
different fields of the same object constrain different locations.

Substitution is written for *closed* arguments. `Bindings.lean` proves its
closing-substitution laws; `ProgramTyping.lean` ensures typed positive values
are closed. The untyped step relation itself imposes no scope check.

The step relation is small-step and total in the sense that matters: a term
that is not a value and cannot step is **stuck**, and the safety predicate in
`Safety.lean` rules that out.
-/
namespace Verification
namespace ExperimentState

/-- The field every single-cell object of the earlier development carries. A
one-field object named this way is what `Tm.obj`, `Tm.read` and `Tm.write`
abbreviate, so every rule and proof written before field names keeps its
meaning. -/
def valueField : String := "value"

/-- The shapes a value can have, and so the tests a program can make of one.
Nullishness groups null and undefined for source coalescing; the other tests
distinguish individual runtime shapes. -/
inductive Tag where
  | isNul | isBool | isRef | isFun | isUndef | isNullish | isNum | isStr
  | numEq (bits : UInt64)
  | strEq (value : String)
  deriving Repr, DecidableEq

/-- Binary arithmetic on two numbers: the IEEE-754 double operation JavaScript
performs on two Numbers. The fragment applies one to nothing else. -/
inductive Arith where
  | add | sub | mul | div
  deriving Repr, DecidableEq, BEq

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
  /-- A number, carried as the bit pattern of the double it denotes, which is
  the identity `numBits` below assigns a numeric literal. Equality tests
  inspect these bits and `arith` combines them as doubles; otherwise a number
  is opaque: it is bound, passed, stored and shape-tested. Two patterns
  that denote the same double are equal, so singletons cannot be confused; two
  that denote it differently would be distinct singletons, which costs
  completeness and never soundness. -/
  | num (bits : UInt64)
  /-- A string, carried as itself. Like a number it is opaque: bound, passed,
  stored, shape-tested and compared for equality, never computed with. -/
  | str (value : String)
  /-- An object identity: the locations its named fields stand for, fixed at
  allocation, with an optional immutable invocation descriptor. -/
  | objAt (fields : List (String × Nat)) (call : CallCode)
  /-- Allocate one object with immutable call code, one fresh location per
  named field, holding the values of `inits` in order. Only the initializers
  are evaluated; code binds its declared parameter count. -/
  | makeAt (call : CallCode) (names : List String) (inits : List Tm)
  | readAt (field : String) (a : Tm)
  | writeAt (field : String) (a b : Tm)
  | test (k : Tag) (a : Tm)
  | ite (c t e : Tm)
  /-- Arithmetic on the values of `a` and `b`, in that order, both numbers. -/
  | arith (op : Arith) (a b : Tm)
  deriving Repr

/-- Invocation code is not a runtime value. A plain object has no call code. -/
inductive CallCode where
  | absent
  | closure (arity : Nat) (body : Tm)
  deriving Repr
end

/-- The bits `Tm.num` carries for a numeric lexeme: the bit pattern of the
double it denotes, with `-0` normalised to `+0`. This is not a JSON helper but
the rule that `1`, `1.0` and `1e0` are one value — a fact about this
calculus's numbers, which the claim decoder happens to need in order to give a
numeric literal the same identity the calculus gives it. Numeric wire data
remains decodable, but `SourceTypes` rejects it; this does not establish
numeric program semantics. -/
def numBits (lexeme : String) : Except String UInt64 :=
  match Lean.Json.parse lexeme with
  | .ok (.num n) =>
      let f := n.toFloat
      .ok (if f == 0.0 then (0.0 : Float).toBits else f.toBits)
  | _ => .error s!"not a decimal numeric literal: {lexeme}"

/-- The bits of an arithmetic result: the double operation on the operands'
doubles, with `-0` normalised to `+0` as `numBits` does for a literal, so a
computed zero and a written zero are one value, as `===` already treats them. -/
def arithBits (op : Arith) (x y : UInt64) : UInt64 :=
  let a := Float.ofBits x
  let b := Float.ofBits y
  let r := match op with
    | .add => a + b
    | .sub => a - b
    | .mul => a * b
    | .div => a / b
  if r == 0.0 then (0.0 : Float).toBits else r.toBits

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
  case num.num a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.num.injEq])
  case str.str a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.str.injEq])
  case objAt.objAt a0 a1 b0 b1 =>
    haveI : Decidable (a1 = b1) := callCodeDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.objAt.injEq])
  case makeAt.makeAt a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a0 = b0) := callCodeDecEq a0 b0
    haveI : Decidable (a2 = b2) := argsDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.makeAt.injEq])
  case readAt.readAt a0 a1 b0 b1 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.readAt.injEq])
  case writeAt.writeAt a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := tmDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.writeAt.injEq])
  case test.test a0 a1 b0 b1 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.test.injEq])
  case ite.ite a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := tmDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.ite.injEq])
  case arith.arith a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := tmDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.arith.injEq])
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

/-! ### The one-field spellings

A cell is an object with the single field `value`. These abbreviations are the
language the development before field names was written in, and they keep that
meaning exactly: every rule, example and proof that says `obj`, `make`, `read`
or `write` is speaking about that one field. -/

/-- An already allocated one-field object. -/
@[match_pattern] abbrev Tm.obj (l : Nat) (call : CallCode) : Tm :=
  .objAt [(valueField, l)] call

/-- Allocation of a one-field object. -/
@[match_pattern] abbrev Tm.make (call : CallCode) (a : Tm) : Tm :=
  .makeAt call [valueField] [a]

/-- Reading and writing that one field. -/
@[match_pattern] abbrev Tm.read (a : Tm) : Tm := .readAt valueField a
@[match_pattern] abbrev Tm.write (a b : Tm) : Tm := .writeAt valueField a b

/-- Plain-object allocation is the absent-descriptor case of `make`. -/
@[match_pattern] abbrev Tm.alloc (a : Tm) : Tm := .make .absent a

/-- Function-object allocation is the closure-descriptor case of `make`. -/
@[match_pattern] abbrev Tm.attach (b a : Tm) : Tm := .make (.closure 1 b) a

/-- Source function creation starts with an empty one-cell property bag. -/
@[match_pattern] abbrev Tm.funE (b : Tm) : Tm := .attach b .nul

/-- Notation for an already allocated function object, used in semantic lemmas. -/
@[match_pattern] abbrev Tm.fn (l : Nat) (b : Tm) : Tm := .obj l (.closure 1 b)

/-- The locations a fresh allocation gives its fields, in declaration order. -/
def slots (base : Nat) : List String → List (String × Nat)
  | [] => []
  | f :: fs => (f, base) :: slots (base + 1) fs

@[simp] theorem slots_value (base : Nat) : slots base [valueField] = [(valueField, base)] := rfl

@[simp] theorem slots_length (base : Nat) (ns : List String) :
    (slots base ns).length = ns.length := by
  induction ns generalizing base <;> simp_all [slots]

/-- A field of a fresh object stands for the location its position was given.
Distinct names are what makes the map a map: with a repeat, only the first
occurrence is ever found. -/
theorem lookup_slots {ns : List String} (hnd : ns.Nodup) {base i : Nat}
    (hi : i < ns.length) : (slots base ns).lookup ns[i] = some (base + i) := by
  induction ns generalizing base i with
  | nil => simp at hi
  | cons a ns ih =>
    cases i with
    | zero => simp [slots, List.lookup]
    | succ i =>
      have hib : i < ns.length := by simpa using hi
      have hne : ns[i] ≠ a := by
        intro he
        exact (List.nodup_cons.mp hnd).1 (he ▸ List.getElem_mem hib)
      have hbeq : (ns[i] == a) = false := by simpa using hne
      simp only [slots, List.lookup, List.getElem_cons_succ, hbeq]
      rw [ih (List.nodup_cons.mp hnd).2 hib]
      congr 1
      omega

/-- Term induction exposing the body stored inside a call descriptor. -/
@[elab_as_elim] theorem Tm.induct {P : Tm → Prop}
    (var : ∀ i, P (.var i))
    (call : ∀ f args, P f → (∀ a ∈ args, P a) → P (.call f args))
    (letE : ∀ a b, P a → P b → P (.letE a b))
    (nul : P .nul) (undef : P .undef) (tru : P .tru) (fls : P .fls)
    (num : ∀ v, P (.num v))
    (str : ∀ s, P (.str s))
    (objAbsent : ∀ fs, P (.objAt fs .absent))
    (objClosure : ∀ fs n b, P b → P (.objAt fs (.closure n b)))
    (attach : ∀ n b ns args, P b → (∀ a ∈ args, P a) → P (.makeAt (.closure n b) ns args))
    (alloc : ∀ ns args, (∀ a ∈ args, P a) → P (.makeAt .absent ns args))
    (read : ∀ f a, P a → P (.readAt f a))
    (write : ∀ f a b, P a → P b → P (.writeAt f a b))
    (test : ∀ k a, P a → P (.test k a))
    (ite : ∀ c a b, P c → P a → P b → P (.ite c a b))
    (arith : ∀ op a b, P a → P b → P (.arith op a b)) (t : Tm) : P t := by
  apply Tm.rec (motive_1 := P)
    (motive_2 := fun c => match c with | .absent => True | .closure _ b => P b)
    (motive_3 := fun args => ∀ a ∈ args, P a)
    var call letE nul undef tru fls num str ?_ ?_ read write test ite arith
    True.intro (fun _ _ h => h) (by simp) (by
      intro a args ha ih v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ha
      · exact ih v hv) t
  · intro fs c ih
    cases c with
    | absent => exact objAbsent fs
    | closure n b => exact objClosure fs n b ih
  · intro c ns args ihc iha
    cases c with
    | absent => exact alloc ns args iha
    | closure n b => exact attach n b ns args ihc iha



abbrev Val := Tm

/-! ## Values and substitution -/


def isVal : Tm → Bool
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .objAt .. => true
  | _ => false

/-- ECMAScript Number::equal on IEEE-754 bits: NaN never equals, and the
sign of zero is ignored. All other equal Numbers have the same encoding. -/
def numberEqual (a b : UInt64) : Bool :=
  let nan := fun (x : UInt64) =>
    (x &&& 0x7ff0000000000000) == 0x7ff0000000000000 &&
      (x &&& 0x000fffffffffffff) != 0
  !nan a && !nan b &&
    (a == b || ((a &&& 0x7fffffffffffffff) == 0 && (b &&& 0x7fffffffffffffff) == 0))

/-- Tests are total on values. Numeric equality also inspects the bits. -/
def tagHolds : Tag → Val → Bool
  | .isNul, .nul => true
  | .isUndef, .undef => true
  | .isNullish, .nul | .isNullish, .undef => true
  | .isBool, .tru => true
  | .isBool, .fls => true
  | .isNum, .num _ => true
  | .numEq bits, .num value => numberEqual value bits
  | .isStr, .str _ => true
  | .strEq s, .str t => s == t
  | .isRef, .objAt _ .absent => true
  | .isFun, .objAt _ (.closure _ _) => true
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
  | .num v => .num v
  | .str s => .str s
  | .objAt fs .absent => .objAt fs .absent
  | .objAt fs (.closure n b) => .objAt fs (.closure n (subst (j + n) a b))
  | .makeAt (.closure n b) ns xs => .makeAt (.closure n (subst (j + n) a b)) ns (substArgs j a xs)
  | .makeAt .absent ns xs => .makeAt .absent ns (substArgs j a xs)
  | .readAt f x => .readAt f (subst j a x)
  | .writeAt f x y => .writeAt f (subst j a x) (subst j a y)
  | .test k x => .test k (subst j a x)
  | .ite c x y => .ite (subst j a c) (subst j a x) (subst j a y)
  | .arith op x y => .arith op (subst j a x) (subst j a y)

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
  | callL : Step h f h' f' → Step h (.call f args) h' (.call f' args)
  | callArg : isVal f = true → args[i]? = some a →
      (∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) →
      Step h a h' a' → Step h (.call f args) h' (.call f (args.set i a'))
  | letC : Step h a h' a' → Step h (.letE a b) h' (.letE a' b)
  | letV : isVal a = true → Step h (.letE a b) h (subst 0 a b)
  /-- Invocation executes the object's stored code in one step. -/
  | callV : (∀ a ∈ args, isVal a = true) →
      Step h (.call (.objAt fs (.closure n b)) args) h (CallArguments.bindParameters n args b)
  /-- Initializers are evaluated left to right, like actual arguments. -/
  | makeArg {c : CallCode} {ns : List String} {inits : List Tm} {i : Nat}
      {h h' : Heap} {a a' : Tm} : inits[i]? = some a →
      (∀ j, j < i → ∀ v, inits[j]? = some v → isVal v = true) →
      Step h a h' a' → Step h (.makeAt c ns inits) h' (.makeAt c ns (inits.set i a'))
  /-- Allocation takes one fresh location per named field, in order. -/
  | makeFields {c : CallCode} {ns : List String} {vs : List Tm} {h : Heap} :
      (∀ v ∈ vs, isVal v = true) → ns.length = vs.length →
      Step h (.makeAt c ns vs) (h ++ vs) (.objAt (slots h.length ns) c)
  | readC : Step h a h' a' → Step h (.readAt f a) h' (.readAt f a')
  /-- Reading and writing a field go to its location, whatever the object's code. -/
  | readField {f : String} {fs : List (String × Nat)} {c : CallCode} {l : Nat}
      {h : Heap} {v : Val} : fs.lookup f = some l → h[l]? = some v →
      Step h (.readAt f (.objAt fs c)) h v
  | writeC1 : Step h a h' a' → Step h (.writeAt f a b) h' (.writeAt f a' b)
  | writeC2 : isVal a = true → Step h b h' b' → Step h (.writeAt f a b) h' (.writeAt f a b')
  | writeField {f : String} {fs : List (String × Nat)} {c : CallCode} {l : Nat}
      {h : Heap} {v : Val} : isVal v = true → fs.lookup f = some l → l < h.length →
      Step h (.writeAt f (.objAt fs c) v) (h.set l v) .nul
  | testC : Step h a h' a' → Step h (.test k a) h' (.test k a')
  | testV : isVal v = true →
      Step h (.test k v) h (if tagHolds k v then .tru else .fls)
  | iteC : Step h c h' c' → Step h (.ite c t e) h' (.ite c' t e)
  | iteT : Step h (.ite .tru t e) h t
  | iteF : Step h (.ite .fls t e) h e
  | arithC1 : Step h a h' a' → Step h (.arith op a b) h' (.arith op a' b)
  | arithC2 : isVal a = true → Step h b h' b' → Step h (.arith op a b) h' (.arith op a b')
  /-- Two numbers combine in one step; nothing else is ever combined. -/
  | arithV : Step h (.arith op (.num x) (.num y)) h (.num (arithBits op x y))

/-! ### The one-field rules

Each is the single-field instance of the rule above it, and carries the name
and the statement the development used before fields were named. -/

@[simp] theorem lookup_value (l : Nat) : ([(valueField, l)] : List (String × Nat)).lookup valueField = some l := by
  simp [List.lookup]

theorem Step.makeC (hs : Step h a h' a') : Step h (.make c a) h' (.make c a') :=
  .makeArg (i := 0) rfl (by intro j hj; omega) hs

theorem Step.makeV (hv : isVal v = true) :
    Step h (.make c v) (h ++ [v]) (.obj h.length c) :=
  .makeFields (by simpa using hv) rfl

theorem Step.readV (he : h[l]? = some v) : Step h (.read (.obj l c)) h v :=
  .readField (lookup_value l) he

theorem Step.writeV (hv : isVal v = true) (hlt : l < h.length) :
    Step h (.write (.obj l c) v) (h.set l v) .nul :=
  .writeField hv (lookup_value l) hlt

/-- Singleton operand rules are specializations of native list evaluation. -/
theorem Step.appL (hs : Step h f h' f') : Step h (.app f a) h' (.app f' a) :=
  .callL hs

theorem Step.appR (hv : isVal f = true) (hs : Step h a h' a') :
    Step h (.app f a) h' (.app f a') :=
  .callArg (i := 0) hv rfl (by intro j hj; omega) hs

/-- Inversion for the source pipeline's singleton argument lists. -/
theorem singleton_get {a b : Tm} {i : Nat} (h : [a][i]? = some b) : i = 0 ∧ b = a := by
  have hi := (List.getElem?_eq_some_iff.mp h).1
  have he : i = 0 := by simpa using hi
  subst i
  exact ⟨rfl, (Option.some.inj h).symm⟩

/-- The existing unary beta rule is a specialization of list dispatch. -/
theorem Step.beta {fs : List (String × Nat)} (ha : isVal a = true) :
    Step h (.app (.objAt fs (.closure n b)) a) h (CallArguments.bindParameters n [a] b) :=
  .callV (by simpa using ha)

theorem nul_no_step {h h' t} : ¬ Step h .nul h' t := by intro s; cases s
theorem tru_no_step {h h' t} : ¬ Step h .tru h' t := by intro s; cases s
theorem fls_no_step {h h' t} : ¬ Step h .fls h' t := by intro s; cases s
theorem obj_no_step {h fs c h' t} : ¬ Step h (.objAt fs c) h' t := by intro s; cases s

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
  | callL hs => exact nul_no_step hs
  | callArg _ hg _ hs =>
    obtain ⟨rfl, rfl⟩ := singleton_get hg
    exact nul_no_step hs

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
  | callL s ih =>
    cases s2 with
    | callL s' => exact (ih s').imp id (congrArg (Tm.call · _))
    | callArg hv _ _ _ => exact False.elim (value_no_step hv s)
    | callV => exact False.elim (obj_no_step s)
  | @callArg f args i a h h1 a1 hv hg hb s ih =>
    cases s2 with
    | callL s' => exact False.elim (value_no_step hv s')
    | @callArg _ _ j b _ _ b1 _ hg' hb' s' =>
      have hij : i = j := by
        by_cases he : i = j
        · exact he
        · have hlt : i < j ∨ j < i := by omega
          rcases hlt with hij | hji
          · exact False.elim (value_no_step (hb' i hij a hg) s)
          · exact False.elim (value_no_step (hb j hji b hg') s')
      subst j
      have hab : a = b := Option.some.inj (hg.symm.trans hg')
      subst b
      obtain ⟨rfl, rfl⟩ := ih s'
      exact ⟨rfl, rfl⟩
    | callV hvs => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s)
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
    | callL hs => exact absurd hs obj_no_step
    | callArg _ hg _ hs => exact absurd hs (value_no_step (hv _ (List.mem_of_getElem? hg)))
    | callV => exact ⟨rfl, rfl⟩
  | @makeArg c ns inits i h h1 a a1 hg hb s ih =>
    cases s2 with
    | @makeArg _ _ _ j _ _ b b1 hg' hb' s' =>
      have hij : i = j := by
        by_cases he : i = j
        · exact he
        · have hlt : i < j ∨ j < i := by omega
          rcases hlt with hij | hji
          · exact False.elim (value_no_step (hb' i hij a hg) s)
          · exact False.elim (value_no_step (hb j hji b hg') s')
      subst j
      have hab : a = b := Option.some.inj (hg.symm.trans hg')
      subst b
      obtain ⟨rfl, rfl⟩ := ih s'
      exact ⟨rfl, rfl⟩
    | makeFields hvs _ => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s)
  | makeFields hv hlen =>
    cases s2 with
    | makeArg hg _ s' => exact False.elim (value_no_step (hv _ (List.mem_of_getElem? hg)) s')
    | makeFields _ _ => exact ⟨rfl, rfl⟩
  | readC s ih =>
    cases s2 with
    | readC s' => exact (ih s').imp id (congrArg (Tm.readAt _))
    | readField _ _ => exact absurd s obj_no_step
  | readField hl he =>
    cases s2 with
    | readC s' => exact absurd s' obj_no_step
    | readField hl' he' =>
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, Option.some.inj (he.symm.trans he')⟩
  | writeC1 s ih =>
    cases s2 with
    | writeC1 s' => exact (ih s').imp id (congrArg (Tm.writeAt _ · _))
    | writeC2 hv s' => exact absurd s (by intro hs; exact value_no_step hv hs)
    | writeField _ _ _ => exact absurd s obj_no_step
  | writeC2 hv s ih =>
    cases s2 with
    | writeC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | writeC2 _ s' => exact (ih s').imp id (congrArg (Tm.writeAt _ _ ·))
    | writeField hv' _ _ => exact absurd s (by intro hs; exact value_no_step hv' hs)
  | writeField hv hl hlt =>
    cases s2 with
    | writeC1 s' => exact absurd s' obj_no_step
    | writeC2 _ s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | writeField _ hl' _ =>
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, rfl⟩
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
  | arithC1 s ih =>
    cases s2 with
    | arithC1 s' => exact (ih s').imp id (congrArg (Tm.arith _ · _))
    | arithC2 hv _ => exact absurd s (by intro hs; exact value_no_step hv hs)
    | arithV => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | arithC2 hv s ih =>
    cases s2 with
    | arithC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | arithC2 _ s' => exact (ih s').imp id (congrArg (Tm.arith _ _ ·))
    | arithV => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | arithV =>
    cases s2 with
    | arithC1 s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | arithC2 _ s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | arithV => exact ⟨rfl, rfl⟩

theorem make_step_inv {c : CallCode} {v : Val} (hv : isVal v = true) {h h' t}
    (hs : Step h (.make c v) h' t) : h' = h ++ [v] ∧ t = .obj h.length c := by
  cases hs with
  | makeArg hg _ hs =>
    obtain ⟨rfl, rfl⟩ := singleton_get hg
    exact False.elim (value_no_step hv hs)
  | makeFields => exact ⟨rfl, rfl⟩

theorem beta_inv {b a : Tm} {fs : List (String × Nat)} (ha : isVal a = true) {h h' t}
    (hs : Step h (.app (.objAt fs (.closure 1 b)) a) h' t) : h' = h ∧ t = subst 0 a b := by
  cases hs with
  | callL hs => cases hs
  | callArg _ hg _ hs =>
    obtain ⟨rfl, rfl⟩ := singleton_get hg
    exact False.elim (value_no_step ha hs)
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
  | readField hl he =>
    rw [lookup_value] at hl
    cases hl
    exact ⟨rfl, he⟩


end ExperimentState
end Verification
