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

end ExperimentState
end Verification
