import Verification.Calculus.Values

/-! The type language: its syntax and meaning as sets of values. -/

namespace Verification
namespace Core

/-! ## Type syntax -/

/-- One alternative of a type. A type is the union of its atoms.

`num`, `str` and `bool` are the base types `number`, `string` and `boolean`;
`numLit`, `strLit` and `boolLit` are their literal types, such as `"a"`. There
is no atom for TypeScript's `any`, which the calculus does not model; its
`unknown` is `Ty.top` below. -/
inductive Atom where
  | null
  | undef
  | num
  | str
  | bool
  | numLit (bits : UInt64)
  | strLit (s : String)
  | boolLit (b : Bool)
  deriving DecidableEq, Repr

/-- A type: `unknown` (`top`), or the union of a finite list of atoms.
An empty atom list with `top = false` is `never`. -/
structure Ty where
  top : Bool
  atoms : List Atom
  deriving DecidableEq, Repr

/-! ## Type semantics -/

/-- `inhabits v a` : the value `v` is one of the values the atom `a` denotes. -/
def inhabits : Val → Atom → Bool
  | .vnull, .null => true
  | .vundef, .undef => true
  | .vnum _, .num => true
  | .vstr _, .str => true
  | .vbool _, .bool => true
  | .vnum b, .numLit c => b == c
  | .vstr s, .strLit t => s == t
  | .vbool b, .boolLit c => b == c
  | _, _ => false

/-- The denotation of a type as a set of values. -/
def mem (v : Val) (t : Ty) : Prop :=
  t.top = true ∨ ∃ a ∈ t.atoms, inhabits v a = true

/-- Arguments satisfy the declared parameter types, with matching arity. -/
def MemAll : List Val → List (String × Ty) → Prop
  | [], [] => True
  | v :: vs, (_, t) :: ps => mem v t ∧ MemAll vs ps
  | _, _ => False

end Core
end Verification
