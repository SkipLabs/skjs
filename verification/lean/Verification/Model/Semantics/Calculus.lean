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
that is not a value, does not throw (`Raises`) and cannot step is **stuck**,
and the safety predicate in `Safety.lean` rules that out. A throw is an
outcome, as a value is: JavaScript's exceptions are part of its meaning, and a
well-typed program may throw, never reach a wrong value.
-/
namespace Verification
namespace Model

/-- A property key. JavaScript keys an object's properties by strings and by
symbols, and the two spaces are disjoint: no string names a symbol-keyed
property, so a string-keyed access, and a type that constrains every string
key, never reaches one. A symbol key is the identity of a symbol value. -/
inductive PropKey where
  | str (name : String)
  | sym (id : Nat)
  deriving Repr, DecidableEq

/-- Field names written in the model are string keys. -/
instance : Coe String PropKey := ⟨PropKey.str⟩

/-- For messages only: a symbol key is shown by its identity. -/
instance : ToString PropKey where
  toString
    | .str name => name
    | .sym id => s!"[symbol {id}]"

/-- An order for sorting field maps: string keys by name, then symbol keys by
identity. -/
def PropKey.before : PropKey → PropKey → Bool
  | .str a, .str b => a < b
  | .str _, .sym _ => true
  | .sym _, .str _ => false
  | .sym a, .sym b => a < b

/-- The field every single-cell object of the earlier development carries. A
one-field object named this way is what `Tm.obj`, `Tm.read` and `Tm.write`
abbreviate, so every rule and proof written before field names keeps its
meaning. -/
def valueField : PropKey := "value"

/-- The key an array object holds its store under (`CallArguments.arrayStoreField`).
No source property names it, so an object owns it exactly when it is an array:
that is what `Array.isArray` tests (`Tag.isArray`). -/
def arrayStoreKey : PropKey := "[]"

/-- The shapes a value can have, and so the tests a program can make of one.
Nullishness groups null and undefined for source coalescing; the other tests
distinguish individual runtime shapes. `truthy` is JavaScript's `ToBoolean`:
false exactly for `false`, the two zeros, NaN, `""`, `0n`, `null` and
`undefined`. -/
inductive Tag where
  | isNul | isBool | isRef | isFun | isUndef | isNullish | isNum | isStr
  | numEq (bits : UInt64)
  | strEq (value : String)
  | isBigint | isSymbol
  | truthy
  /-- `Array.isArray`: a plain object owning the store key, which only an
  array does. Keys are fixed at allocation, so the answer never changes. -/
  | isArray
  deriving Repr, DecidableEq

/-- The binary operators on primitive operands, JavaScript's own (`binop`
gives their meaning). Arithmetic combines two numbers as the IEEE-754 double
operation, or two bigints as the integer one: `pow` is `**`, `xor` is `^`,
which `~x` is written with (`x ^ -1`). The relational operators compare two
numeric operands, number and bigint alike, or two strings, and answer a
Boolean. A combination JavaScript throws on, or converts through anything
else, is stuck. -/
inductive Arith where
  | add | sub | mul | div
  | pow | xor
  | lt | le | gt | ge
  deriving Repr, DecidableEq, BEq

/-- Whether an operator compares rather than computes. -/
def Arith.relational : Arith → Bool
  | .lt | .le | .gt | .ge => true
  | _ => false

/-- Which of JavaScript's internal methods a function's code provides: `call`
code runs when the function is called (`[[Call]]`), and `construct` code only
under `new` (`[[Construct]]`), as a class constructor's does, whose plain call
throws. An arrow's or a method's code is `call`: `new` on it throws. -/
inductive Invoke where
  | call | construct
  deriving Repr, DecidableEq

mutual
/-- Terms. Values are terms too, so worlds and the operational semantics speak
about the same objects. -/
inductive Tm where
  | var (i : Nat)
  /-- Invoke the callee `f` with the receiver `r` and the actuals `args`: the
  callee first, then the receiver, then the actuals left to right. A receiver
  is not an actual: it changes no arity, optional position or rest. -/
  | invoke (f r : Tm) (args : List Tm)
  /-- `new f(args)`: evaluate `f`, then the actuals left to right, then run
  `f`'s `construct` code with them. There is no receiver: the code allocates
  and returns the instance itself. -/
  | construct (f : Tm) (args : List Tm)
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
  /-- A string, carried as itself: bound, passed, stored, shape-tested,
  compared, and concatenated by `+` (`binop`). -/
  | str (value : String)
  /-- A bigint, carried as the integer it is: its identity, as a number's bits
  are. `arith` computes with it; equal integers are the same bigint. -/
  | bigint (value : Int)
  /-- A symbol, carried as an identity. Nothing here computes with it: it is
  bound, passed, stored and shape-tested. -/
  | sym (id : Nat)
  /-- An object identity: the locations its named fields stand for, fixed at
  allocation, with an optional immutable invocation descriptor. -/
  | objAt (fields : List (PropKey × Nat)) (call : CallCode)
  /-- Allocate one object with immutable call code, one fresh location per
  named field, holding the values of `inits` in order. Only the initializers
  are evaluated; code binds its declared parameter count. -/
  | makeAt (call : CallCode) (names : List PropKey) (inits : List Tm)
  | readAt (field : PropKey) (a : Tm)
  /-- Evaluate the receiver, then a string key, then read the named property. -/
  | indexAt (a key : Tm)
  | writeAt (field : PropKey) (a b : Tm)
  | test (k : Tag) (a : Tm)
  | ite (c t e : Tm)
  /-- A binary operator on the values of `a` and `b`, in that order: defined
  where `binop` answers, stuck elsewhere. -/
  | arith (op : Arith) (a b : Tm)
  /-- An array's store: the location of each element, in order, or none at a
  hole. The array object holds this value in its store field and replaces it
  when the array grows, so identity, aliasing and holes all live in locations. -/
  | arr (elems : List (Option Nat))
  /-- Allocate one location per initializer, in order, as a store. -/
  | arrLit (inits : List Tm)
  /-- The element a numeric index names in a store: `undefined` at a hole or
  past the end, as property lookup answers. In a string it is the code unit
  there, as the string's own index property answers. -/
  | elemAt (a i : Tm)
  /-- Store a value at a numeric index: into the element's location, or, at a
  hole or past the end, into a fresh location the returned store records. -/
  | setElem (a i v : Tm)
  /-- A store's length, or a string's own `length`: its UTF-16 code units. -/
  | lenOf (a : Tm)
  /-- An actual that stands for the elements of the store `a` evaluates to,
  read in order when every earlier actual is a value. Only an argument list
  gives it meaning: anywhere else it is stuck. -/
  | spread (a : Tm)
  /-- `throw a`: evaluate `a`, then throw its value. A thrown value is not a
  value: it propagates outward through every evaluation context (`Raises`)
  until a handler catches it or it leaves the program. -/
  | throw (a : Tm)
  deriving Repr

/-- Invocation code is not a runtime value. A plain object has no call code. -/
inductive CallCode where
  | absent
  /-- Code taking `arity` parameters. Its body is scoped under `arity + 1`
  binders, the frame `[this, parameter_0, …, parameter_{arity-1}]` before the
  captures: slot 0 is the receiver and slots `1 .. arity` the parameters. Code
  that ignores its receiver, as an arrow's does, never reads slot 0. -/
  | closure (arity : Nat) (body : Tm) (kind : Invoke := .call)
  /-- Code that takes `fixed` parameters and collects every further actual into
  one fresh array. Its body is scoped under `fixed + 2` binders: slot 0 is that
  array, slot 1 the receiver and slots `2 .. fixed + 1` the parameters.
  Invocation binds what it is given; the array is allocated by the ordinary
  steps of the term it yields. -/
  | variadic (fixed : Nat) (body : Tm)
  /-- A forwarding descriptor: what `.bind` creates. It keeps the target, the
  receiver and the argument prefix it was given, each a value by the time the
  object is allocated. Invoking it ignores the receiver of that call and
  invokes the target with the saved receiver, the prefix, then the new actuals.
  No field holds this state, so no write can reach it, and a second `.bind`
  cannot replace the first receiver. -/
  | bound (target receiver : Tm) (pre : List Tm)
  deriving Repr
end

/-- Whether code has `[[Call]]`: all code but a class constructor's. A plain
object has none. -/
def CallCode.callable : CallCode → Bool
  | .absent => false
  | .closure _ _ .construct => false
  | _ => true

/-- A call without a receiver supplies `undefined` for it: an abbreviation of
`invoke`, not a second form of call. -/
@[match_pattern] abbrev Tm.call (f : Tm) (args : List Tm) : Tm := .invoke f .undef args

/-- Canonical bits for a source numeric literal type. Equal decimal spellings
share a singleton; source type zero expands to both runtime bit patterns in
`SourceTypes`. Runtime literals use `literalBits` and retain their sign. -/
def numBits (lexeme : String) : Except String UInt64 :=
  match Lean.Json.parse lexeme with
  | .ok (.num n) =>
      let f := n.toFloat
      .ok (if f == 0.0 then (0.0 : Float).toBits else f.toBits)
  | _ => .error s!"not a decimal numeric literal: {lexeme}"

/-- Runtime literals retain their sign. Source type zero
is lowered to both bit singletons, while an expression keeps its exact bits. -/
def literalBits (lexeme : String) : Except String UInt64 := do
  let bits ← numBits lexeme
  return if Float.ofBits bits == 0.0 && lexeme.startsWith "-"
    then (9223372036854775808 : UInt64) else bits

/-- JavaScript's `Number::exponentiate`, which is IEEE `pow` except that a NaN
exponent always gives NaN and a base of magnitude one to an infinite power is
NaN, where C's `pow` answers 1 for both. -/
def jsPow (a b : Float) : Float :=
  if b.isNaN then 0.0 / 0.0
  else if (a == 1.0 || a == -1.0) && b.isInf then 0.0 / 0.0
  else a ^ b

/-- `ToInt32` on the bits of a double, exactly: NaN and the infinities are 0;
otherwise the value truncated toward zero, modulo 2^32, read as signed. -/
def toInt32 (x : UInt64) : Int :=
  let e := ((x >>> 52) &&& 0x7ff).toNat
  let m := (x &&& 0xfffffffffffff).toNat
  if e == 0x7ff then 0 else
  let mant := if e == 0 then m else m + 2 ^ 52
  let shift : Int := (if e == 0 then 1 else (e : Int)) - 1075
  -- Past 2^32 the low 32 bits of an integer multiple of 2^32 are zero.
  let mag : Nat := if 32 ≤ shift then 0
    else if 0 ≤ shift then mant * 2 ^ shift.toNat else mant / 2 ^ (-shift).toNat
  let k : Nat := mag % 2 ^ 32
  let u : Nat := if x >>> 63 == 1 then (2 ^ 32 - k) % 2 ^ 32 else k
  if 2 ^ 31 ≤ u then (u : Int) - 2 ^ 32 else u

/-- Two's-complement exclusive or of two integers: a negative integer is the
complement of a natural, and complementing one operand complements the result. -/
def intXor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

/-- The double an integer in the 32-bit range denotes, exactly. -/
def int32Bits (i : Int) : UInt64 :=
  (if i < 0 then -((-i).toNat.toFloat) else i.toNat.toFloat).toBits

/-- The bits of an arithmetic result on two numbers: the double operation on
the operands' doubles. Signed zero is preserved: division observes its sign
even though strict equality equates the two zeros. A relational operator
yields a Boolean, not a number (`binop`); it has no bits here. -/
def arithBits (op : Arith) (x y : UInt64) : UInt64 :=
  let a := Float.ofBits x
  let b := Float.ofBits y
  match op with
    | .add => (a + b).toBits
    | .sub => (a - b).toBits
    | .mul => (a * b).toBits
    | .div => (a / b).toBits
    | .pow => (jsPow a b).toBits
    | .xor => int32Bits (intXor (toInt32 x) (toInt32 y))
    | .lt | .le | .gt | .ge => (0.0 / 0.0 : Float).toBits

/-- Arithmetic on two bigints: JavaScript's integer operations. Division
truncates toward zero; dividing by zero and a negative exponent throw a
`RangeError` (`binopThrows`), so they have no result. -/
def bigintArith : Arith → Int → Int → Option Int
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .div, x, y => if y = 0 then none else some (x.tdiv y)
  | .pow, x, y => if y < 0 then none else some (x ^ y.toNat)
  | .xor, x, y => some (intXor x y)
  | .lt, _, _ | .le, _, _ | .gt, _, _ | .ge, _, _ => none

/-- The order of two doubles: none when either is NaN, and the two zeros
equal, as IEEE comparison has them. -/
def doubleOrder (x y : UInt64) : Option Ordering :=
  let a := Float.ofBits x
  let b := Float.ofBits y
  if a < b then some .lt else if a == b then some .eq else if b < a then some .gt else none

/-- The order of a double and an integer, exactly: none when the double is
NaN; an infinity is beyond every integer; a finite double is compared as the
rational it denotes, `mantissa * 2^shift`. -/
def doubleIntOrder (x : UInt64) (n : Int) : Option Ordering :=
  let e := ((x >>> 52) &&& 0x7ff).toNat
  let m := (x &&& 0xfffffffffffff).toNat
  let negative := x >>> 63 == 1
  if e == 0x7ff then
    if m != 0 then none else some (if negative then .lt else .gt)
  else
    let mant : Int := if e == 0 then m else m + 2 ^ 52
    let signed := if negative then -mant else mant
    let shift : Int := (if e == 0 then 1 else (e : Int)) - 1075
    if 0 ≤ shift then some (compare (signed * 2 ^ shift.toNat) n)
    else some (compare signed (n * 2 ^ (-shift).toNat))

/-- A string as JavaScript sees it: its UTF-16 code units, in order. -/
def utf16Units (s : String) : List Nat :=
  s.toList.flatMap fun c =>
    let v := c.val.toNat
    if v < 0x10000 then [v]
    else [0xD800 + (v - 0x10000) / 0x400, 0xDC00 + (v - 0x10000) % 0x400]

/-- Lexicographic order of code-unit sequences: a proper prefix is less. -/
def unitsOrder : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else unitsOrder as bs

/-- A relational operator's answer from the order of its operands, where
`none` is JavaScript's undefined comparison (a NaN operand): every relational
operator is then false. -/
def relationHolds : Arith → Option Ordering → Bool
  | .lt, some .lt => true
  | .le, some .lt | .le, some .eq => true
  | .gt, some .gt => true
  | .ge, some .gt | .ge, some .eq => true
  | _, _ => false

def boolVal (b : Bool) : Tm := if b then .tru else .fls

/-- `a * 2^e / 10^d` as a fraction of naturals, exactly. -/
private def scaledFraction (a : Nat) (e d : Int) : Nat × Nat :=
  (a * 2 ^ e.toNat * 10 ^ (-d).toNat, 2 ^ (-e).toNat * 10 ^ d.toNat)

/-- The shortest decimal digits of a positive finite double `mant * 2^exp`,
as `Number::toString` chooses them: the integer `s` and exponent `d` with
`s * 10^d` rounding to the double, `s` of as few digits as possible, and among
those the one closest to the double, the even one on a tie (the choice the
specification's note recommends and engines make). Rounding to nearest even
rounds exactly the reals strictly between the midpoints to the neighbouring
doubles, and the midpoints too when `mant` is even; the midpoint below is
nearer where `mant` is the first of a binade above the smallest. Measured in
quarters of the double's unit, the double is `4 mant` and the midpoints
`4 mant + 2` and `4 mant - 2` (or `- 1`). The largest `d` for which an integer
fits between them gives the fewest digits; `fuel` counts the exponents
tried, from above every finite double's. -/
def shortestDigits (mant : Nat) (exp : Int) (lower : Bool) : Nat × Int :=
  let e := exp - 2
  let x := 4 * mant
  let lo := if lower then x - 1 else x - 2
  let hi := x + 2
  let closed := mant % 2 == 0
  let rec go : Nat → Int → Nat × Int
    | 0, d => (mant, d)
    | fuel + 1, d =>
      let (ln, ld) := scaledFraction lo e d
      let (hn, hd) := scaledFraction hi e d
      -- The least integer at or above (above, when open) the lower midpoint,
      -- and the greatest at or below (below) the upper one.
      let least := if closed then (ln + ld - 1) / ld else ln / ld + 1
      let most := if closed then hn / hd else (hn + hd - 1) / hd - 1
      if least ≤ most then
        let (xn, xd) := scaledFraction x e d
        let below := xn / xd
        let twice := 2 * (xn % xd)
        let nearest := if twice < xd then below else if xd < twice then below + 1
          else if below % 2 == 0 then below else below + 1
        (min most (max least nearest), d)
      else go fuel (d - 1)
  go 700 309

/-- `Number::toString` in radix 10, exactly: `NaN`, the infinities, `0` for
both zeros, and otherwise the shortest digits `s` with `n` the position of
the decimal point: plain up to 21 integer digits, `0.` and up to six leading
zeros below one, else exponent form `d.ddde±x`. -/
def numberToString (x : UInt64) : String :=
  let e := ((x >>> 52) &&& 0x7ff).toNat
  let m := (x &&& 0xfffffffffffff).toNat
  let sign := if x >>> 63 == 1 then "-" else ""
  if e == 0x7ff then (if m != 0 then "NaN" else sign ++ "Infinity")
  else if e == 0 && m == 0 then "0"
  else
    let mant := if e == 0 then m else m + 2 ^ 52
    let exp : Int := (if e == 0 then 1 else (e : Int)) - 1075
    let (s, d) := shortestDigits mant exp (m == 0 && 1 < e)
    let digits := toString s
    let k : Int := digits.length
    let n : Int := k + d
    let zeros := fun (i : Int) => String.ofList (List.replicate i.toNat '0')
    let body :=
      if k ≤ n && n ≤ 21 then digits ++ zeros (n - k)
      else if 0 < n && n ≤ 21 then
        String.ofList (digits.toList.take n.toNat) ++ "." ++ String.ofList (digits.toList.drop n.toNat)
      else if -6 < n && n ≤ 0 then "0." ++ zeros (-n) ++ digits
      else
        let x := n - 1
        let exponent := "e" ++ (if 0 ≤ x then "+" else "-") ++ toString x.natAbs
        match digits.toList with
        | [c] => String.singleton c ++ exponent
        | c :: rest => String.singleton c ++ "." ++ String.ofList rest ++ exponent
        | [] => exponent
    sign ++ body

/-- `ToString` of a primitive other than a symbol, as JavaScript defines it:
no user code runs. A symbol throws a `TypeError`, and an object's conversion
calls its own methods, so neither has one here. -/
def primString : Tm → Option String
  | .str s => some s
  | .num x => some (numberToString x)
  | .bigint i => some (toString i)
  | .tru => some "true"
  | .fls => some "false"
  | .nul => some "null"
  | .undef => some "undefined"
  | _ => none

/-- **What a binary operator does on two values**, as JavaScript's does on
them, where that is a value. Arithmetic combines two numbers or two bigints,
never one of each (JavaScript throws a `TypeError`: `binopThrows`), and not a
bigint division by zero or a negative bigint exponent (a `RangeError`). A relational operator
compares two numeric values of either kind, exactly, or two strings by their
UTF-16 code units. `+` with a string operand concatenates: the other operand,
a primitive other than a symbol, converts by `ToString` (`primString`), which
runs no code. Every other pair converts its operands through code or
coercions not modelled here, and has no answer: the term is stuck. -/
def binop (op : Arith) : Tm → Tm → Option Tm
  | .num x, .num y =>
    some (if op.relational then boolVal (relationHolds op (doubleOrder x y)) else .num (arithBits op x y))
  | .bigint x, .bigint y =>
    if op.relational then some (boolVal (relationHolds op (some (compare x y))))
    else (bigintArith op x y).map .bigint
  | .num x, .bigint y =>
    if op.relational then some (boolVal (relationHolds op (doubleIntOrder x y))) else none
  | .bigint x, .num y =>
    if op.relational then some (boolVal (relationHolds op ((doubleIntOrder y x).map Ordering.swap)))
    else none
  | .str s, .str t =>
    if op.relational then some (boolVal (relationHolds op (some (unitsOrder (utf16Units s) (utf16Units t)))))
    else if op == .add then some (.str (s ++ t)) else none
  | .str s, b => if op == .add then (primString b).map fun t => .str (s ++ t) else none
  | a, .str t => if op == .add then (primString a).map fun s => .str (s ++ t) else none
  | _, _ => none

def isSym : Tm → Bool
  | .sym _ => true
  | _ => false

/-- A primitive value: one no conversion runs code on. -/
def isPrim : Tm → Bool
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ => true
  | _ => false

/-- **Where a binary operator throws** on two values, as JavaScript's does,
with no code of the program's run first: a bigint division by zero and a
negative bigint exponent (`RangeError`); arithmetic combining a number and a
bigint (`TypeError`); and any operator with a symbol operand and a primitive
other one, which converts the symbol by `ToString` or `ToNumeric`
(`TypeError`). An object operand converts through its own code first, which is
not modelled: that combination stays stuck. Disjoint from `binop`
(`binop_not_throws`). -/
def binopThrows (op : Arith) : Tm → Tm → Bool
  | .bigint _, .bigint y => match op with
    | .div => y == 0
    | .pow => decide (y < 0)
    | _ => false
  | .num _, .bigint _ | .bigint _, .num _ => !op.relational
  | a, b => isSym a && isPrim b || isPrim a && isSym b

/-- The object a primitive operation throws: an object with no field, which
takes no location, as `{}` allocates. It stands for the `TypeError` or
`RangeError` instance JavaScript allocates; a handler binds it at `unknown`,
and nothing typed reads more of it. -/
def thrownError : Tm := .objAt [] .absent

/-- The array index a number denotes, when it is one: a finite integer in the
index range, the property name it would spell. Any other number names an
ordinary property this fragment does not model. -/
def indexOfBits (b : UInt64) : Option Nat :=
  let f := Float.ofBits b
  if f.isFinite && decide (0.0 ≤ f) && f == f.floor && decide (f < 4294967295.0)
  then some f.toUInt64.toNat else none

def bitsOfNat (n : Nat) : UInt64 := n.toFloat.toBits

/-- A one-code-unit string. A model string is a sequence of Unicode scalar
values, so half of a surrogate pair has no string of its own: it reads as
U+FFFD, the one place the model's strings differ from JavaScript's
(SEMANTICS.md, "Strings"). -/
def unitString (u : Nat) : String :=
  if 0xD800 ≤ u ∧ u ≤ 0xDFFF then "\uFFFD" else String.singleton (Char.ofNat u)

/-- What a string's index property holds at a numeric key: the code unit at an
array index below its length, else nothing (a JavaScript string owns no other
numeric key, and its prototype none). -/
def codeUnitAt (s : String) (b : UInt64) : Tm :=
  match (indexOfBits b).bind fun k => (utf16Units s)[k]? with
  | some u => .str (unitString u)
  | none => .undef

/-- The location an index names in a store: none at a hole or past the end. -/
def elemLoc (ls : List (Option Nat)) (b : UInt64) : Option Nat :=
  (indexOfBits b).bind fun k => (ls[k]?).bind id

/-- The elements a store holds, in order: `undefined` at a hole, as iterating
an array answers. None when a location is missing from the heap. -/
def readElems (h : List Tm) : List (Option Nat) → Option (List Tm)
  | [] => some []
  | none :: ls => (readElems h ls).map (.undef :: ·)
  | some l :: ls => h[l]?.bind fun v => (readElems h ls).map (v :: ·)

theorem readElems_mem {h : List Tm} {ls : List (Option Nat)} {vs : List Tm}
    (hr : readElems h ls = some vs) : ∀ v ∈ vs, v = .undef ∨ ∃ l : Nat, h[l]? = some v := by
  induction ls generalizing vs with
  | nil => cases hr; simp
  | cons o ls ih =>
    cases o with
    | none =>
      simp only [readElems, Option.map_eq_some_iff] at hr
      obtain ⟨ws, hw, rfl⟩ := hr
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Or.inl rfl
      · exact ih hw v hv
    | some l =>
      simp only [readElems, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨w, hl, ws, hw, rfl⟩ := hr
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Or.inr ⟨l, hl⟩
      · exact ih hw v hv

/-- One fresh location per element, in order, as a literal allocates them. -/
def elemSlots (base n : Nat) : List (Option Nat) := (List.range n).map fun i => some (base + i)

/-- The store with location `l` at index `k`, holes filling any gap before it. -/
def placeAt (ls : List (Option Nat)) (k l : Nat) : List (Option Nat) :=
  (ls ++ List.replicate (k + 1 - ls.length) none).set k (some l)

theorem mem_elemSlots {base n l : Nat} (h : l ∈ (elemSlots base n).filterMap id) :
    base ≤ l ∧ l < base + n := by
  simp only [elemSlots, List.mem_filterMap, List.mem_map, List.mem_range, id] at h
  obtain ⟨o, ⟨i, hi, rfl⟩, he⟩ := h
  simp only [Option.some.injEq] at he
  omega

/-- A grown store names the old locations and the one it was given. -/
theorem mem_placeAt {ls : List (Option Nat)} {k m l : Nat}
    (h : l ∈ (placeAt ls k m).filterMap id) : l ∈ ls.filterMap id ∨ l = m := by
  simp only [placeAt, List.mem_filterMap, id] at h ⊢
  obtain ⟨o, ho, he⟩ := h
  cases o with
  | none => simp at he
  | some x =>
    simp only [Option.some.injEq] at he
    subst he
    rcases List.mem_or_eq_of_mem_set ho with ho | he
    · rcases List.mem_append.mp ho with ho | ho
      · exact Or.inl ⟨some x, ho, rfl⟩
      · simp [List.mem_replicate] at ho
    · exact Or.inr (Option.some.inj he)

/-! Executable structural equality, kept explicit because Lean's deriving
handler does not support nested mutual types such as list-valued applications.
Each recursive comparison visits a strict subterm; no classical decision is used. -/
mutual
def tmDecEq (a b : Tm) : Decidable (a = b) := by
  cases a <;> cases b <;> try (solve | apply isFalse; intro h; cases h)
  case var.var a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.var.injEq])
  case invoke.invoke a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := argsDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.invoke.injEq])
  case construct.construct a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := argsDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.construct.injEq])
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
  case bigint.bigint a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.bigint.injEq])
  case sym.sym a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.sym.injEq])
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
  case indexAt.indexAt a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.indexAt.injEq])
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
  case arr.arr a0 b0 =>
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.arr.injEq])
  case arrLit.arrLit a0 b0 =>
    haveI : Decidable (a0 = b0) := argsDecEq a0 b0
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.arrLit.injEq])
  case elemAt.elemAt a0 a1 b0 b1 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Tm.elemAt.injEq])
  case setElem.setElem a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := tmDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Tm.setElem.injEq])
  case lenOf.lenOf a0 b0 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.lenOf.injEq])
  case spread.spread a0 b0 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.spread.injEq])
  case throw.throw a0 b0 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    exact decidable_of_iff (a0 = b0) (by simp only [Tm.throw.injEq])
termination_by sizeOf a

def callCodeDecEq (a b : CallCode) : Decidable (a = b) := by
  cases a <;> cases b <;> try (solve | apply isFalse; intro h; cases h)
  case absent.absent =>
    exact isTrue rfl
  case closure.closure a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [CallCode.closure.injEq])
  case variadic.variadic a0 a1 b0 b1 =>
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [CallCode.variadic.injEq])
  case bound.bound a0 a1 a2 b0 b1 b2 =>
    haveI : Decidable (a0 = b0) := tmDecEq a0 b0
    haveI : Decidable (a1 = b1) := tmDecEq a1 b1
    haveI : Decidable (a2 = b2) := argsDecEq a2 b2
    exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [CallCode.bound.injEq])
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
def slots (base : Nat) : List PropKey → List (PropKey × Nat)
  | [] => []
  | f :: fs => (f, base) :: slots (base + 1) fs

@[simp] theorem slots_value (base : Nat) : slots base [valueField] = [(valueField, base)] := rfl

@[simp] theorem slots_length (base : Nat) (ns : List PropKey) :
    (slots base ns).length = ns.length := by
  induction ns generalizing base <;> simp_all [slots]

/-- A field of a fresh object stands for the location its position was given.
Distinct names are what makes the map a map: with a repeat, only the first
occurrence is ever found. -/
theorem lookup_slots {ns : List PropKey} (hnd : ns.Nodup) {base i : Nat}
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
    (invoke : ∀ f r args, P f → P r → (∀ a ∈ args, P a) → P (.invoke f r args))
    (construct : ∀ f args, P f → (∀ a ∈ args, P a) → P (.construct f args))
    (letE : ∀ a b, P a → P b → P (.letE a b))
    (nul : P .nul) (undef : P .undef) (tru : P .tru) (fls : P .fls)
    (num : ∀ v, P (.num v))
    (str : ∀ s, P (.str s))
    (bigint : ∀ i, P (.bigint i)) (sym : ∀ i, P (.sym i))
    (objAbsent : ∀ fs, P (.objAt fs .absent))
    (objClosure : ∀ fs n b k, P b → P (.objAt fs (.closure n b k)))
    (attach : ∀ n b k ns args, P b → (∀ a ∈ args, P a) → P (.makeAt (.closure n b k) ns args))
    (objVariadic : ∀ fs n b, P b → P (.objAt fs (.variadic n b)))
    (makeVariadic : ∀ n b ns args, P b → (∀ a ∈ args, P a) → P (.makeAt (.variadic n b) ns args))
    (objBound : ∀ fs t r pre, P t → P r → (∀ a ∈ pre, P a) → P (.objAt fs (.bound t r pre)))
    (makeBound : ∀ t r pre ns args, P t → P r → (∀ a ∈ pre, P a) → (∀ a ∈ args, P a) →
      P (.makeAt (.bound t r pre) ns args))
    (alloc : ∀ ns args, (∀ a ∈ args, P a) → P (.makeAt .absent ns args))
    (read : ∀ f a, P a → P (.readAt f a))
    (index : ∀ a key, P a → P key → P (.indexAt a key))
    (write : ∀ f a b, P a → P b → P (.writeAt f a b))
    (test : ∀ k a, P a → P (.test k a))
    (ite : ∀ c a b, P c → P a → P b → P (.ite c a b))
    (arith : ∀ op a b, P a → P b → P (.arith op a b))
    (arr : ∀ ls, P (.arr ls))
    (arrLit : ∀ inits, (∀ a ∈ inits, P a) → P (.arrLit inits))
    (elemAt : ∀ a i, P a → P i → P (.elemAt a i))
    (setElem : ∀ a i v, P a → P i → P v → P (.setElem a i v))
    (lenOf : ∀ a, P a → P (.lenOf a))
    (spread : ∀ a, P a → P (.spread a))
    (throw : ∀ a, P a → P (.throw a)) (t : Tm) : P t := by
  apply Tm.rec (motive_1 := P)
    (motive_2 := fun c => match c with
      | .absent => True | .closure _ b _ => P b | .variadic _ b => P b
      | .bound t r pre => P t ∧ P r ∧ ∀ a ∈ pre, P a)
    (motive_3 := fun args => ∀ a ∈ args, P a)
    var invoke construct letE nul undef tru fls num str bigint sym ?_ ?_ read index write test ite arith arr arrLit elemAt setElem lenOf spread throw
    True.intro (fun _ _ _ h => h) (fun _ _ h => h) (fun _ _ _ ht hr hp => ⟨ht, hr, hp⟩) (by simp) (by
      intro a args ha ih v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ha
      · exact ih v hv) t
  · intro fs c ih
    cases c with
    | absent => exact objAbsent fs
    | closure n b k => exact objClosure fs n b k ih
    | variadic n b => exact objVariadic fs n b ih
    | bound t r pre => exact objBound fs t r pre ih.1 ih.2.1 ih.2.2
  · intro c ns args ihc iha
    cases c with
    | absent => exact alloc ns args iha
    | closure n b k => exact attach n b k ns args ihc iha
    | variadic n b => exact makeVariadic n b ns args ihc iha
    | bound t r pre => exact makeBound t r pre ns args ihc.1 ihc.2.1 ihc.2.2 iha



abbrev Val := Tm

/-! ## Values and substitution -/


def isVal : Tm → Bool
  | .nul | .undef | .tru | .fls | .num _ | .str _ | .bigint _ | .sym _ | .objAt .. | .arr _ => true
  | _ => false

/-- An operator answers only for two values, and answers a Boolean, a
number, a bigint or a string. -/
theorem primString_val {a : Tm} {s : String} (h : primString a = some s) : isVal a = true := by
  cases a <;> simp [primString] at h <;> rfl

theorem binop_result {op : Arith} {a b v : Tm} (h : binop op a b = some v) :
    isVal a = true ∧ isVal b = true ∧
      (v = .tru ∨ v = .fls ∨ (∃ x, v = .num x) ∨ (∃ i, v = .bigint i) ∨ ∃ s, v = .str s) := by
  have hb : ∀ q, boolVal q = .tru ∨ boolVal q = .fls := fun q => by cases q <;> simp [boolVal]
  unfold binop at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, by rcases hb _ with h | h <;> rw [h] <;> simp⟩)
    | (obtain rfl := Option.some.inj h; exact ⟨rfl, rfl, by simp⟩)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, rfl, by simp⟩)
    | (obtain ⟨_, ht, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, primString_val ht, by simp⟩)
    | (obtain ⟨_, ht, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨primString_val ht, rfl, by simp⟩)

theorem binop_values {op : Arith} {a b v : Tm} (h : binop op a b = some v) :
    isVal a = true ∧ isVal b = true ∧ isVal v = true := by
  obtain ⟨ha, hb, hv⟩ := binop_result h
  refine ⟨ha, hb, ?_⟩
  rcases hv with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

theorem isPrim_val {a : Tm} (h : isPrim a = true) : isVal a = true := by
  cases a <;> simp_all [isPrim, isVal]

theorem isSym_val {a : Tm} (h : isSym a = true) : isVal a = true := by
  cases a <;> simp_all [isSym, isVal]

/-- An operator throws only on two values. -/
theorem binopThrows_values {op : Arith} {a b : Tm} (h : binopThrows op a b = true) :
    isVal a = true ∧ isVal b = true := by
  unfold binopThrows at h
  split at h
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨isSym_val h1, isPrim_val h2⟩
    · exact ⟨isPrim_val h1, isSym_val h2⟩

/-- An operator never both answers and throws. -/
theorem binop_not_throws {op : Arith} {a b v : Tm} (h : binop op a b = some v) :
    binopThrows op a b = false := by
  obtain ⟨ha, hb, -⟩ := binop_values h
  cases a <;> simp [isVal] at ha <;> cases b <;> simp [isVal] at hb <;>
    cases op <;> simp_all [binop, binopThrows, bigintArith, isPrim, isSym, Arith.relational, primString] <;>
    (obtain ⟨_, ⟨h1, _⟩, _⟩ := h; exact h1)

/-- ECMAScript Number::equal on IEEE-754 bits: NaN never equals, and the
sign of zero is ignored. All other equal Numbers have the same encoding. -/
def numberEqual (a b : UInt64) : Bool :=
  let nan := fun (x : UInt64) =>
    (x &&& 0x7ff0000000000000) == 0x7ff0000000000000 &&
      (x &&& 0x000fffffffffffff) != 0
  !nan a && !nan b &&
    (a == b || ((a &&& 0x7fffffffffffffff) == 0 && (b &&& 0x7fffffffffffffff) == 0))

/-- `ToBoolean` of a number: false for the two zeros and NaN, which is the one
double not equal to itself. -/
def numberTruthy (b : UInt64) : Bool := !numberEqual b 0 && numberEqual b b

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
  | .isBigint, .bigint _ => true
  | .isSymbol, .sym _ => true
  | .isRef, .objAt _ .absent => true
  | .isFun, .objAt _ (.closure _ _ _) => true
  | .isFun, .objAt _ (.variadic _ _) => true
  | .isFun, .objAt _ (.bound _ _ _) => true
  | .truthy, .tru => true
  | .truthy, .num b => numberTruthy b
  | .truthy, .str s => s != ""
  | .truthy, .bigint i => i != 0
  | .truthy, .sym _ => true
  | .truthy, .objAt _ _ => true
  | .truthy, .arr _ => true
  | .isArray, .objAt fs .absent => (fs.lookup arrayStoreKey).isSome
  | _, _ => false

mutual
def subst (j : Nat) (a : Tm) : Tm → Tm
  | .var i => if i == j then a else if j < i then .var (i - 1) else .var i
  | .invoke f r args => .invoke (subst j a f) (subst j a r) (substArgs j a args)
  | .construct f args => .construct (subst j a f) (substArgs j a args)
  | .letE x b => .letE (subst j a x) (subst (j + 1) a b)
  | .nul => .nul
  | .undef => .undef
  | .tru => .tru
  | .fls => .fls
  | .num v => .num v
  | .str s => .str s
  | .bigint i => .bigint i
  | .sym i => .sym i
  | .objAt fs .absent => .objAt fs .absent
  | .objAt fs (.closure n b k) => .objAt fs (.closure n (subst (j + n + 1) a b) k)
  | .makeAt (.closure n b k) ns xs => .makeAt (.closure n (subst (j + n + 1) a b) k) ns (substArgs j a xs)
  | .objAt fs (.variadic n b) => .objAt fs (.variadic n (subst (j + n + 2) a b))
  | .makeAt (.variadic n b) ns xs => .makeAt (.variadic n (subst (j + n + 2) a b)) ns (substArgs j a xs)
  | .objAt fs (.bound t r pre) => .objAt fs (.bound (subst j a t) (subst j a r) (substArgs j a pre))
  | .makeAt (.bound t r pre) ns xs =>
      .makeAt (.bound (subst j a t) (subst j a r) (substArgs j a pre)) ns (substArgs j a xs)
  | .makeAt .absent ns xs => .makeAt .absent ns (substArgs j a xs)
  | .readAt f x => .readAt f (subst j a x)
  | .indexAt x key => .indexAt (subst j a x) (subst j a key)
  | .writeAt f x y => .writeAt f (subst j a x) (subst j a y)
  | .test k x => .test k (subst j a x)
  | .ite c x y => .ite (subst j a c) (subst j a x) (subst j a y)
  | .arith op x y => .arith op (subst j a x) (subst j a y)
  | .arr ls => .arr ls
  | .arrLit xs => .arrLit (substArgs j a xs)
  | .elemAt x y => .elemAt (subst j a x) (subst j a y)
  | .setElem x y z => .setElem (subst j a x) (subst j a y) (subst j a z)
  | .lenOf x => .lenOf (subst j a x)
  | .spread x => .spread (subst j a x)
  | .throw x => .throw (subst j a x)

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

/-- Bind the receiver and a prepared argument list without evaluating or
allocating anything: the receiver in slot 0, then the parameters. -/
def bindParameters (arity : Nat) (args : List Tm) (recv : Tm) (body : Tm) : Tm :=
  bindArgs 0 (recv :: parameters arity args) body

/-- The field an array object keeps its store in: `SourceTypes.storeField`. -/
def arrayStoreField : PropKey := arrayStoreKey

/-- The field an object keeps its prototype in. No source property names it:
a read of a key the object lacks continues there (`Step.readProto`). -/
def protoField : PropKey := "[[proto]]"

/-- Variadic dispatch binds the receiver and then the fixed parameters as
`parameters` does, and the actuals after the fixed ones become the store the
body finds in slot 0. Invocation itself still allocates nothing: the yielded
term does, when it runs. The body wraps the store into an array with the
prototype it captured, as an array literal is allocated. -/
def bindRest (fixed : Nat) (args : List Tm) (recv : Tm) (body : Tm) : Tm :=
  .letE (.arrLit (args.drop fixed)) (bindArgs 1 (recv :: parameters fixed args) body)

end CallArguments

abbrev Heap := List Val

/-! ## One small step, threading the heap -/


inductive Step : Heap → Tm → Heap → Tm → Prop where
  | callL : Step h f h' f' → Step h (.invoke f r args) h' (.invoke f' r args)
  /-- The receiver runs after the callee and before every actual. -/
  | callRecv : isVal f = true → Step h r h' r' → Step h (.invoke f r args) h' (.invoke f r' args)
  | callArg : isVal f = true → isVal r = true → args[i]? = some a →
      (∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) →
      Step h a h' a' → Step h (.invoke f r args) h' (.invoke f r (args.set i a'))
  /-- `new` evaluates the constructor, then the actuals left to right, as a
  call does, and runs only `construct` code: `new` on call-only code, and a
  plain call of construct-only code, are stuck, as JavaScript throws. The code
  receives `undefined` for its receiver. -/
  | constructL : Step h f h' f' → Step h (.construct f args) h' (.construct f' args)
  | constructArg : isVal f = true → args[i]? = some a →
      (∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true) →
      Step h a h' a' → Step h (.construct f args) h' (.construct f (args.set i a'))
  | constructV : (∀ a ∈ args, isVal a = true) →
      Step h (.construct (.objAt fs (.closure n b .construct)) args) h
        (CallArguments.bindParameters n args .undef b)
  | letC : Step h a h' a' → Step h (.letE a b) h' (.letE a' b)
  | letV : isVal a = true → Step h (.letE a b) h (subst 0 a b)
  /-- Invocation executes the object's stored code in one step. -/
  | callV : isVal r = true → (∀ a ∈ args, isVal a = true) →
      Step h (.invoke (.objAt fs (.closure n b)) r args) h (CallArguments.bindParameters n args r b)
  /-- Variadic invocation likewise takes one step and changes no heap. -/
  | callRest : isVal r = true → (∀ a ∈ args, isVal a = true) →
      Step h (.invoke (.objAt fs (.variadic n b)) r args) h (CallArguments.bindRest n args r b)
  /-- A bound function forwards in one step: the receiver of this call is
  dropped, the saved one used, and the prefix goes before the actuals. -/
  | callBound : isVal r = true → (∀ a ∈ args, isVal a = true) →
      Step h (.invoke (.objAt fs (.bound t r₀ pre)) r args) h (.invoke t r₀ (pre ++ args))
  /-- A spread actual whose store is ready is replaced by the store's elements
  once every earlier actual is a value, so later actuals run after the read. -/
  | spreadC : Step h a h' a' → Step h (.spread a) h' (.spread a')
  | callSpread {args pre post : List Tm} {ls : List (Option Nat)} {vs : List Tm} :
      isVal f = true → isVal r = true → args = pre ++ .spread (.arr ls) :: post →
      (∀ v ∈ pre, isVal v = true) →
      readElems h ls = some vs → Step h (.invoke f r args) h (.invoke f r (pre ++ vs ++ post))
  /-- Initializers are evaluated left to right, like actual arguments. -/
  | makeArg {c : CallCode} {ns : List PropKey} {inits : List Tm} {i : Nat}
      {h h' : Heap} {a a' : Tm} : inits[i]? = some a →
      (∀ j, j < i → ∀ v, inits[j]? = some v → isVal v = true) →
      Step h a h' a' → Step h (.makeAt c ns inits) h' (.makeAt c ns (inits.set i a'))
  /-- Allocation takes one fresh location per named field, in order. -/
  | makeFields {c : CallCode} {ns : List PropKey} {vs : List Tm} {h : Heap} :
      (∀ v ∈ vs, isVal v = true) → ns.length = vs.length →
      Step h (.makeAt c ns vs) (h ++ vs) (.objAt (slots h.length ns) c)
  | readC : Step h a h' a' → Step h (.readAt f a) h' (.readAt f a')
  /-- Reading and writing a field go to its location, whatever the object's code. -/
  | readField {f : PropKey} {fs : List (PropKey × Nat)} {c : CallCode} {l : Nat}
      {h : Heap} {v : Val} : fs.lookup f = some l → h[l]? = some v →
      Step h (.readAt f (.objAt fs c)) h v
  /-- A key the object lacks is read from its prototype, when it has one. -/
  | readProto {f : PropKey} {fs : List (PropKey × Nat)} {c : CallCode} {l : Nat}
      {h : Heap} {p : Val} : fs.lookup f = none → fs.lookup CallArguments.protoField = some l →
      h[l]? = some p → Step h (.readAt f (.objAt fs c)) h (.readAt f p)
  /-- JavaScript property lookup produces undefined when the name is absent
  and there is no prototype to continue at. -/
  | readMissing {f : PropKey} {fs : List (PropKey × Nat)} {c : CallCode} {h : Heap} :
      fs.lookup f = none → fs.lookup CallArguments.protoField = none →
      Step h (.readAt f (.objAt fs c)) h .undef
  | indexC1 : Step h a h' a' → Step h (.indexAt a key) h' (.indexAt a' key)
  | indexC2 : isVal a = true → Step h key h' key' →
      Step h (.indexAt a key) h' (.indexAt a key')
  | indexField {f : String} {fs : List (PropKey × Nat)} {c : CallCode} {l : Nat}
      {h : Heap} {v : Val} : fs.lookup (.str f) = some l → h[l]? = some v →
      Step h (.indexAt (.objAt fs c) (.str f)) h v
  | indexProto {f : String} {fs : List (PropKey × Nat)} {c : CallCode} {l : Nat}
      {h : Heap} {p : Val} : fs.lookup (.str f) = none → fs.lookup CallArguments.protoField = some l →
      h[l]? = some p → Step h (.indexAt (.objAt fs c) (.str f)) h (.indexAt p (.str f))
  | indexMissing {f : String} {fs : List (PropKey × Nat)} {c : CallCode} {h : Heap} :
      fs.lookup (.str f) = none → fs.lookup CallArguments.protoField = none →
      Step h (.indexAt (.objAt fs c) (.str f)) h .undef
  | writeC1 : Step h a h' a' → Step h (.writeAt f a b) h' (.writeAt f a' b)
  | writeC2 : isVal a = true → Step h b h' b' → Step h (.writeAt f a b) h' (.writeAt f a b')
  | writeField {f : PropKey} {fs : List (PropKey × Nat)} {c : CallCode} {l : Nat}
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
  /-- Two values combine in one step where `binop` answers for them. -/
  | arithV : binop op a b = some v → Step h (.arith op a b) h v
  /-- Store initializers are evaluated left to right, like fields. -/
  | arrArg {inits : List Tm} {i : Nat} {h h' : Heap} {a a' : Tm} : inits[i]? = some a →
      (∀ j, j < i → ∀ v, inits[j]? = some v → isVal v = true) →
      Step h a h' a' → Step h (.arrLit inits) h' (.arrLit (inits.set i a'))
  /-- A spread among a literal's initializers is replaced by its store's
  elements once every earlier initializer is a value, as in a call. -/
  | arrSpread {inits pre post : List Tm} {ls : List (Option Nat)} {vs : List Tm} {h : Heap} :
      inits = pre ++ .spread (.arr ls) :: post → (∀ v ∈ pre, isVal v = true) →
      readElems h ls = some vs → Step h (.arrLit inits) h (.arrLit (pre ++ vs ++ post))
  /-- A store takes one fresh location per element, in order. -/
  | arrAlloc {vs : List Tm} {h : Heap} : (∀ v ∈ vs, isVal v = true) →
      Step h (.arrLit vs) (h ++ vs) (.arr (elemSlots h.length vs.length))
  | elemC1 : Step h a h' a' → Step h (.elemAt a i) h' (.elemAt a' i)
  | elemC2 : isVal a = true → Step h i h' i' → Step h (.elemAt a i) h' (.elemAt a i')
  /-- An index naming a location reads it; any other reads `undefined`. -/
  | elemRead {ls : List (Option Nat)} {b : UInt64} {l : Nat} {h : Heap} {v : Val} :
      elemLoc ls b = some l → h[l]? = some v → Step h (.elemAt (.arr ls) (.num b)) h v
  | elemAbsent {ls : List (Option Nat)} {b : UInt64} {h : Heap} :
      elemLoc ls b = none → Step h (.elemAt (.arr ls) (.num b)) h .undef
  | setC1 : Step h a h' a' → Step h (.setElem a i v) h' (.setElem a' i v)
  | setC2 : isVal a = true → Step h i h' i' → Step h (.setElem a i v) h' (.setElem a i' v)
  | setC3 : isVal a = true → isVal i = true → Step h v h' v' →
      Step h (.setElem a i v) h' (.setElem a i v')
  /-- A present element's location takes the value; the store is unchanged. -/
  | setPresent {ls : List (Option Nat)} {b : UInt64} {l : Nat} {h : Heap} {v : Val} :
      isVal v = true → elemLoc ls b = some l → l < h.length →
      Step h (.setElem (.arr ls) (.num b) v) (h.set l v) (.arr ls)
  /-- A hole or an index past the end takes a fresh location, which the new
  store records; holes fill any gap. -/
  | setGrow {ls : List (Option Nat)} {b : UInt64} {k : Nat} {h : Heap} {v : Val} :
      isVal v = true → indexOfBits b = some k → elemLoc ls b = none →
      Step h (.setElem (.arr ls) (.num b) v) (h ++ [v]) (.arr (placeAt ls k h.length))
  | lenC : Step h a h' a' → Step h (.lenOf a) h' (.lenOf a')
  | lenV {ls : List (Option Nat)} {h : Heap} : Step h (.lenOf (.arr ls)) h (.num (bitsOfNat ls.length))
  /-- A string's length is its count of UTF-16 code units. -/
  | lenStr {s : String} {h : Heap} :
      Step h (.lenOf (.str s)) h (.num (bitsOfNat (utf16Units s).length))
  /-- A string's own index property: the code unit at an index below its
  length, `undefined` at any other number. -/
  | elemStr {s : String} {b : UInt64} {h : Heap} :
      Step h (.elemAt (.str s) (.num b)) h (codeUnitAt s b)
  /-- A throw's operand is evaluated first. -/
  | throwC : Step h a h' a' → Step h (.throw a) h' (.throw a')
  /-- Two values an operator throws on step to throwing a fresh error object. -/
  | arithThrow : binopThrows op a b = true → Step h (.arith op a b) h (.throw thrownError)

/-- **A term that throws.** `Raises t v`: `t` is `throw v` for a value `v`, in
evaluation position: under exactly the contexts `Step` evaluates in, each
constructor here the congruence rule of the same name with a throw in place of
a step. Such a term does not step (`raises_no_step`); the thrown value leaves
every context it is in, until a handler catches it. -/
inductive Raises : Tm → Tm → Prop where
  | throwV : isVal v = true → Raises (.throw v) v
  | throwC : Raises a v → Raises (.throw a) v
  | callL : Raises f v → Raises (.invoke f r args) v
  | callRecv : isVal f = true → Raises r v → Raises (.invoke f r args) v
  | callArg {f r a v : Tm} {args : List Tm} {i : Nat} :
      isVal f = true → isVal r = true → args[i]? = some a →
      (∀ j, j < i → ∀ w, args[j]? = some w → isVal w = true) →
      Raises a v → Raises (.invoke f r args) v
  | constructL : Raises f v → Raises (.construct f args) v
  | constructArg {f a v : Tm} {args : List Tm} {i : Nat} :
      isVal f = true → args[i]? = some a →
      (∀ j, j < i → ∀ w, args[j]? = some w → isVal w = true) →
      Raises a v → Raises (.construct f args) v
  | letC : Raises a v → Raises (.letE a b) v
  | spreadC : Raises a v → Raises (.spread a) v
  | makeArg {c : CallCode} {ns : List PropKey} {inits : List Tm} {i : Nat} {a v : Tm} :
      inits[i]? = some a →
      (∀ j, j < i → ∀ w, inits[j]? = some w → isVal w = true) →
      Raises a v → Raises (.makeAt c ns inits) v
  | readC : Raises a v → Raises (.readAt f a) v
  | indexC1 : Raises a v → Raises (.indexAt a key) v
  | indexC2 : isVal a = true → Raises key v → Raises (.indexAt a key) v
  | writeC1 : Raises a v → Raises (.writeAt f a b) v
  | writeC2 : isVal a = true → Raises b v → Raises (.writeAt f a b) v
  | testC : Raises a v → Raises (.test k a) v
  | iteC : Raises c v → Raises (.ite c t e) v
  | arithC1 : Raises a v → Raises (.arith op a b) v
  | arithC2 : isVal a = true → Raises b v → Raises (.arith op a b) v
  | arrArg {inits : List Tm} {i : Nat} {a v : Tm} : inits[i]? = some a →
      (∀ j, j < i → ∀ w, inits[j]? = some w → isVal w = true) →
      Raises a v → Raises (.arrLit inits) v
  | elemC1 : Raises a v → Raises (.elemAt a i) v
  | elemC2 : isVal a = true → Raises i v → Raises (.elemAt a i) v
  | setC1 : Raises a v → Raises (.setElem a i x) v
  | setC2 : isVal a = true → Raises i v → Raises (.setElem a i x) v
  | setC3 : isVal a = true → isVal i = true → Raises x v → Raises (.setElem a i x) v
  | lenC : Raises a v → Raises (.lenOf a) v

/-! ### The one-field rules

Each is the single-field instance of the rule above it, and carries the name
and the statement the development used before fields were named. -/

@[simp] theorem lookup_value (l : Nat) : ([(valueField, l)] : List (PropKey × Nat)).lookup valueField = some l := by
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
  .callArg (i := 0) hv rfl rfl (by intro j hj; omega) hs

/-- Inversion for the source pipeline's singleton argument lists. -/
theorem singleton_get {a b : Tm} {i : Nat} (h : [a][i]? = some b) : i = 0 ∧ b = a := by
  have hi := (List.getElem?_eq_some_iff.mp h).1
  have he : i = 0 := by simpa using hi
  subst i
  exact ⟨rfl, (Option.some.inj h).symm⟩

/-- The existing unary beta rule is a specialization of list dispatch. -/
theorem Step.beta {fs : List (PropKey × Nat)} (ha : isVal a = true) :
    Step h (.app (.objAt fs (.closure n b)) a) h (CallArguments.bindParameters n [a] .undef b) :=
  .callV rfl (by simpa using ha)

theorem value_no_step {v : Val} (hv : isVal v = true) {h h' t} : ¬ Step h v h' t := by
  intro hs
  cases v <;> simp [isVal] at hv <;> cases hs

theorem spread_arr_no_step {ls h h' t} : ¬ Step h (.spread (.arr ls)) h' t := by
  intro hs
  cases hs with
  | spreadC s => exact value_no_step rfl s

/-- A list with a spread in it is not all values. -/
theorem spread_not_values {args pre post : List Tm} {a : Tm}
    (he : args = pre ++ .spread a :: post) (hv : ∀ v ∈ args, isVal v = true) : False := by
  have := hv (.spread a) (by simp [he])
  simp [isVal] at this

/-- A spread whose store is ready is the first actual still to run, so no
earlier actual steps and it has no step of its own. -/
theorem spread_blocks_arg {args pre post : List Tm} {ls : List (Option Nat)}
    (he : args = pre ++ .spread (.arr ls) :: post) (hpre : ∀ v ∈ pre, isVal v = true)
    {i : Nat} {a : Tm} (hg : args[i]? = some a)
    (hb : ∀ j, j < i → ∀ v, args[j]? = some v → isVal v = true)
    {h h' a'} (s : Step h a h' a') : False := by
  subst he
  rcases Nat.lt_trichotomy i pre.length with hi | hi | hi
  · rw [List.getElem?_append_left hi] at hg
    exact value_no_step (hpre a (List.mem_of_getElem? hg)) s
  · subst hi
    rw [List.getElem?_append_right (Nat.le_refl _)] at hg
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hg
    subst hg
    exact spread_arr_no_step s
  · have := hb pre.length hi (.spread (.arr ls)) (by simp)
    simp [isVal] at this

/-- The first actual that is not a value is where a list splits. -/
theorem split_unique {pre post pre' post' : List Tm} {x x' : Tm}
    (he : pre ++ x :: post = pre' ++ x' :: post')
    (hp : ∀ v ∈ pre, isVal v = true) (hp' : ∀ v ∈ pre', isVal v = true)
    (hx : isVal x = false) (hx' : isVal x' = false) : pre = pre' ∧ x = x' ∧ post = post' := by
  induction pre generalizing pre' with
  | nil =>
    cases pre' with
    | nil => simp_all
    | cons y pre' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      have := hp' y (by simp)
      rw [← he.1] at this
      simp [hx] at this
  | cons y pre ih =>
    cases pre' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      have := hp y (by simp)
      rw [he.1] at this
      simp [hx'] at this
    | cons y' pre' =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl, rfl⟩ := ih he (fun v hv => hp v (by simp [hv]))
        (fun v hv => hp' v (by simp [hv]))
      exact ⟨rfl, rfl, rfl⟩

theorem nul_no_step {h h' t} : ¬ Step h .nul h' t := by intro s; cases s
theorem tru_no_step {h h' t} : ¬ Step h .tru h' t := by intro s; cases s
theorem fls_no_step {h h' t} : ¬ Step h .fls h' t := by intro s; cases s
theorem obj_no_step {h fs c h' t} : ¬ Step h (.objAt fs c) h' t := by intro s; cases s

/-! ## Divergence

`omegaTm` steps to itself forever. It is the inhabitant of last resort: safe at
every budget, since safety asks for progress and not termination. -/

def delta : Tm := .fn 0 (.app (.var 1) (.var 1))
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
  | callRecv _ hs => exact value_no_step rfl hs
  | callArg _ _ hg _ hs =>
    obtain ⟨rfl, rfl⟩ := singleton_get hg
    exact nul_no_step hs
  | callSpread _ _ he _ _ => exact spread_not_values he (by simp [isVal])

theorem closed_omega : Closed omegaTm := by
  intro k a
  simp [omegaTm, delta, subst]

/-- **Evaluation is deterministic.** One term in one heap has at most one next
state. Nothing in the safety definition says so — it quantifies existentially
over the world a step lands in — so this has to be proved, and it is what lets
two independent runs of the same program be compared. -/
theorem Step_det {h t h1 t1 h2 t2} (s1 : Step h t h1 t1) (s2 : Step h t h2 t2) :
    h1 = h2 ∧ t1 = t2 := by
  induction s1 generalizing h2 t2 with
  | constructL s ih =>
    cases s2 with
    | constructL s' => exact (ih s').imp id (congrArg (Tm.construct · _))
    | constructArg hv _ _ _ => exact False.elim (value_no_step hv s)
    | constructV => exact False.elim (obj_no_step s)
  | @constructArg f args i a h h1 a1 hv hg hb s ih =>
    cases s2 with
    | constructL s' => exact False.elim (value_no_step hv s')
    | @constructArg _ _ j b _ _ b1 _ hg' hb' s' =>
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
    | constructV hvs => exact False.elim (value_no_step (hvs a (List.mem_of_getElem? hg)) s)
  | constructV hvs =>
    cases s2 with
    | constructL s' => exact False.elim (obj_no_step s')
    | constructArg _ hg _ s' => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s')
    | constructV _ => exact ⟨rfl, rfl⟩
  | callL s ih =>
    cases s2 with
    | callL s' => exact (ih s').imp id (congrArg (Tm.invoke · _ _))
    | callRecv hv _ => exact False.elim (value_no_step hv s)
    | callArg hv _ _ _ _ => exact False.elim (value_no_step hv s)
    | callV => exact False.elim (obj_no_step s)
    | callRest => exact False.elim (obj_no_step s)
    | callBound => exact False.elim (obj_no_step s)
    | callSpread hv _ _ _ _ => exact False.elim (value_no_step hv s)
  | callRecv hf s ih =>
    cases s2 with
    | callL s' => exact False.elim (value_no_step hf s')
    | callRecv _ s' => exact (ih s').imp id (congrArg (Tm.invoke _ · _))
    | callArg _ hr _ _ _ => exact False.elim (value_no_step hr s)
    | callV hr _ => exact False.elim (value_no_step hr s)
    | callRest hr _ => exact False.elim (value_no_step hr s)
    | callBound hr _ => exact False.elim (value_no_step hr s)
    | callSpread _ hr _ _ _ => exact False.elim (value_no_step hr s)
  | @callArg f r args i a h h1 a1 hv hrv hg hb s ih =>
    cases s2 with
    | callL s' => exact False.elim (value_no_step hv s')
    | callRecv _ s' => exact False.elim (value_no_step hrv s')
    | @callArg _ _ _ j b _ _ b1 _ _ hg' hb' s' =>
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
    | callV _ hvs => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s)
    | callRest _ hvs => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s)
    | callBound _ hvs => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s)
    | callSpread _ _ he hpre _ => exact False.elim (spread_blocks_arg he hpre hg hb s)
  | spreadC s ih =>
    cases s2 with
    | spreadC s' => exact (ih s').imp id (congrArg Tm.spread)
  | callSpread hf hr he hpre hre =>
    cases s2 with
    | callL s' => exact False.elim (value_no_step hf s')
    | callRecv _ s' => exact False.elim (value_no_step hr s')
    | callArg _ _ hg hb s' => exact False.elim (spread_blocks_arg he hpre hg hb s')
    | callV _ hvs => exact False.elim (spread_not_values he hvs)
    | callRest _ hvs => exact False.elim (spread_not_values he hvs)
    | callBound _ hvs => exact False.elim (spread_not_values he hvs)
    | callSpread _ _ he' hpre' hre' =>
      obtain ⟨rfl, hx, rfl⟩ := split_unique (he.symm.trans he') hpre hpre' rfl rfl
      cases hx
      cases Option.some.inj (hre.symm.trans hre')
      exact ⟨rfl, rfl⟩
  | letC hs ih =>
    cases s2 with
    | letC hs' => exact (ih hs').imp id (congrArg (Tm.letE · _))
    | letV hv => exact absurd hs (value_no_step hv)
  | letV hv =>
    cases s2 with
    | letC hs => exact absurd hs (value_no_step hv)
    | letV => exact ⟨rfl, rfl⟩
  | callV hr hv =>
    cases s2 with
    | callL hs => exact absurd hs obj_no_step
    | callRecv _ hs => exact absurd hs (value_no_step hr)
    | callArg _ _ hg _ hs => exact absurd hs (value_no_step (hv _ (List.mem_of_getElem? hg)))
    | callV => exact ⟨rfl, rfl⟩
    | callSpread _ _ he _ _ => exact False.elim (spread_not_values he hv)
  | callRest hr hv =>
    cases s2 with
    | callL hs => exact absurd hs obj_no_step
    | callRecv _ hs => exact absurd hs (value_no_step hr)
    | callArg _ _ hg _ hs => exact absurd hs (value_no_step (hv _ (List.mem_of_getElem? hg)))
    | callRest => exact ⟨rfl, rfl⟩
    | callSpread _ _ he _ _ => exact False.elim (spread_not_values he hv)
  | callBound hr hv =>
    cases s2 with
    | callL hs => exact absurd hs obj_no_step
    | callRecv _ hs => exact absurd hs (value_no_step hr)
    | callArg _ _ hg _ hs => exact absurd hs (value_no_step (hv _ (List.mem_of_getElem? hg)))
    | callBound => exact ⟨rfl, rfl⟩
    | callSpread _ _ he _ _ => exact False.elim (spread_not_values he hv)
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
    | readProto _ _ _ => exact absurd s obj_no_step
    | readMissing _ _ => exact absurd s obj_no_step
  | readField hl he =>
    cases s2 with
    | readC s' => exact absurd s' obj_no_step
    | readField hl' he' =>
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, Option.some.inj (he.symm.trans he')⟩
    | readProto hm _ _ => simp [hl] at hm
    | readMissing hm _ => simp [hl] at hm
  | readProto hm hp he =>
    cases s2 with
    | readC s' => exact absurd s' obj_no_step
    | readField hl _ => simp [hm] at hl
    | readProto _ hp' he' =>
      cases Option.some.inj (hp.symm.trans hp')
      cases Option.some.inj (he.symm.trans he')
      exact ⟨rfl, rfl⟩
    | readMissing _ hn => simp [hp] at hn
  | readMissing hm hn =>
    cases s2 with
    | readC s' => exact absurd s' obj_no_step
    | readField hl _ => simp [hm] at hl
    | readProto _ hp _ => simp [hn] at hp
    | readMissing _ _ => exact ⟨rfl, rfl⟩
  | indexC1 s ih =>
    cases s2 with
    | indexC1 s' => exact (ih s').imp id (congrArg (Tm.indexAt · _))
    | indexC2 hv _ => exact False.elim (value_no_step hv s)
    | indexField _ _ => exact absurd s obj_no_step
    | indexProto _ _ _ => exact absurd s obj_no_step
    | indexMissing _ _ => exact absurd s obj_no_step
  | indexC2 hv s ih =>
    cases s2 with
    | indexC1 s' => exact False.elim (value_no_step hv s')
    | indexC2 _ s' => exact (ih s').imp id (congrArg (Tm.indexAt _ ·))
    | indexField _ _ => exact False.elim (value_no_step rfl s)
    | indexProto _ _ _ => exact False.elim (value_no_step rfl s)
    | indexMissing _ _ => exact False.elim (value_no_step rfl s)
  | indexField hl he =>
    cases s2 with
    | indexC1 s' => exact absurd s' obj_no_step
    | indexC2 _ s' => exact False.elim (value_no_step rfl s')
    | indexField hl' he' =>
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, Option.some.inj (he.symm.trans he')⟩
    | indexProto hm _ _ => simp [hl] at hm
    | indexMissing hm _ => simp [hl] at hm
  | indexProto hm hp he =>
    cases s2 with
    | indexC1 s' => exact absurd s' obj_no_step
    | indexC2 _ s' => exact False.elim (value_no_step rfl s')
    | indexField hl _ => simp [hm] at hl
    | indexProto _ hp' he' =>
      cases Option.some.inj (hp.symm.trans hp')
      cases Option.some.inj (he.symm.trans he')
      exact ⟨rfl, rfl⟩
    | indexMissing _ hn => simp [hp] at hn
  | indexMissing hm hn =>
    cases s2 with
    | indexC1 s' => exact absurd s' obj_no_step
    | indexC2 _ s' => exact False.elim (value_no_step rfl s')
    | indexField hl _ => simp [hm] at hl
    | indexProto _ hp _ => simp [hn] at hp
    | indexMissing _ _ => exact ⟨rfl, rfl⟩
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
    | arithV hb => exact absurd s (by intro hs; exact value_no_step (binop_values hb).1 hs)
    | arithThrow ht => exact absurd s (by intro hs; exact value_no_step (binopThrows_values ht).1 hs)
  | arithC2 hv s ih =>
    cases s2 with
    | arithC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | arithC2 _ s' => exact (ih s').imp id (congrArg (Tm.arith _ _ ·))
    | arithV hb => exact absurd s (by intro hs; exact value_no_step (binop_values hb).2.1 hs)
    | arithThrow ht => exact absurd s (by intro hs; exact value_no_step (binopThrows_values ht).2 hs)
  | arithV hb =>
    cases s2 with
    | arithC1 s' => exact absurd s' (by intro hs; exact value_no_step (binop_values hb).1 hs)
    | arithC2 _ s' => exact absurd s' (by intro hs; exact value_no_step (binop_values hb).2.1 hs)
    | arithV hb' => exact ⟨rfl, Option.some.inj (hb.symm.trans hb')⟩
    | arithThrow ht => simp [binop_not_throws hb] at ht
  | arithThrow ht =>
    cases s2 with
    | arithC1 s' => exact absurd s' (by intro hs; exact value_no_step (binopThrows_values ht).1 hs)
    | arithC2 _ s' => exact absurd s' (by intro hs; exact value_no_step (binopThrows_values ht).2 hs)
    | arithV hb => simp [binop_not_throws hb] at ht
    | arithThrow _ => exact ⟨rfl, rfl⟩
  | throwC s ih =>
    cases s2 with
    | throwC s' => exact (ih s').imp id (congrArg Tm.throw)
  | @arrArg inits i h h1 a a1 hg hb s ih =>
    cases s2 with
    | @arrArg _ j _ _ b b1 hg' hb' s' =>
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
    | arrAlloc hvs => exact False.elim (value_no_step (hvs _ (List.mem_of_getElem? hg)) s)
    | arrSpread he hpre _ => exact False.elim (spread_blocks_arg he hpre hg hb s)
  | arrSpread he hpre hr =>
    cases s2 with
    | arrArg hg hb s' => exact False.elim (spread_blocks_arg he hpre hg hb s')
    | arrAlloc hvs => exact False.elim (spread_not_values he hvs)
    | arrSpread he' hpre' hr' =>
      obtain ⟨rfl, hx, rfl⟩ := split_unique (he.symm.trans he') hpre hpre' rfl rfl
      cases hx
      cases Option.some.inj (hr.symm.trans hr')
      exact ⟨rfl, rfl⟩
  | arrAlloc hv =>
    cases s2 with
    | arrArg hg _ s' => exact False.elim (value_no_step (hv _ (List.mem_of_getElem? hg)) s')
    | arrAlloc _ => exact ⟨rfl, rfl⟩
    | arrSpread he _ _ => exact False.elim (spread_not_values he hv)
  | elemC1 s ih =>
    cases s2 with
    | elemC1 s' => exact (ih s').imp id (congrArg (Tm.elemAt · _))
    | elemC2 hv _ => exact absurd s (by intro hs; exact value_no_step hv hs)
    | elemRead _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | elemAbsent _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | elemStr => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | elemC2 hv s ih =>
    cases s2 with
    | elemC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | elemC2 _ s' => exact (ih s').imp id (congrArg (Tm.elemAt _ ·))
    | elemRead _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | elemAbsent _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | elemStr => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | elemRead hl hv =>
    cases s2 with
    | elemC1 s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemC2 _ s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemRead hl' hv' =>
      cases Option.some.inj (hl.symm.trans hl')
      cases Option.some.inj (hv.symm.trans hv')
      exact ⟨rfl, rfl⟩
    | elemAbsent hn => exact absurd (hl.symm.trans hn) (by simp)
  | elemAbsent hn =>
    cases s2 with
    | elemC1 s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemC2 _ s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemRead hl' _ => exact absurd (hn.symm.trans hl') (by simp)
    | elemAbsent _ => exact ⟨rfl, rfl⟩
  | setC1 s ih =>
    cases s2 with
    | setC1 s' => exact (ih s').imp id (congrArg (Tm.setElem · _ _))
    | setC2 hv _ => exact absurd s (by intro hs; exact value_no_step hv hs)
    | setC3 hv _ _ => exact absurd s (by intro hs; exact value_no_step hv hs)
    | setPresent _ _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | setGrow _ _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | setC2 hv s ih =>
    cases s2 with
    | setC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | setC2 _ s' => exact (ih s').imp id (congrArg (Tm.setElem _ · _))
    | setC3 _ hi _ => exact absurd s (by intro hs; exact value_no_step hi hs)
    | setPresent _ _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | setGrow _ _ _ => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | setC3 hv hi s ih =>
    cases s2 with
    | setC1 s' => exact absurd s' (by intro hs; exact value_no_step hv hs)
    | setC2 _ s' => exact absurd s' (by intro hs; exact value_no_step hi hs)
    | setC3 _ _ s' => exact (ih s').imp id (congrArg (Tm.setElem _ _ ·))
    | setPresent hw _ _ => exact absurd s (by intro hs; exact value_no_step hw hs)
    | setGrow hw _ _ => exact absurd s (by intro hs; exact value_no_step hw hs)
  | setPresent hw hl hlt =>
    cases s2 with
    | setC1 s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | setC2 _ s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | setC3 _ _ s' => exact absurd s' (by intro hs; exact value_no_step hw hs)
    | setPresent _ hl' _ =>
      cases Option.some.inj (hl.symm.trans hl')
      exact ⟨rfl, rfl⟩
    | setGrow _ _ hn => exact absurd (hl.symm.trans hn) (by simp)
  | setGrow hw hk hn =>
    cases s2 with
    | setC1 s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | setC2 _ s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | setC3 _ _ s' => exact absurd s' (by intro hs; exact value_no_step hw hs)
    | setPresent _ hl' _ => exact absurd (hn.symm.trans hl') (by simp)
    | setGrow _ hk' _ =>
      cases Option.some.inj (hk.symm.trans hk')
      exact ⟨rfl, rfl⟩
  | lenC s ih =>
    cases s2 with
    | lenC s' => exact (ih s').imp id (congrArg Tm.lenOf)
    | lenV => exact absurd s (by intro hs; exact value_no_step rfl hs)
    | lenStr => exact absurd s (by intro hs; exact value_no_step rfl hs)
  | lenV =>
    cases s2 with
    | lenC s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | lenV => exact ⟨rfl, rfl⟩
  | lenStr =>
    cases s2 with
    | lenC s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | lenStr => exact ⟨rfl, rfl⟩
  | elemStr =>
    cases s2 with
    | elemC1 s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemC2 _ s' => exact absurd s' (by intro hs; exact value_no_step rfl hs)
    | elemStr => exact ⟨rfl, rfl⟩

/-! ### Throwing

A throwing term is neither a value nor a term that steps, and the value it
throws is determined. -/

theorem raises_not_val {t v : Tm} (h : Raises t v) : isVal t = false := by
  cases h <;> rfl

theorem raises_val {t v : Tm} (h : Raises t v) : isVal v = true := by
  induction h <;> assumption

/-- In a list evaluated left to right, the first entry that is not a value is
determined: two such positions with only values before each coincide. -/
theorem first_nonval_unique {xs : List Tm} {i j : Nat} {a b : Tm}
    (ha : xs[i]? = some a) (hb : xs[j]? = some b)
    (hi : ∀ k, k < i → ∀ w, xs[k]? = some w → isVal w = true)
    (hj : ∀ k, k < j → ∀ w, xs[k]? = some w → isVal w = true)
    (na : isVal a = false) (nb : isVal b = false) : i = j ∧ a = b := by
  have hij : i = j := by
    rcases Nat.lt_trichotomy i j with h | h | h
    · have := hj i h a ha; simp [na] at this
    · exact h
    · have := hi j h b hb; simp [nb] at this
  subst hij
  exact ⟨rfl, Option.some.inj (ha.symm.trans hb)⟩

theorem not_val_of_step {h h' t t'} (s : Step h t h' t') : isVal t = false := by
  cases ht : isVal t
  · rfl
  · exact False.elim (value_no_step ht s)

/-- A spread whose store is ready never throws. -/
theorem spread_arr_no_raise {ls : List (Option Nat)} {v : Tm} : ¬ Raises (.spread (.arr ls)) v := by
  intro h; cases h with | spreadC h => cases h

/-- A ready spread is the first actual still to run: nothing before it throws. -/
theorem spread_blocks_raise {args pre post : List Tm} {ls : List (Option Nat)}
    (he : args = pre ++ .spread (.arr ls) :: post) (hpre : ∀ w ∈ pre, isVal w = true)
    {i : Nat} {a v : Tm} (hg : args[i]? = some a)
    (hb : ∀ j, j < i → ∀ w, args[j]? = some w → isVal w = true)
    (hr : Raises a v) : False := by
  subst he
  rcases Nat.lt_trichotomy i pre.length with hi | hi | hi
  · rw [List.getElem?_append_left hi] at hg
    have := hpre a (List.mem_of_getElem? hg)
    rw [raises_not_val hr] at this; contradiction
  · subst hi
    rw [List.getElem?_append_right (Nat.le_refl _)] at hg
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hg
    subst hg
    exact spread_arr_no_raise hr
  · have := hb pre.length hi (.spread (.arr ls)) (by simp)
    simp [isVal] at this

/-- The entry after a prefix of values is the first one still to run. -/
theorem prefix_position {pre rest : List Tm} {t : Tm} (hp : ∀ w ∈ pre, isVal w = true) :
    (pre ++ t :: rest)[pre.length]? = some t ∧
      ∀ j, j < pre.length → ∀ w, (pre ++ t :: rest)[j]? = some w → isVal w = true := by
  refine ⟨by simp, ?_⟩
  intro j hj w hw
  rw [List.getElem?_append_left hj] at hw
  exact hp w (List.mem_of_getElem? hw)

/-- **A throwing term does not step.** -/
theorem raises_no_step {t v : Tm} (hr : Raises t v) : ∀ {h h' t'}, ¬ Step h t h' t' := by
  induction hr with
  | throwV hv => intro _ _ _ s; cases s with | throwC s => exact value_no_step hv s
  | throwC _ ih => intro _ _ _ s; cases s with | throwC s => exact ih s
  | callL hf ih =>
    intro _ _ _ s
    cases s with
    | callL s => exact ih s
    | callRecv hv _ => rw [raises_not_val hf] at hv; contradiction
    | callArg hv _ _ _ _ => rw [raises_not_val hf] at hv; contradiction
    | callV => cases hf
    | callRest => cases hf
    | callBound => cases hf
    | callSpread hv _ _ _ _ => rw [raises_not_val hf] at hv; contradiction
  | callRecv hfv hr ih =>
    intro _ _ _ s
    cases s with
    | callL s => exact value_no_step hfv s
    | callRecv _ s => exact ih s
    | callArg _ hv _ _ _ => rw [raises_not_val hr] at hv; contradiction
    | callV hv _ => rw [raises_not_val hr] at hv; contradiction
    | callRest hv _ => rw [raises_not_val hr] at hv; contradiction
    | callBound hv _ => rw [raises_not_val hr] at hv; contradiction
    | callSpread _ hv _ _ _ => rw [raises_not_val hr] at hv; contradiction
  | callArg hfv hrv hg hb hr ih =>
    intro _ _ _ s
    cases s with
    | callL s => exact value_no_step hfv s
    | callRecv _ s => exact value_no_step hrv s
    | callArg _ _ hg' hb' s =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val hr) (not_val_of_step s)
      exact ih s
    | callV _ hvs => have := hvs _ (List.mem_of_getElem? hg); rw [raises_not_val hr] at this; contradiction
    | callRest _ hvs => have := hvs _ (List.mem_of_getElem? hg); rw [raises_not_val hr] at this; contradiction
    | callBound _ hvs => have := hvs _ (List.mem_of_getElem? hg); rw [raises_not_val hr] at this; contradiction
    | callSpread _ _ he hpre _ => exact spread_blocks_raise he hpre hg hb hr
  | constructL hf ih =>
    intro _ _ _ s
    cases s with
    | constructL s => exact ih s
    | constructArg hv _ _ _ => rw [raises_not_val hf] at hv; contradiction
    | constructV => cases hf
  | constructArg hfv hg hb hr ih =>
    intro _ _ _ s
    cases s with
    | constructL s => exact value_no_step hfv s
    | constructArg _ hg' hb' s =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val hr) (not_val_of_step s)
      exact ih s
    | constructV hvs => have := hvs _ (List.mem_of_getElem? hg); rw [raises_not_val hr] at this; contradiction
  | letC hr ih =>
    intro _ _ _ s
    cases s with
    | letC s => exact ih s
    | letV hv => rw [raises_not_val hr] at hv; contradiction
  | spreadC _ ih => intro _ _ _ s; cases s with | spreadC s => exact ih s
  | makeArg hg hb hr ih =>
    intro _ _ _ s
    cases s with
    | makeArg hg' hb' s =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val hr) (not_val_of_step s)
      exact ih s
    | makeFields hvs _ => have := hvs _ (List.mem_of_getElem? hg); rw [raises_not_val hr] at this; contradiction
  | readC hr ih =>
    intro _ _ _ s
    cases s with
    | readC s => exact ih s
    | readField => cases hr
    | readProto => cases hr
    | readMissing => cases hr
  | indexC1 hr ih =>
    intro _ _ _ s
    cases s with
    | indexC1 s => exact ih s
    | indexC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | indexField => cases hr
    | indexProto => cases hr
    | indexMissing => cases hr
  | indexC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | indexC1 s => exact value_no_step hv s
    | indexC2 _ s => exact ih s
    | indexField => cases hr
    | indexProto => cases hr
    | indexMissing => cases hr
  | writeC1 hr ih =>
    intro _ _ _ s
    cases s with
    | writeC1 s => exact ih s
    | writeC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | writeField => cases hr
  | writeC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | writeC1 s => exact value_no_step hv s
    | writeC2 _ s => exact ih s
    | writeField hw _ _ => rw [raises_not_val hr] at hw; contradiction
  | testC hr ih =>
    intro _ _ _ s
    cases s with
    | testC s => exact ih s
    | testV hv => rw [raises_not_val hr] at hv; contradiction
  | iteC hr ih =>
    intro _ _ _ s
    cases s with
    | iteC s => exact ih s
    | iteT => cases hr
    | iteF => cases hr
  | arithC1 hr ih =>
    intro _ _ _ s
    cases s with
    | arithC1 s => exact ih s
    | arithC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | arithV hb => have := (binop_values hb).1; rw [raises_not_val hr] at this; contradiction
    | arithThrow ht => have := (binopThrows_values ht).1; rw [raises_not_val hr] at this; contradiction
  | arithC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | arithC1 s => exact value_no_step hv s
    | arithC2 _ s => exact ih s
    | arithV hb => have := (binop_values hb).2.1; rw [raises_not_val hr] at this; contradiction
    | arithThrow ht => have := (binopThrows_values ht).2; rw [raises_not_val hr] at this; contradiction
  | arrArg hg hb hr ih =>
    intro _ _ _ s
    cases s with
    | arrArg hg' hb' s =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val hr) (not_val_of_step s)
      exact ih s
    | arrSpread he hpre _ => exact spread_blocks_raise he hpre hg hb hr
    | arrAlloc hvs => have := hvs _ (List.mem_of_getElem? hg); rw [raises_not_val hr] at this; contradiction
  | elemC1 hr ih =>
    intro _ _ _ s
    cases s with
    | elemC1 s => exact ih s
    | elemC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | elemRead => cases hr
    | elemAbsent => cases hr
    | elemStr => cases hr
  | elemC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | elemC1 s => exact value_no_step hv s
    | elemC2 _ s => exact ih s
    | elemRead => cases hr
    | elemAbsent => cases hr
    | elemStr => cases hr
  | setC1 hr ih =>
    intro _ _ _ s
    cases s with
    | setC1 s => exact ih s
    | setC2 hv _ => rw [raises_not_val hr] at hv; contradiction
    | setC3 hv _ _ => rw [raises_not_val hr] at hv; contradiction
    | setPresent => cases hr
    | setGrow => cases hr
  | setC2 hv hr ih =>
    intro _ _ _ s
    cases s with
    | setC1 s => exact value_no_step hv s
    | setC2 _ s => exact ih s
    | setC3 _ hi _ => rw [raises_not_val hr] at hi; contradiction
    | setPresent => cases hr
    | setGrow => cases hr
  | setC3 hv hi hr ih =>
    intro _ _ _ s
    cases s with
    | setC1 s => exact value_no_step hv s
    | setC2 _ s => exact value_no_step hi s
    | setC3 _ _ s => exact ih s
    | setPresent hw _ _ => rw [raises_not_val hr] at hw; contradiction
    | setGrow hw _ _ => rw [raises_not_val hr] at hw; contradiction
  | lenC hr ih =>
    intro _ _ _ s
    cases s with
    | lenC s => exact ih s
    | lenV => cases hr
    | lenStr => cases hr

/-- **The thrown value is determined.** -/
theorem Raises_det {t v w : Tm} (h1 : Raises t v) (h2 : Raises t w) : v = w := by
  induction h1 generalizing w with
  | throwV hv =>
    cases h2 with
    | throwV => rfl
    | throwC h => rw [raises_not_val h] at hv; contradiction
  | throwC h ih =>
    cases h2 with
    | throwV hv => rw [raises_not_val h] at hv; contradiction
    | throwC h' => exact ih h'
  | callL h ih =>
    cases h2 with
    | callL h' => exact ih h'
    | callRecv hv _ => rw [raises_not_val h] at hv; contradiction
    | callArg hv _ _ _ _ => rw [raises_not_val h] at hv; contradiction
  | callRecv hf h ih =>
    cases h2 with
    | callL h' => rw [raises_not_val h'] at hf; contradiction
    | callRecv _ h' => exact ih h'
    | callArg _ hv _ _ _ => rw [raises_not_val h] at hv; contradiction
  | callArg hf hr hg hb h ih =>
    cases h2 with
    | callL h' => rw [raises_not_val h'] at hf; contradiction
    | callRecv _ h' => rw [raises_not_val h'] at hr; contradiction
    | callArg _ _ hg' hb' h' =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val h) (raises_not_val h')
      exact ih h'
  | constructL h ih =>
    cases h2 with
    | constructL h' => exact ih h'
    | constructArg hv _ _ _ => rw [raises_not_val h] at hv; contradiction
  | constructArg hf hg hb h ih =>
    cases h2 with
    | constructL h' => rw [raises_not_val h'] at hf; contradiction
    | constructArg _ hg' hb' h' =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val h) (raises_not_val h')
      exact ih h'
  | letC h ih => cases h2 with | letC h' => exact ih h'
  | spreadC h ih => cases h2 with | spreadC h' => exact ih h'
  | makeArg hg hb h ih =>
    cases h2 with
    | makeArg hg' hb' h' =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val h) (raises_not_val h')
      exact ih h'
  | readC h ih => cases h2 with | readC h' => exact ih h'
  | indexC1 h ih =>
    cases h2 with
    | indexC1 h' => exact ih h'
    | indexC2 hv _ => rw [raises_not_val h] at hv; contradiction
  | indexC2 hv h ih =>
    cases h2 with
    | indexC1 h' => rw [raises_not_val h'] at hv; contradiction
    | indexC2 _ h' => exact ih h'
  | writeC1 h ih =>
    cases h2 with
    | writeC1 h' => exact ih h'
    | writeC2 hv _ => rw [raises_not_val h] at hv; contradiction
  | writeC2 hv h ih =>
    cases h2 with
    | writeC1 h' => rw [raises_not_val h'] at hv; contradiction
    | writeC2 _ h' => exact ih h'
  | testC h ih => cases h2 with | testC h' => exact ih h'
  | iteC h ih => cases h2 with | iteC h' => exact ih h'
  | arithC1 h ih =>
    cases h2 with
    | arithC1 h' => exact ih h'
    | arithC2 hv _ => rw [raises_not_val h] at hv; contradiction
  | arithC2 hv h ih =>
    cases h2 with
    | arithC1 h' => rw [raises_not_val h'] at hv; contradiction
    | arithC2 _ h' => exact ih h'
  | arrArg hg hb h ih =>
    cases h2 with
    | arrArg hg' hb' h' =>
      obtain ⟨rfl, rfl⟩ := first_nonval_unique hg hg' hb hb' (raises_not_val h) (raises_not_val h')
      exact ih h'
  | elemC1 h ih =>
    cases h2 with
    | elemC1 h' => exact ih h'
    | elemC2 hv _ => rw [raises_not_val h] at hv; contradiction
  | elemC2 hv h ih =>
    cases h2 with
    | elemC1 h' => rw [raises_not_val h'] at hv; contradiction
    | elemC2 _ h' => exact ih h'
  | setC1 h ih =>
    cases h2 with
    | setC1 h' => exact ih h'
    | setC2 hv _ => rw [raises_not_val h] at hv; contradiction
    | setC3 hv _ _ => rw [raises_not_val h] at hv; contradiction
  | setC2 hv h ih =>
    cases h2 with
    | setC1 h' => rw [raises_not_val h'] at hv; contradiction
    | setC2 _ h' => exact ih h'
    | setC3 _ hi _ => rw [raises_not_val h] at hi; contradiction
  | setC3 hv hi h ih =>
    cases h2 with
    | setC1 h' => rw [raises_not_val h'] at hv; contradiction
    | setC2 _ h' => rw [raises_not_val h'] at hi; contradiction
    | setC3 _ _ h' => exact ih h'
  | lenC h ih => cases h2 with | lenC h' => exact ih h'

theorem Raises.makeC {c : CallCode} {a v : Tm} (h : Raises a v) : Raises (.make c a) v :=
  .makeArg (i := 0) rfl (by intro j hj; omega) h

theorem Raises.appR {f a v : Tm} (hf : isVal f = true) (h : Raises a v) : Raises (.app f a) v :=
  .callArg (i := 0) hf rfl rfl (by intro j hj; omega) h

theorem Raises.appL {f a v : Tm} (h : Raises f v) : Raises (.app f a) v := .callL h

#print axioms raises_no_step
#print axioms Raises_det

theorem make_step_inv {c : CallCode} {v : Val} (hv : isVal v = true) {h h' t}
    (hs : Step h (.make c v) h' t) : h' = h ++ [v] ∧ t = .obj h.length c := by
  cases hs with
  | makeArg hg _ hs =>
    obtain ⟨rfl, rfl⟩ := singleton_get hg
    exact False.elim (value_no_step hv hs)
  | makeFields => exact ⟨rfl, rfl⟩

theorem beta_inv {b a : Tm} {fs : List (PropKey × Nat)} (ha : isVal a = true) {h h' t}
    (hs : Step h (.app (.objAt fs (.closure 1 b)) a) h' t) :
    h' = h ∧ t = subst 0 .undef (subst 1 a b) := by
  cases hs with
  | callL hs => cases hs
  | callRecv _ hs => cases hs
  | callArg _ _ hg _ hs =>
    obtain ⟨rfl, rfl⟩ := singleton_get hg
    exact False.elim (value_no_step ha hs)
  | callV => exact ⟨rfl, rfl⟩
  | callSpread _ _ he _ _ => exact False.elim (spread_not_values he (by simp [ha]))

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
  | readProto hm => simp at hm
  | readMissing hm => simp at hm


end Model
end Verification
