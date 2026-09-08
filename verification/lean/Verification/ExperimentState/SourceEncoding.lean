import Lean.Data.Json

/-! Primitive source/claim wire data and JSON helpers. This is an input encoding,
not a second program calculus. The source adapter rejects unsupported primitives;
its exact-translation lemmas relate accepted encodings to the current semantics. -/
namespace Verification

abbrev Span := Nat × Nat
def spanStr (p : Span) : String := s!"[{p.1},{p.2})"

namespace Wire

inductive Val where
  | vnull
  | vundef
  | vnum (bits : UInt64)
  | vstr (s : String)
  | vbool (b : Bool)
  deriving DecidableEq, Repr

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

/-! Primitive wire membership used by exact-translation lemmas. -/

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

end Wire
open Lean Wire

/-- The canonical identity of a numeric literal: the bit pattern of the double
it denotes, with `-0` normalised to `+0`. Numeric wire data remains decodable,
but SourceTypes rejects it; this does not establish numeric program semantics. -/
def numBits (lexeme : String) : Except String UInt64 :=
  match Json.parse lexeme with
  | .ok (.num n) =>
      let f := n.toFloat
      .ok (if f == 0.0 then (0.0 : Float).toBits else f.toBits)
  | _ => .error s!"not a decimal numeric literal: {lexeme}"

/-! ### JSON helpers -/

def jField (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error e => .error s!"missing field '{k}': {e}"

def jStr (j : Json) : Except String String := j.getStr?
def jArr (j : Json) (k : String) : Except String (List Json) := do
  let a ← (← jField j k).getArr?
  return a.toList

def jSpan (j : Json) (k : String) : Except String Span := do
  let a ← (← jField j k).getArr?
  if h : a.size = 2 then
    let s ← a[0].getNat?
    let e ← a[1].getNat?
    return (s, e)
  else .error s!"field '{k}' is not a [start, end] pair"

/-! ### Atoms and types -/

def decodeBoolLiteral (j : Json) : Except String Bool := do
  match ← jStr (← jField j "v") with
  | "true" => return true
  | "false" => return false
  | _ => throw "boolean literal must be exactly true or false"

def decodeAtom (j : Json) : Except String Atom := do
  let a ← jStr (← jField j "a")
  match a with
  | "null" => return .null
  | "undefined" => return .undef
  | "number" => return .num
  | "string" => return .str
  | "boolean" => return .bool
  | "numberlit" => return .numLit (← numBits (← jStr (← jField j "v")))
  | "stringlit" => return .strLit (← jStr (← jField j "v"))
  | "booleanlit" => return .boolLit (← decodeBoolLiteral j)
  | other => .error s!"unknown type atom '{other}'"

/-- The literal forms. An `Expr.lit` node denotes one value, so a "literal"
whose atom is a whole base type (`number`, say) is not a literal at all and is
rejected here rather than being smuggled past the checker. Rejecting it in the
decoder avoids treating a base type as a runtime literal. -/
def decodeVal (j : Json) : Except String Val := do
  let a ← jStr (← jField j "a")
  match a with
  | "null" => return .vnull
  | "undefined" => return .vundef
  | "numberlit" => return .vnum (← numBits (← jStr (← jField j "v")))
  | "stringlit" => return .vstr (← jStr (← jField j "v"))
  | "booleanlit" => return .vbool (← decodeBoolLiteral j)
  | other => .error s!"'{other}' is not a literal value"

/-- A type SKJS could not express in the supported fragment decodes as `none`; the
checker then rejects wherever that type is actually needed. -/
def decodeTyOpt (j : Json) : Except String (Option Ty) := do
  match j.getObjVal? "unsupported" with
  | .ok _ => return none
  | .error _ =>
    let top ← (← jField j "top").getBool?
    let raw ← jArr j "atoms"
    -- These exported types belong to the stateful decoder. Keep them explicitly
    -- unsupported here; the cell and function decoders handle them separately.
    if raw.any (fun a => [some "record", some "function"].contains
        ((a.getObjValAs? String "a").toOption)) then return none
    let atoms ← raw.mapM decodeAtom
    return some { top := top, atoms := atoms }

def decodeTy (j : Json) : Except String Ty := do
  match ← decodeTyOpt j with
  | some t => return t
  | none => .error "a type outside the supported fragment"


end Verification
