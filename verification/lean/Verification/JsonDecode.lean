/- JSON decoding for the TypeScript source AST and SKJS type claims. -/
import Lean.Data.Json
import Verification.SkjsTypeClaims

namespace Verification

open Lean
open Core hiding Fn

/-- The canonical identity of a numeric literal: the bit pattern of the double
it denotes, with `-0` normalised to `+0`. Two spellings of one double give one
value, which is what makes a spurious `never` between them detectable. -/
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
decoder is what makes erasure into the calculus total. -/
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
    let atoms ← (← jArr j "atoms").mapM decodeAtom
    return some { top := top, atoms := atoms }

def decodeTy (j : Json) : Except String Ty := do
  match ← decodeTyOpt j with
  | some t => return t
  | none => .error "a type outside the supported fragment"

/-! ### Abstract syntax -/

def decodeBinOp (s : String) : Except String BinOp :=
  match s with
  | "===" => .ok .eq
  | "!==" => .ok .ne
  | "&&" => .ok .and
  | "||" => .ok .or
  | other => .error s!"operator `{other}` is not in the supported fragment"

partial def decodeExpr (j : Json) : Except String Expr := do
  let pos ← jSpan j "pos"
  let k ← jStr (← jField j "k")
  match k with
  | "id" => return .var pos (← jStr (← jField j "name"))
  | "lit" => return .lit pos (← decodeVal (← jField j "lit"))
  | "bin" =>
      return .bin pos (← decodeBinOp (← jStr (← jField j "op")))
        (← decodeExpr (← jField j "l")) (← decodeExpr (← jField j "r"))
  | "not" => return .neg pos (← decodeExpr (← jField j "e"))
  | "typeof" => return .tyof pos (← decodeExpr (← jField j "e"))
  | "call" =>
      let args ← (← jArr j "args").mapM decodeExpr
      return .call pos (← jStr (← jField j "callee")) args
  | other => .error s!"unknown expression node '{other}'"

partial def decodeStmt (j : Json) : Except String Stmt := do
  let pos ← jSpan j "pos"
  let k ← jStr (← jField j "k")
  match k with
  | "return" => return .ret pos (← decodeExpr (← jField j "e"))
  | "const" =>
      let annot ← match ← jField j "annot" with
        | .null => pure none
        | a => pure (some (← decodeTy a))
      return .cst pos (← jStr (← jField j "name")) annot (← decodeExpr (← jField j "init"))
  | "if" =>
      let thn ← (← jArr j "then").mapM decodeStmt
      let els ← match ← jField j "else_" with
        | .null => pure none
        | .arr a => pure (some (← a.toList.mapM decodeStmt))
        | _ => .error "malformed else branch"
      return .ite pos (← decodeExpr (← jField j "cond")) thn els
  | other => .error s!"unknown statement node '{other}'"

def decodeFn (j : Json) : Except String Fn := do
  let params ← (← jArr j "params").mapM fun p => do
    return ({ name := ← jStr (← jField p "name"), ty := ← decodeTy (← jField p "type") } : Param)
  return {
    name := ← jStr (← jField j "name")
    namePos := ← jSpan j "namePos"
    params := params
    ret := ← decodeTy (← jField j "retType")
    body := ← (← jArr j "body").mapM decodeStmt
  }

def decodeAst (j : Json) : Except String (List Fn) := do
  (← jArr j "functions").mapM decodeFn

/-! ### Claims -/

def decodeVars (j : Json) : Except String (List (String × Option Ty)) := do
  (← jArr j "vars").mapM fun v => do
    return (← jStr (← jField v "name"), ← decodeTyOpt (← jField v "type"))

def decodeFunTypeClaims (j : Json) : Except String FunTypeClaims := do
  let params ← (← jArr j "params").mapM fun p => do
    return (← jStr (← jField p "name"), ← decodeTyOpt (← jField p "type"))
  let envs ← (← jArr j "envs").mapM fun e => do
    return ((← jSpan e "pos").1, ← decodeVars e)
  let exprs ← (← jArr j "exprs").mapM fun x => do
    return (← jSpan x "pos", ← decodeTyOpt (← jField x "type"))
  return {
    name := ← jStr (← jField j "name")
    namePos := ← jSpan j "namePos"
    params := params
    ret := ← decodeTyOpt (← jField j "retType")
    envs := envs
    exprs := exprs
  }

/-- Claims are emitted for every file SKJS checked; pick the ones for
the file under test, by the exact key SKJS was given. -/
def decodeTypeClaims (j : Json) (fileKey : String) : Except String (List FunTypeClaims) := do
  let files ← j.getArr?
  for f in files do
    if (← jStr (← jField f "file")) == fileKey then
      return ← (← jArr f "functions").mapM decodeFunTypeClaims
  .error s!"the claims contain no entry for '{fileKey}'"

end Verification
