import Verification.ExperimentState.FunctionClaims

/-! Stateful source syntax and raw claims. Types remain JSON until consumed, so
unsupported unused claims do not become invented types. Cell annotations and
claims use the same bounded contract decoder. -/
namespace Verification.ExperimentState.SourceInput
open Lean ProgramTyping PositiveRules

/-- Decode every union arm with its existing strict contract decoder. An
unsupported arm rejects the whole type; no projection or widening is allowed.
Record fields and arrow inputs/results retain their bounded primitive decoders. -/
def translate (j : Json) : Except String (Ty Nat) := do
  CellClaims.fieldsExactly j ["top","atoms"]
  if ← (← jField j "top").getBool? then throw "top is outside the source slice"
  let atoms ← jArr j "atoms"
  let arms ← atoms.mapM fun atom => do
    let single := Json.mkObj [("top",toJson false),("atoms",toJson [atom])]
    match ← jStr (← jField atom "a") with
    | "record" =>
      let A ← CellClaims.translate single
      pure [CellClaims.referenceLabel A]
    | "function" => FunctionClaims.translate single
    | _ => SourceTypes.translate (← CellClaims.primitive single)
  return arms.flatten.mergeSort (· ≤ ·) |>.eraseDups

inductive Expr where
  | var (pos : Span) (name : String)
  | lit (pos : Span) (v : Wire.Val)
  | nullTest (pos : Span) (equal testLeft : Bool) (left right : Expr)
  | not (pos : Span) (e : Expr)
  | alloc (pos : Span) (e : Expr)
  | read (pos : Span) (e : Expr)
  | write (pos : Span) (receiver rhs : Expr)
  | lam (pos : Span) (name : String) (arg result : Json) (body : Expr)
  | app (pos : Span) (callee arg : Expr)
  /-- The return statement's entry environment; the expression retains its own span. -/
  | atEnv (pos : Span) (body : Expr)
  /-- Administrative completion and sequencing; neither invents a source expression claim. -/
  | done (pos : Span)
  | seqBody (pos : Span) (init body : Expr)
  /-- Some result denotes a lowered statement conditional with an entry claim;
  none denotes a source ternary whose own expression claim supplies its result. -/
  | ifBody (pos : Span) (result : Option Json) (cond thn els : Expr)
  | letBody (pos : Span) (name : String) (annot : Option Json) (init body : Expr)

def Expr.span : Expr → Span
  | .atEnv _ body | .letBody _ _ _ _ body | .seqBody _ _ body => body.span
  | .ifBody p _ _ _ _ | .done p | .nullTest p _ _ _ _ => p
  | .var p _ | .lit p _ | .not p _ | .alloc p _ | .read p _ | .write p _ _ | .lam p _ _ _ _ | .app p _ _ => p

inductive Stmt where
  | ret (pos : Span) (e : Expr)
  | cst (pos : Span) (name : String) (annot : Option Json) (init : Expr)
  | ite (pos : Span) (cond : Expr) (thn : List Stmt) (els : Option (List Stmt))
  | brk (pos : Span)
  | cont (pos : Span)
  | loop (pos : Span) (cond : Expr) (body : List Stmt)
  | effect (pos : Span) (e : Expr)

structure Param where
  name : String
  ty : Json
structure Fn where
  name : String
  namePos : Span
  params : List Param
  ret : Json
  body : List Stmt
structure Claims where
  name : String
  namePos : Span
  params : List (String × Json)
  ret : Json
  envs : List (Nat × List (String × Json))
  exprs : List (Span × Json)

partial def decodeExpr (j : Json) : Except String Expr := do
  let p ← jSpan j "pos"
  match ← jStr (← jField j "k") with
  | "id" => return .var p (← jStr (← jField j "name"))
  | "lit" => return .lit p (← decodeVal (← jField j "lit"))
  | "bin" =>
    let op ← jStr (← jField j "op")
    if op != "===" && op != "!==" then
      throw s!"unsupported source expression at [{p.1},{p.2}): only strict equality with a null literal is supported"
    let left ← decodeExpr (← jField j "l")
    let right ← decodeExpr (← jField j "r")
    match left, right with
    | _, .lit _ .vnull => return .nullTest p (op == "===") true left right
    | .lit _ .vnull, _ => return .nullTest p (op == "===") false left right
    | _, _ => throw s!"unsupported source expression at [{p.1},{p.2}): equality requires a null literal operand"
  | "not" => return .not p (← decodeExpr (← jField j "e"))
  | "alloc" => return .alloc p (← decodeExpr (← jField j "e"))
  | "read" => return .read p (← decodeExpr (← jField j "e"))
  | "lambda" =>
    return .lam p (← jStr (← jField j "name")) (← jField j "arg")
      (← jField j "result") (← decodeExpr (← jField j "body"))
  | "doneBody" => return .done p
  | "seqBody" => return .seqBody p (← decodeExpr (← jField j "init")) (← decodeExpr (← jField j "body"))
  | "ifBody" =>
    return .ifBody p (some (← jField j "result")) (← decodeExpr (← jField j "cond"))
      (← decodeExpr (← jField j "then")) (← decodeExpr (← jField j "else_"))
  | "conditional" =>
    return .ifBody p none (← decodeExpr (← jField j "cond"))
      (← decodeExpr (← jField j "then")) (← decodeExpr (← jField j "else_"))
  | "letBody" =>
    let annot ← jField j "annot"
    return .letBody p (← jStr (← jField j "name"))
      (if annot == .null then none else some annot)
      (← decodeExpr (← jField j "init")) (← decodeExpr (← jField j "body"))
  | "returnBody" => return .atEnv p (← decodeExpr (← jField j "e"))
  | "apply" => return .app p (← decodeExpr (← jField j "callee")) (← decodeExpr (← jField j "arg"))
  | "write" => return .write p (← decodeExpr (← jField j "receiver")) (← decodeExpr (← jField j "rhs"))
  | _ => throw s!"unsupported source expression at [{p.1},{p.2}): expression outside the stateful source slice"

partial def decodeStmt (j : Json) : Except String Stmt := do
  let p ← jSpan j "pos"
  match ← jStr (← jField j "k") with
  | "return" => return .ret p (← decodeExpr (← jField j "e"))
  | "effect" => return .effect p (← decodeExpr (← jField j "e"))
  | "const" =>
    let a ← jField j "annot"
    return .cst p (← jStr (← jField j "name")) (if a == .null then none else some a)
      (← decodeExpr (← jField j "init"))
  | "break" => return .brk p
  | "continue" => return .cont p
  | "while" => return .loop p (← decodeExpr (← jField j "cond")) (← (← jArr j "body").mapM decodeStmt)
  | "if" =>
    let thn ← (← jArr j "then").mapM decodeStmt
    let els ← match ← jField j "else_" with
      | .null => pure none
      | .arr a => pure (some (← a.toList.mapM decodeStmt))
      | _ => throw "malformed else branch"
    return .ite p (← decodeExpr (← jField j "cond")) thn els
  | _ => throw "statement outside the stateful source slice"

def decodeFn (j : Json) : Except String Fn := do
  return ⟨← jStr (← jField j "name"), ← jSpan j "namePos",
    ← (← jArr j "params").mapM (fun p => do return ⟨← jStr (← jField p "name"), ← jField p "type"⟩),
    ← jField j "retType", ← (← jArr j "body").mapM decodeStmt⟩

def decodeAst (j : Json) : Except String (List Fn) := do
  (← jArr j "functions").mapM decodeFn

def decodeClaims (j : Json) : Except String Claims := do
  let vars := fun j => do
    (← jArr j "vars").mapM fun v => do return (← jStr (← jField v "name"), ← jField v "type")
  return ⟨← jStr (← jField j "name"), ← jSpan j "namePos",
    ← (← jArr j "params").mapM (fun p => do return (← jStr (← jField p "name"), ← jField p "type")),
    ← jField j "retType",
    ← (← jArr j "envs").mapM (fun e => do return ((← jSpan e "pos").1, ← vars e)),
    ← (← jArr j "exprs").mapM (fun e => do return (← jSpan e "pos", ← jField e "type"))⟩

def decodeTypeClaims (j : Json) (fileKey : String) : Except String (List Claims) := do
  for f in (← j.getArr?).toList do
    if (← jStr (← jField f "file")) == fileKey then
      return ← (← jArr f "functions").mapM decodeClaims
  throw "missing claim file"

end Verification.ExperimentState.SourceInput
