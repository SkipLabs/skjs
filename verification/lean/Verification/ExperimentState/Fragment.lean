import Verification.ExperimentState.CellUnion

/-! # The fragment language

The subset of TypeScript this pipeline accepts, as an abstract syntax tree:
functions, statements, expressions and type parameters. The tree is declared on
the producer side in `tools/fragment.mts` and written by `tools/fragment-parse.mts`;
the decoders here read that JSON, so the two files describe one language.

Raw claims travel alongside the tree. Types remain JSON until consumed, so
unsupported unused claims do not become invented types. Cell annotations and
claims use the same bounded contract decoder. -/
namespace Verification.ExperimentState.Fragment
open Lean ProgramTyping PositiveRules

/-- Validate a free required-parameter signature without projecting away object requirements. -/
private def callableShape (a : Json) : Except String (List Json × Json) := do
  CellClaims.fieldsExactly a ["a","params","result","construct","array"]
  if (← jStr (← jField a "a")) != "function" then throw "expected a function atom"
  for key in ["construct","array"] do
    let mode ← jStr (← jField a key)
    if mode != "unknown" && mode != "absent" then throw "unsupported function object mode"
  let args ← jArr a "params"
  return (args, ← jField a "result")

/-- Callable operands may recursively contain callables and primitives.
Every union and overload arm is checked; record operands remain excluded. -/
partial def callableType (j : Json) : SourceTypes.Lowering (Ty Nat) := do
  CellClaims.fieldsExactly j ["top","atoms"]
  if ← (← jField j "top").getBool? then throw "top is outside callable operands"
  let arms ← (← jArr j "atoms").mapM fun atom => do
    if (← jStr (← jField atom "a")) == "function" then
      let signatures ← (← CellClaims.conjuncts atom).mapM fun a => do
        let (args, result) ← callableShape a
        return (← args.mapM callableType, ← callableType result)
      return [← SourceTypes.use (.arrs signatures.eraseDups)]
    else
      let single := Json.mkObj [("top",toJson false),("atoms",toJson [atom])]
      SourceTypes.translate (← CellClaims.primitive single)
  return arms.flatten.mergeSort (· ≤ ·) |>.eraseDups

/-- Required cell fields admit primitives and callables, but not nested records.
Decode both capabilities through the same table before checking invariance. -/
private def cellContract (atom : Json) : SourceTypes.Lowering CellUnion.Contract := do
  let (read, write) ← CellClaims.decodeShape
    (Json.mkObj [("top",toJson false),("atoms",toJson [atom])])
  return ⟨← callableType read, ← callableType write⟩

private def cellConjunction (atom : Json) : SourceTypes.Lowering Nat := do
  let types ← (← CellClaims.conjuncts atom).mapM fun part => do
    let c ← cellContract part
    if c.read != c.write then throw "cell read and write types do not describe the same invariant"
    return c.read
  let first :: rest := (types.mergeSort CellClaims.before).eraseDups
    | throw "an empty conjunction is not a contract"
  SourceTypes.use (.refs first rest)

/-- A callable bag is one value satisfying both contracts, never a union. -/
private def callableObject (atom : Json) : SourceTypes.Lowering Nat := do
  CellClaims.fieldsExactly atom ["a","function","bag"]
  let fn ← jField atom "function"
  let (args,result) ← callableShape fn
  let Ds ← args.mapM callableType
  let R ← callableType result
  let c ← cellContract (← jField atom "bag")
  if c.read != c.write then throw "callable field requires an invariant read/write contract"
  SourceTypes.use (.callable c.write [] [(Ds,R)])

/-- Validate every union arm. Record alternatives may absorb a redundant
read/write contract into an existing invariant alternative (CellUnion.normalize_exact).
Other unsupported arms reject the whole type; no projection is allowed.
Record fields admit bounded primitive/callable contracts.
Arrow operands additionally admit callable contracts. -/
def translate (j : Json) : SourceTypes.Lowering (Ty Nat) := do
  if j == Json.mkObj [("unsupported", toJson true)] then
    throw "type claim unavailable from producer"
  CellClaims.fieldsExactly j ["top","atoms"]
  if ← (← jField j "top").getBool? then throw "top is outside the fragment"
  let atoms ← jArr j "atoms"
  let tagged ← atoms.mapM fun atom => do return (← jStr (← jField atom "a"),atom)
  -- A conjunction is one arm of the union, not a union of its own, so each
  -- contributes a single label. Absorption applies to the plain arms, which is
  -- where two contracts can subsume one another.
  let (conjoined, plain) :=
    ((tagged.filter (fun p => p.1 == "record")).map (·.2)).partition
      (fun a => (a.getObjVal? "and").toOption.isSome)
  let records ← CellUnion.lower (← plain.mapM cellContract)
  let conjunctions ← conjoined.mapM fun a => do return [← cellConjunction a]
  let arms ← (tagged.filter (fun p => p.1 != "record")).mapM fun (_,atom) => do
    let single := Json.mkObj [("top",toJson false),("atoms",toJson [atom])]
    match ← jStr (← jField atom "a") with
    | "callable" => return [← callableObject atom]
    | "function" => callableType single
    -- A number arm is interned, so `1` and `number` are separate labels and
    -- the singleton is below the family by the ordinary clause rules.
    | "number" | "numberlit" =>
      SourceTypes.numberLabels (← CellClaims.primitive single)
    | _ => SourceTypes.translate (← CellClaims.primitive single)
  return (records ++ conjunctions ++ arms).flatten.mergeSort (· ≤ ·) |>.eraseDups

/-- A point assertion separates the persistent reference type from a current
contents predicate. It is never accepted by erasing `current`. Ordinary function
signatures and nested function operands continue to use `translate`. -/
structure PointType where
  type : Ty Nat
  current : Option (Ty Nat) := none

def translatePoint (j : Json) : SourceTypes.Lowering PointType := do
  -- Preserve the existing exact union translation when it succeeds.
  match ← SourceTypes.attempt (translate j) with
  | .ok A => return ⟨A,none⟩
  | .error original =>
    let .ok f := CellClaims.decode j | throw original
    let R ← SourceTypes.translate f.read
    let W ← SourceTypes.translate f.write
    return ⟨[← CellClaims.reference W],some R⟩

inductive Expr where
  | var (pos : Span) (name : String)
  | lit (pos : Span) (v : Claim.Val)
  | logical (pos : Span) (andOp : Bool) (left right : Expr)
  | coalesce (pos : Span) (left right : Expr)
  | shapeTest (pos : Span) (tag : Tag) (equal : Bool) (e : Expr)
  | unitTest (pos : Span) (tag : Tag) (equal testLeft : Bool) (left right : Expr)
  | not (pos : Span) (e : Expr)
  | alloc (pos : Span) (e : Expr)
  | read (pos : Span) (e : Expr)
  | write (pos : Span) (receiver rhs : Expr)
  /-- Assignment to a mutable local, which is an expression: it yields the
  value written, where the calculus's write yields null. -/
  | assign (pos : Span) (name : String) (namePos : Span) (rhs : Expr)
  | withValue (pos : Span) (fn initial : Expr) (functionType bagType : Json)
  | lambda (pos : Span) (params : List (String × Json)) (result : Json) (body : Expr)
  | bindWithReceiver (pos : Span) (callee receiver : Expr) (args : List Expr)
  | callWithReceiver (pos : Span) (callee receiver : Expr) (args : List Expr)
  | call (pos : Span) (callee : Expr) (args : List Expr)
  /-- The return statement's entry environment; the expression retains its own span. -/
  | atEnv (pos : Span) (body : Expr)
  /-- Administrative completion and sequencing; neither invents a source expression claim. -/
  | done (pos : Span)
  | seqBody (pos : Span) (init body : Expr)
  /-- Some result denotes a lowered statement conditional with an entry claim;
  none denotes a source ternary whose own expression claim supplies its result. -/
  | ifBody (pos : Span) (result : Option Json) (cond thn els : Expr)
  | letBody (pos : Span) (name : String) (annot : Option Json) (init body : Expr)

/-- Singleton notation for small source-adapter fixtures. -/
abbrev Expr.lam (p : Span) (name : String) (arg result : Json) (body : Expr) : Expr :=
  .lambda p [(name,arg)] result body
abbrev Expr.app (p : Span) (callee arg : Expr) : Expr := .call p callee [arg]

def Expr.span : Expr → Span
  | .atEnv _ body | .letBody _ _ _ _ body | .seqBody _ _ body => body.span
  | .ifBody p _ _ _ _ | .done p | .unitTest p _ _ _ _ _ | .coalesce p _ _ | .logical p _ _ _ => p
  | .var p _ | .lit p _ | .shapeTest p _ _ _ | .not p _ | .alloc p _ | .read p _ | .write p _ _ | .assign p _ _ _ | .withValue p _ _ _ _ | .lambda p _ _ _ | .call p _ _ | .callWithReceiver p _ _ _ | .bindWithReceiver p _ _ _ => p

inductive Stmt where
  | ret (pos : Span) (e : Expr)
  | cst (pos : Span) (name : String) (annot : Option Json) (init : Expr)
  /-- A mutable local. The annotation is the storage contract every assignment
  is checked against, and is required: what the initializer happens to produce
  is not what the binding may later hold. -/
  | mut (pos : Span) (name : String) (namePos : Span) (annot : Json) (init : Expr)
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
    if op == "&&" || op == "||" then
      return .logical p (op == "&&") (← decodeExpr (← jField j "l")) (← decodeExpr (← jField j "r"))
    if op != "===" && op != "!==" then
      throw s!"unsupported source expression at [{p.1},{p.2}): only strict equality with a null or undefined literal or Boolean &&/|| is supported"
    let left ← decodeExpr (← jField j "l")
    let right ← decodeExpr (← jField j "r")
    match left, right with
    | _, .lit _ .vnull => return .unitTest p .isNul (op == "===") true left right
    | .lit _ .vnull, _ => return .unitTest p .isNul (op == "===") false left right
    | _, .lit _ .vundef => return .unitTest p .isUndef (op == "===") true left right
    | .lit _ .vundef, _ => return .unitTest p .isUndef (op == "===") false left right
    | _, _ => throw s!"unsupported source expression at [{p.1},{p.2}): equality requires a null or undefined literal operand"
  | "functionTest" => do
    CellClaims.fieldsExactly j ["k","pos","equal","e"]
    return .shapeTest p .isFun (← (← jField j "equal").getBool?) (← decodeExpr (← jField j "e"))
  | "coalesce" => return .coalesce p (← decodeExpr (← jField j "left")) (← decodeExpr (← jField j "right"))
  | "not" => return .not p (← decodeExpr (← jField j "e"))
  | "alloc" => return .alloc p (← decodeExpr (← jField j "e"))
  | "read" => return .read p (← decodeExpr (← jField j "e"))
  | "bindWithReceiver" => do
    CellClaims.fieldsExactly j ["k","pos","callee","receiver","args"]
    return .bindWithReceiver p (← decodeExpr (← jField j "callee"))
      (← decodeExpr (← jField j "receiver")) (← (← jArr j "args").mapM decodeExpr)
  | "callWithReceiver" => do
    CellClaims.fieldsExactly j ["k","pos","callee","receiver","args"]
    return .callWithReceiver p (← decodeExpr (← jField j "callee"))
      (← decodeExpr (← jField j "receiver")) (← (← jArr j "args").mapM decodeExpr)
  | "withValue" => do
    CellClaims.fieldsExactly j ["k","pos","fn","initial","functionType","bagType"]
    return .withValue p (← decodeExpr (← jField j "fn")) (← decodeExpr (← jField j "initial"))
      (← jField j "functionType") (← jField j "bagType")
  | "lambda" => do
    CellClaims.fieldsExactly j ["k","pos","params","result","body"]
    let params ← (← jArr j "params").mapM fun param => do
      CellClaims.fieldsExactly param ["name","type"]
      return (← jStr (← jField param "name"), ← jField param "type")
    return .lambda p params (← jField j "result") (← decodeExpr (← jField j "body"))
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
  | "apply" => do
    CellClaims.fieldsExactly j ["k","pos","callee","args"]
    return .call p (← decodeExpr (← jField j "callee"))
      (← (← jArr j "args").mapM decodeExpr)
  | "write" => return .write p (← decodeExpr (← jField j "receiver")) (← decodeExpr (← jField j "rhs"))
  | "assign" => do
    CellClaims.fieldsExactly j ["k","pos","name","namePos","rhs"]
    return .assign p (← jStr (← jField j "name")) (← jSpan j "namePos")
      (← decodeExpr (← jField j "rhs"))
  | _ => throw s!"unsupported source expression at [{p.1},{p.2}): expression outside the stateful fragment"

partial def decodeStmt (j : Json) : Except String Stmt := do
  let p ← jSpan j "pos"
  match ← jStr (← jField j "k") with
  | "return" => return .ret p (← decodeExpr (← jField j "e"))
  | "effect" => return .effect p (← decodeExpr (← jField j "e"))
  | "const" =>
    let a ← jField j "annot"
    return .cst p (← jStr (← jField j "name")) (if a == .null then none else some a)
      (← decodeExpr (← jField j "init"))
  | "let" => do
    CellClaims.fieldsExactly j ["k","pos","name","namePos","annot","init"]
    return .mut p (← jStr (← jField j "name")) (← jSpan j "namePos")
      (← jField j "annot") (← decodeExpr (← jField j "init"))
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
  | _ => throw "statement outside the stateful fragment"

structure TypeParam where
  name : String
  bound : Option Json

def decodeTypeParam (j : Json) : Except String TypeParam := do
  CellClaims.fieldsExactly j ["name", "bound"]
  let name ← jStr (← jField j "name")
  if name.isEmpty then throw "empty type-parameter name"
  let b ← jField j "bound"
  return ⟨name, if b == Json.null then none else some b⟩

def decodeFn (j : Json) : Except String (Fn × List TypeParam) := do
  let typeParams ← (← jArr j "typeParams").mapM decodeTypeParam
  return (⟨← jStr (← jField j "name"), ← jSpan j "namePos",
    ← (← jArr j "params").mapM (fun p => do return ⟨← jStr (← jField p "name"), ← jField p "type"⟩),
    ← jField j "retType", ← (← jArr j "body").mapM decodeStmt⟩, typeParams)

def decodeAstWithParams (j : Json) : Except String (List (Fn × List TypeParam)) := do
  (← jArr j "functions").mapM decodeFn

def decodeAst (j : Json) : Except String (List Fn) := do
  (← decodeAstWithParams j).mapM fun (f, tps) => do
    if !tps.isEmpty then throw "generic functions are checked through source extraction"
    return f

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

end Verification.ExperimentState.Fragment
