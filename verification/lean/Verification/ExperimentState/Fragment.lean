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
      -- The callable table grows as this walks it, so a numeric parameter or
      -- result is interned rather than refused for being outside the four
      -- fixed labels.
      SourceTypes.translateArm (← CellClaims.primitive single)
  return arms.flatten.mergeSort (· ≤ ·) |>.eraseDups

/-- Required record fields admit primitives and callables, but not nested
records. Decode both capabilities through the same table before checking
invariance, field by field. -/
private def cellContract (atom : Json) : SourceTypes.Lowering CellUnion.Contract := do
  let fields ← CellClaims.decodeShapes
    (Json.mkObj [("top",toJson false),("atoms",toJson [atom])])
  fields.mapM fun (name, read, write) => do
    return ⟨name, ← callableType read, ← callableType write⟩

private def cellConjunction (atom : Json) : SourceTypes.Lowering Nat := do
  let types ← (← CellClaims.conjuncts atom).mapM fun part => do
    let c ← cellContract part
    if !CellUnion.invariant c then
      throw "cell read and write types do not describe the same invariant"
    return c.map fun f => (f.name, f.read)
  let first :: rest := (types.mergeSort CellClaims.beforeFields).eraseDups
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
  if !CellUnion.invariant c then
    throw "callable field requires an invariant read/write contract"
  SourceTypes.use (.callable (c.map fun f => (f.name, f.write)) [] [(Ds,R)])

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
    -- A number or string arm is interned, so `1` and `number` are separate
    -- labels and the singleton is below the family by the ordinary clause rules.
    | "number" | "numberlit" | "string" | "stringlit" =>
      SourceTypes.numberLabels (← CellClaims.primitive single)
    | _ => SourceTypes.translate (← CellClaims.primitive single)
  return (records ++ conjunctions ++ arms).flatten.mergeSort (· ≤ ·) |>.eraseDups

/-- A point assertion separates the persistent reference type from a current
contents predicate. It is never accepted by erasing `current`. Ordinary function
signatures and nested function operands continue to use `translate`. -/
structure PointType where
  type : Ty Nat
  /-- What the point's record currently holds, field by field, for the fields
  whose read and write contracts differ. A point naming no record has none. -/
  current : Option (List (String × Ty Nat)) := none

def translatePoint (j : Json) : SourceTypes.Lowering PointType := do
  -- Preserve the existing exact union translation when it succeeds.
  match ← SourceTypes.attempt (translate j) with
  | .ok A => return ⟨A,none⟩
  | .error original =>
    -- The persistent contract is what a field may be written; what it holds
    -- now is the read side, stated separately and field by field. Numbers are
    -- interned on both sides, so a numeric field can carry an assertion.
    let .ok fs := CellClaims.decode j | throw original
    let write ← fs.mapM fun f => do return (f.name, ← SourceTypes.translateArm f.write)
    let read ← fs.mapM fun f => do return (f.name, ← SourceTypes.translateArm f.read)
    let current := (read.zip write).filterMap fun (r,w) => if r.2 == w.2 then none else some r
    if current.isEmpty then throw original
    return ⟨[← CellClaims.reference write],some current⟩

inductive Expr where
  | var (pos : Span) (name : String)
  | lit (pos : Span) (v : Claim.Val)
  | logical (pos : Span) (andOp : Bool) (left right : Expr)
  | coalesce (pos : Span) (left right : Expr)
  | shapeTest (pos : Span) (tag : Tag) (equal : Bool) (e : Expr)
  /-- Strict equality awaiting a checked singleton operand from source claims. -/
  | equality (pos : Span) (equal : Bool) (left right : Expr)
  | singletonTest (pos : Span) (tag : Tag) (equal testLeft : Bool) (left right : Expr)
  | not (pos : Span) (e : Expr)
  /-- `e as T`, `e satisfies T` or `e!`: the operand's value. An annotation is
  an obligation the operand must meet, never a fact about it. -/
  | cast (pos : Span) (annot : Option Json) (e : Expr)
  /-- An object literal: one named field per initializer, in source order. -/
  | alloc (pos : Span) (names : List String) (es : List Expr)
  | read (pos : Span) (field : String) (e : Expr)
  | write (pos : Span) (field : String) (receiver rhs : Expr)
  /-- `e[key]`: the receiver, then the key, then the read of the field the
  key's claimed type names. The decoder leaves the field unresolved; the
  extractor fills it from the key's claim, a string singleton, and the key's
  expression obligation must establish it. -/
  | index (pos : Span) (field : Option String) (e key : Expr)
  | indexWrite (pos : Span) (field : Option String) (receiver key rhs : Expr)
  /-- Read a local once; assign and return the RHS only when nullish. -/
  | nullishAssign (pos : Span) (name : String) (namePos : Span) (rhs : Expr)
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
  | .ifBody p _ _ _ _ | .done p | .equality p _ _ _ | .singletonTest p _ _ _ _ _ | .coalesce p _ _ | .logical p _ _ _ => p
  | .index p _ _ _ | .indexWrite p _ _ _ _ => p
  | .var p _ | .lit p _ | .shapeTest p _ _ _ | .not p _ | .cast p _ _ | .alloc p _ _ | .read p _ _ | .write p _ _ _ | .assign p _ _ _ | .nullishAssign p _ _ _ | .withValue p _ _ _ _ | .lambda p _ _ _ | .call p _ _ | .callWithReceiver p _ _ _ | .bindWithReceiver p _ _ _ => p

/-- One declarator of a `const` or `let`. -/
structure Binding where
  name : String
  namePos : Span
  annot : Option Json
  init : Expr

/-- One property of an object pattern: `field: name = default_`. -/
structure PatternProp where
  field : String
  name : String
  namePos : Span
  default_ : Option Expr

inductive Stmt where
  | ret (pos : Span) (e : Expr)
  /-- Immutable bindings, left to right, each initializer seeing the earlier
  ones. The statement is the entry; no cut separates its declarators. -/
  | constants (pos : Span) (bindings : List Binding)
  /-- Mutable locals, one private cell each. A binding's annotation is the
  storage contract every assignment is checked against; absent, the producer
  supplies one. What the initializer happens to produce is not what the
  binding may later hold. -/
  | mutables (pos : Span) (bindings : List Binding)
  /-- An object pattern on a `const`: the initializer once, then each property
  read in order, a default evaluated only when its read is undefined. -/
  | pattern (pos : Span) (props : List PatternProp) (init : Expr)
  | ite (pos : Span) (cond : Expr) (thn : List Stmt) (els : Option (List Stmt))
  | brk (pos : Span)
  | cont (pos : Span)
  | loop (pos : Span) (cond : Expr) (body : List Stmt)
  | effect (pos : Span) (e : Expr)

/-- Singleton notation for small source-adapter fixtures. -/
abbrev Stmt.cst (p : Span) (name : String) (annot : Option Json) (init : Expr) : Stmt :=
  .constants p [⟨name, p, annot, init⟩]
abbrev Stmt.mut (p : Span) (name : String) (namePos : Span) (annot : Option Json) (init : Expr) : Stmt :=
  .mutables p [⟨name, namePos, annot, init⟩]

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
    | _, .lit _ .vnull => return .singletonTest p .isNul (op == "===") true left right
    | .lit _ .vnull, _ => return .singletonTest p .isNul (op == "===") false left right
    | _, .lit _ .vundef => return .singletonTest p .isUndef (op == "===") true left right
    | .lit _ .vundef, _ => return .singletonTest p .isUndef (op == "===") false left right
    | _, _ => return .equality p (op == "===") left right
  | "functionTest" => do
    CellClaims.fieldsExactly j ["k","pos","equal","e"]
    return .shapeTest p .isFun (← (← jField j "equal").getBool?) (← decodeExpr (← jField j "e"))
  | "coalesce" => return .coalesce p (← decodeExpr (← jField j "left")) (← decodeExpr (← jField j "right"))
  | "not" => return .not p (← decodeExpr (← jField j "e"))
  | "cast" =>
    CellClaims.fieldsExactly j ["k","pos","cast","annot","e"]
    let kind ← jStr (← jField j "cast")
    if kind != "as" && kind != "satisfies" && kind != "nonNull" then throw "unknown cast kind"
    let a ← jField j "annot"
    if (kind == "nonNull") != (a == .null) then throw "a cast's annotation does not match its kind"
    return .cast p (if a == .null then none else some a) (← decodeExpr (← jField j "e"))
  | "alloc" =>
    let fields ← jArr j "fields"
    let parts ← fields.mapM fun f => do
      return (← jStr (← jField f "name"), ← decodeExpr (← jField f "e"))
    return .alloc p (parts.map Prod.fst) (parts.map Prod.snd)
  | "read" => return .read p (← jStr (← jField j "field")) (← decodeExpr (← jField j "e"))
  | "index" => do
    CellClaims.fieldsExactly j ["k","pos","e","key"]
    return .index p none (← decodeExpr (← jField j "e")) (← decodeExpr (← jField j "key"))
  | "indexWrite" => do
    CellClaims.fieldsExactly j ["k","pos","receiver","key","rhs"]
    return .indexWrite p none (← decodeExpr (← jField j "receiver")) (← decodeExpr (← jField j "key"))
      (← decodeExpr (← jField j "rhs"))
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
  | "write" =>
    return .write p (← jStr (← jField j "field")) (← decodeExpr (← jField j "receiver"))
      (← decodeExpr (← jField j "rhs"))
  | "nullishAssign" => do
    CellClaims.fieldsExactly j ["k","pos","name","namePos","rhs"]
    return .nullishAssign p (← jStr (← jField j "name")) (← jSpan j "namePos")
      (← decodeExpr (← jField j "rhs"))
  | "assign" => do
    CellClaims.fieldsExactly j ["k","pos","name","namePos","rhs"]
    return .assign p (← jStr (← jField j "name")) (← jSpan j "namePos")
      (← decodeExpr (← jField j "rhs"))
  | _ => throw s!"unsupported source expression at [{p.1},{p.2}): expression outside the stateful fragment"

/-- The declarators of a `const` or `let`: at least one, in source order. -/
partial def decodeBindings (j : Json) : Except String (List Binding) := do
  CellClaims.fieldsExactly j ["k","pos","bindings"]
  let bindings ← (← jArr j "bindings").mapM fun b => do
    CellClaims.fieldsExactly b ["name","namePos","annot","init"]
    let a ← jField b "annot"
    return (⟨← jStr (← jField b "name"), ← jSpan b "namePos",
      if a == .null then none else some a, ← decodeExpr (← jField b "init")⟩ : Binding)
  if bindings.isEmpty then throw "a declaration needs a binding"
  return bindings

partial def decodeStmt (j : Json) : Except String Stmt := do
  let p ← jSpan j "pos"
  match ← jStr (← jField j "k") with
  | "return" => return .ret p (← decodeExpr (← jField j "e"))
  | "effect" => return .effect p (← decodeExpr (← jField j "e"))
  | "const" => return .constants p (← decodeBindings j)
  | "let" => return .mutables p (← decodeBindings j)
  | "pattern" =>
    CellClaims.fieldsExactly j ["k","pos","props","init"]
    let props ← (← jArr j "props").mapM fun q => do
      CellClaims.fieldsExactly q ["field","name","namePos","default_"]
      let d ← jField q "default_"
      let dflt ← if d == .null then pure none else some <$> decodeExpr d
      return (⟨← jStr (← jField q "field"), ← jStr (← jField q "name"), ← jSpan q "namePos", dflt⟩ : PatternProp)
    if props.isEmpty then throw "an empty pattern binds nothing"
    return .pattern p props (← decodeExpr (← jField j "init"))
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
