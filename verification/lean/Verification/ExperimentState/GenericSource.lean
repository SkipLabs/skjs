import Verification.ExperimentState.Fragment
import Verification.ExperimentState.CellClaims
import Verification.ExperimentState.DirectObligation

/-! Bodies under rigid binders: the one checker for a generic declaration's
body and for a quantified closure's, whatever its nesting.

A body is a variable, a primitive literal, or a closure whose annotation names
the binders in scope; a declaration body is a sequence of immutable copies and
a return. Everything is typed from the source under distinct rigid parameters
and forward upper bounds, along `letE_safeP` and `var_safeP`; `T extends
boolean` is the assumption `T ≤ boolean`, walked by the proved
`GenericBounds.follows`, and never justifies `true ≤ T`. A failed inclusion is
an obligation at its span, never a sentence. Producer claims enter already
decoded to direct types, so no claim representation is re-parsed here. -/
namespace Verification.ExperimentState.GenericSource
open Lean Claim

def paramName (j : Json) : Except String String := do
  CellClaims.fieldsExactly j ["top", "atoms"]
  if ← (← jField j "top").getBool? then throw "expected a type parameter, not unknown"
  let [atom] ← jArr j "atoms" | throw "expected a single type-parameter atom"
  CellClaims.fieldsExactly atom ["a", "name"]
  if (← jStr (← jField atom "a")) != "param" then throw "expected a type-parameter atom"
  let name ← jStr (← jField atom "name")
  if name.isEmpty then throw "empty type-parameter name"
  return name

def booleanType : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "boolean")]])]

def isBooleanType (j : Json) : Bool := j == booleanType

open DirectObligation

/-- Whether a source type annotation names a type parameter anywhere. -/
partial def mentionsParam : Json → Bool
  | .obj kvs =>
      (match kvs.get? "a" with
        | some v => (match v.getStr? with | .ok "param" => true | _ => false)
        | none => false) ||
      kvs.foldl (fun acc _ v => acc || mentionsParam v) false
  | .arr xs => xs.any mentionsParam
  | _ => false

/-- A source annotation as a direct type. A declared binder is rigid; a
function type that mentions a binder is a callable over direct types; every
other annotation is lowered to graph labels by the one translation all
annotations take, so `number` here is the `number` the graph knows. -/
partial def annotationTy (names : List String) (j : Json) :
    SourceTypes.Lowering DirectObligation.Ty := do
  if let .ok name := paramName j then
    if !names.contains name then throw s!"undeclared type parameter '{name}'"
    return .rigid name
  if mentionsParam j then
    let [atom] ← jArr j "atoms"
      | throw "a rigid annotation is a binder, a function type over binders, or a ground type"
    if (← jStr (← jField atom "a")) != "function" then
      throw "a rigid annotation is a binder, a function type over binders, or a ground type"
    let params ← (← jArr atom "params").mapM (annotationTy names)
    return .arrow params (← annotationTy names (← jField atom "result"))
  return .ground (← Fragment.translate j)

/-- Rigid binders in declaration order. A bound is `boolean` or an earlier
binder; duplicate names, forward references and cycles are refused. -/
def parametersOf (typeParams : List Fragment.TypeParam) : Except String (List Parameter) := do
  let mut seen : List Parameter := []
  for tp in typeParams do
    if tp.name == "undefined" then throw "shadowing undefined is outside the fragment"
    if seen.any (·.name == tp.name) then throw "duplicate type parameter"
    let outside := "only `extends boolean` or an earlier type parameter is in the fragment"
    let upper : Option DirectObligation.Ty ← match tp.bound with
      | none => pure none
      | some bound =>
        if isBooleanType bound then
          pure (some (DirectObligation.Ty.ground [1, 2]))
        else
          match paramName bound with
          | .ok u =>
            if seen.any (·.name == u) then pure (some (DirectObligation.Ty.rigid u))
            else throw outside
          | .error _ => throw outside
    seen := seen ++ [⟨tp.name, .quantified, upper⟩]
  return seen

/-- What a producer claims, already as direct types. The sidecar and the SKJS
export each decode to this once; nothing here re-parses a claim. -/
structure Claims where
  name : String
  namePos : Span
  params : List (String × DirectObligation.Ty)
  ret : DirectObligation.Ty
  entries : List (Nat × List (String × DirectObligation.Ty))
  exprs : List (Span × DirectObligation.Ty)

/-- Checking runs over the type table, because a ground annotation met on the
way may need a row the table does not have yet. -/
abbrev M := StateT SourceTypes.Table (Except Failure)

private def lower (pos : Span) (role : SourceRole) (x : SourceTypes.Lowering α) : M α := do
  match x.run (← get) with
  | .ok (a, T) => set T; pure a
  | .error e => throw (.refusal pos role e)

private def refuse (pos : Span) (role : SourceRole) (x : Except String α) : M α :=
  match x with
  | .ok a => pure a
  | .error e => throw (.refusal pos role e)

/-- What a body is checked against: the binders in scope, the claims, and which
names are cells, so that only a cell may be assigned. -/
structure Ctx where
  parameters : List Parameter
  claims : Claims
  cells : List String

private def requireLe (c : Ctx) (env : List (String × DirectObligation.Ty))
    (role : SourceRole) (subject : Subject) (actual expected : DirectObligation.Ty) : M Unit := do
  unless actual.leUnder c.parameters expected do
    throw (.obligation ⟨subject.pos, role,
      .subtyping c.parameters (env.map fun (name, type) => ⟨name, type⟩) subject actual expected⟩)

mutual

/-- An expression's type, read from the source and never from its claim:
trusting a claimed type is exactly what would let a body that happens to fit
every observed instantiation pass as universally valid. A write into a cell
is an obligation on the value against the cell's fixed contract; no
instantiation retypes the cell. -/
partial def exprTy (c : Ctx) (env : List (String × DirectObligation.Ty)) :
    Fragment.Expr → M DirectObligation.Ty
  | .var pos name => match env.lookup name with
      | some t => pure t
      | none => throw (.refusal pos .genericValidation s!"body refers to unbound variable '{name}'")
  | .lit _ .vnull => pure (.ground [0])
  | .lit _ (.vbool true) => pure (.ground [1])
  | .lit _ (.vbool false) => pure (.ground [2])
  | .lit _ .vundef => pure (.ground [3])
  | .assign pos name _ rhs => do
      if !c.cells.contains name then
        throw (.refusal pos .storageWrite s!"assignment to '{name}', which is not a cell")
      let some contract := env.lookup name
        | throw (.refusal pos .storageWrite s!"assignment to unbound '{name}'")
      let actual ← exprTy c env rhs
      requireLe c env .storageWrite (.expression pos) actual contract
      return actual
  | .call pos callee args => do
      -- A call to a callable the body knows over rigid types, such as a
      -- callback parameter `(arg: T) => number`: each argument is an
      -- obligation against that parameter, and the result is the callable's.
      let .var cpos name := callee
        | throw (.refusal pos .callArgument "a call in a rigid body names a callable binding")
      let some (.arrow ps r) := env.lookup name
        | throw (.refusal cpos .callArgument s!"'{name}' is not a callable over rigid types")
      if ps.length != args.length then
        throw (.refusal pos .callArgument "call arity differs from the callable's parameters")
      for (p, a) in ps.zip args do
        let actual ← exprTy c env a
        requireLe c env .callArgument (.expression a.span) actual p
      return r
  | .lambda pos tps ps ret body => do
      if !tps.isEmpty then
        throw (.refusal pos .schemeIntroduction "a nested quantified closure is outside the checked fragment")
      -- The compiled graph takes a nested closure's types from its claim, so
      -- the claim must be exactly the source annotation.
      let names := c.parameters.map (·.name)
      let source ← lower pos .schemeIntroduction (do
        let ps ← ps.mapM fun (q : String × Json) => annotationTy names q.2
        pure (DirectObligation.Ty.arrow ps (← annotationTy names ret)))
      let some claim := c.claims.exprs.lookup pos
        | throw (.refusal pos .schemeIntroduction "nested closure has no claim")
      if claim != source then
        throw (.refusal pos .schemeIntroduction "nested closure claim differs from its source annotation")
      closureTy c env pos ps ret body
  | e => throw (.refusal e.span .genericValidation
      "body requires a variable, a primitive literal, an assignment, a call or a closure")

/-- A closure's type is its annotation once its body establishes that
annotation under the binders in scope. A quantified closure and every closure
nested in it are checked here alike; failure is an obligation at the body. -/
partial def closureTy (c : Ctx) (env : List (String × DirectObligation.Ty))
    (pos : Span) (ps : List (String × Json)) (ret : Json) (body : Fragment.Expr) :
    M DirectObligation.Ty := do
  let names := c.parameters.map (·.name)
  let inner ← ps.mapM fun q => do return (q.1, ← lower pos .schemeIntroduction (annotationTy names q.2))
  let declared ← lower pos .schemeIntroduction (annotationTy names ret)
  let actual ← exprTy c (inner ++ env) body
  unless actual.leUnder c.parameters declared do
    let context := (inner ++ env).map fun (name, type) => Binding.mk name type
    throw (.obligation ⟨body.span, .schemeIntroduction,
      .schemeIntroduction c.parameters context (.closureBody body.span) actual declared⟩)
  return .arrow (inner.map Prod.snd) declared

end

private def entryClaims (c : Ctx) (env : List (String × DirectObligation.Ty)) (pos : Span) :
    M (List (String × DirectObligation.Ty)) := do
  let some source := c.claims.entries.lookup pos.1
    | throw (.refusal pos .entryClaim "missing statement environment")
  let names := source.map Prod.fst
  if names.eraseDups.length != names.length then throw (.refusal pos .entryClaim "duplicate binding")
  if source.length != env.length || source.any (fun p => !(env.map Prod.fst).contains p.1) then
    throw (.refusal pos .entryClaim "bindings differ from the source scope")
  env.mapM fun (name, actual) => do
    let some expected := source.lookup name
      | throw (.refusal pos .entryClaim s!"missing generic binding '{name}'")
    requireLe c env .entryClaim (.binding name pos) actual expected
    return (name, expected)

private def expressionClaim (c : Ctx) (env : List (String × DirectObligation.Ty))
    (e : Fragment.Expr) : M DirectObligation.Ty := do
  let some expected := c.claims.exprs.lookup e.span
    | throw (.refusal e.span .expressionClaim "missing expression claim")
  let actual ← exprTy c env e
  requireLe c env .expressionClaim (.expression e.span) actual expected
  return expected

private def claimSites : List Fragment.Stmt → List Nat × List Span
  | [] => ([],[])
  | .ret pos e :: rest =>
    let (entries,expressions) := claimSites rest
    (pos.1 :: entries,e.span :: expressions)
  | .constants pos bs :: rest =>
    let (entries,expressions) := claimSites rest
    (pos.1 :: entries,bs.map (·.init.span) ++ expressions)
  | _ :: rest => claimSites rest

/-- A declaration body: immutable copies, each seeing the earlier, then a
return. One entry per statement; each declarator's claim is checked in the
scope the earlier ones extend. -/
private def bodyClaims (c : Ctx) (env : List (String × DirectObligation.Ty))
    (result : DirectObligation.Ty) (origin : Span) : List Fragment.Stmt → M Unit
  | [.ret pos e] => do
    let H ← entryClaims c env pos
    let actual ← expressionClaim c H e
    requireLe c H .returnContract (.returned pos) actual result
  | .constants pos bindings :: rest => do
    let H ← entryClaims c env pos
    let H ← bindings.foldlM (fun H b => do
      let actual ← expressionClaim c H b.init
      -- Inference retains the checked initializer type, never a producer-selected
      -- binding type. A weakened expression claim can lose precision, not regain it.
      let expected ← match b.annot with
        | some annot => lower pos .bindingAnnotation (annotationTy (c.parameters.map (·.name)) annot)
        | none => pure actual
      requireLe c H .bindingAnnotation (.binding b.name pos) actual expected
      return H ++ [(b.name, expected)]) H
    bodyClaims c H result origin rest
  | _ => throw (.refusal origin .genericValidation "generic claim checking requires a checked variable-copy body")

/-- The declared signature and the claimed one must agree exactly; a bound
never identifies its endpoints. -/
def checkScheme (f : Fragment.Fn) (typeParams : List Fragment.TypeParam)
    (claims : Claims) : SourceTypes.Lowering Unit := do
  if f.name != claims.name || f.namePos != claims.namePos then
    throw "function claim identity mismatch"
  if typeParams.isEmpty then throw "generic body requires type parameters"
  let names := (← parametersOf typeParams).map (·.name)
  if f.params.isEmpty then throw "generic body requires a value parameter"
  let sourceNames := f.params.map (·.name)
  if sourceNames.eraseDups.length != sourceNames.length then throw "duplicate source parameter"
  for p in f.params do
    if p.name == "undefined" then throw "shadowing undefined is outside the fragment"
  if f.params.length != claims.params.length then throw "parameter claim count mismatch"
  for (p, c) in f.params.zip claims.params do
    if p.name != c.1 then throw "parameter claim name or order mismatch"
    if (← annotationTy names p.ty) != c.2 then
      throw "claimed generic identity types differ from the source annotation"
  if claims.ret != (← annotationTy names f.ret) then
    throw "claimed generic identity types differ from the source annotation"

/-- Both production and independent consumption reconstruct these obligations.
Every source entry and expression must occur exactly once; no supplied point is
silently ignored. -/
def check (f : Fragment.Fn) (typeParams : List Fragment.TypeParam) (claims : Claims) : M Unit := do
  let parameters ← refuse f.namePos .genericValidation (parametersOf typeParams)
  let names := parameters.map (·.name)
  let c : Ctx := ⟨parameters, claims, []⟩
  let (entries, expressions) := claimSites f.body
  let suppliedEntries := claims.entries.map Prod.fst
  let suppliedExpressions := claims.exprs.map Prod.fst
  if suppliedEntries.eraseDups.length != suppliedEntries.length ||
      suppliedEntries.length != entries.length || suppliedEntries.any (fun p => !entries.contains p) then
    throw (.refusal f.namePos .genericValidation "generic entry claims: missing, duplicate or unmatched statement site")
  if suppliedExpressions.eraseDups.length != suppliedExpressions.length ||
      suppliedExpressions.length != expressions.length || suppliedExpressions.any (fun p => !expressions.contains p) then
    throw (.refusal f.namePos .genericValidation "generic expression claims: missing, duplicate or unmatched expression site")
  let env ← f.params.mapM fun p => do
    return (p.name, ← lower f.namePos .genericValidation (annotationTy names p.ty))
  bodyClaims c env (← lower f.namePos .genericValidation (annotationTy names f.ret)) f.namePos f.body
  -- The remaining source-shape and exact-signature invariants, once the claim
  -- pass has exposed any failed inclusion.
  lower f.namePos .genericValidation (checkScheme f typeParams claims)

private def paramT : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "param"), ("name", toJson "T")]])]
private def T : DirectObligation.Ty := .rigid "T"
private def bool : DirectObligation.Ty := .ground [1, 2]
private def tpT : Fragment.TypeParam := ⟨"T", none⟩
private def tpTbool : Fragment.TypeParam := ⟨"T", some booleanType⟩

private def idFn : Fragment.Fn :=
  ⟨"id", (0, 2), [⟨"x", paramT⟩], paramT, [.ret (10, 18) (.var (17, 18) "x")]⟩
private def idClaims : Claims :=
  ⟨"id", (0, 2), [("x", T)], T, [(10, [("x", T)])], [((17, 18), T)]⟩
private def asBoolFn : Fragment.Fn :=
  ⟨"asBoolean", (0, 2), [⟨"x", paramT⟩], booleanType, [.ret (10, 18) (.var (17, 18) "x")]⟩
private def asBoolClaims : Claims :=
  ⟨"asBoolean", (0, 2), [("x", T)], bool, [(10, [("x", T)])], [((17, 18), T)]⟩

private def run (x : M α) : Except Failure α := x.run' SourceTypes.initial
private def ok (x : Except ε α) : Bool := match x with | .ok _ => true | .error _ => false
private def failsAt (role : SourceRole) (x : Except Failure α) : Bool :=
  match x with | .error (.obligation l) => l.role == role | _ => false
private def refusedWith (text : String) (x : Except Failure α) : Bool :=
  match x with | .error (.refusal _ _ e) => text.isPrefixOf e | _ => false

#guard ok ((checkScheme idFn [tpT] idClaims).run' SourceTypes.initial)
#guard ok (run (check idFn [tpT] idClaims))
-- A body that is not copies-then-return is refused as such, once its (absent)
-- claim sites agree with the source.
#guard refusedWith "generic claim checking requires"
  (run (check {idFn with body := [.effect (10, 18) (.var (17, 18) "x")]} [tpT]
    {idClaims with entries := [], exprs := []}))
#guard (match (checkScheme idFn [tpT, tpT] idClaims).run' SourceTypes.initial with
  | .error e => "duplicate type parameter".isPrefixOf e
  | _ => false)
-- `T extends boolean` transports `T` to `boolean`; an unbounded `T` does not.
#guard ok (run (check asBoolFn [tpTbool] asBoolClaims))
#guard failsAt .returnContract (run (check asBoolFn [tpT] asBoolClaims))
-- An upper bound never justifies `true ≤ T`.
#guard failsAt .returnContract (run (check
  {idFn with body := [.ret (10, 18) (.lit (17, 18) (.vbool true))]}
  [tpTbool] {idClaims with exprs := [((17, 18), .ground [1])]}))

private def bindFn : Fragment.Fn :=
  ⟨"bind", (0, 2), [⟨"x", paramT⟩], paramT,
    [.cst (2, 3) "y" (some paramT) (.var (4, 5) "x"),
     .ret (6, 7) (.var (8, 9) "y")]⟩
private def bindClaims : Claims :=
  ⟨"bind", (0, 2), [("x", T)], T,
   [(2, [("x", T)]), (6, [("x", T), ("y", T)])], [((4, 5), T), ((8, 9), T)]⟩
private def fstFn : Fragment.Fn :=
  ⟨"fst", (0, 2), [⟨"x", paramT⟩, ⟨"y", paramT⟩], paramT,
    [.ret (10, 18) (.var (17, 18) "x")]⟩
private def fstClaims : Claims :=
  ⟨"fst", (0, 2), [("x", T), ("y", T)], T, [(10, [("x", T), ("y", T)])], [((17, 18), T)]⟩

#guard ok (run (check bindFn [tpT] bindClaims))
#guard ok (run (check fstFn [tpT] fstClaims))
-- A copy may be returned through either name, and an unannotated copy keeps
-- the checked initializer type.
#guard ok (run (check {bindFn with body :=
    [.cst (2, 3) "y" (some paramT) (.var (4, 5) "x"), .ret (6, 7) (.var (8, 9) "x")]}
  [tpT] bindClaims))
#guard ok (run (check {bindFn with body :=
    [.cst (2, 3) "y" none (.var (4, 5) "x"), .ret (6, 7) (.var (8, 9) "y")]}
  [tpT] bindClaims))

end Verification.ExperimentState.GenericSource
