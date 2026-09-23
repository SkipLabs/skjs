import Verification.Model.Source.Fragment
import Verification.Model.Programs.CellClaims
import Verification.Model.Types.GenericCertificate

/-! Bodies under rigid binders: the one checker for a generic declaration's
body and for a quantified closure's, whatever its nesting.

A body is a variable, a primitive literal, or a closure whose annotation names
the binders in scope; a declaration body is a sequence of immutable copies and
a return. Everything is typed from the source under distinct rigid parameters
and forward upper bounds, along `letE_safeP` and `var_safeP`; `T extends
boolean` is the assumption `T ≤ boolean`, and an imported graph bound such as
`T extends Json` is the assumption `T ≤ Json`. Both are walked by the direct relation whose
accepted comparisons imply semantic inclusion, and never justifies `true ≤ T`.
A failed inclusion is an obligation at its span, never a sentence. Producer claims enter already
decoded to direct types, so no claim representation is re-parsed here. Accepted
variable-copy declarations also produce a `GenericCertificate`; its independent
checker reconstructs a calculus term and proves the result for every admissible
rigid assignment satisfying the bounds. -/
namespace Verification.Model.GenericSource
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

mutual
/-- A source annotation as a direct type. A declared binder is rigid; a
function type that mentions a binder is a callable over direct types; every
other annotation is lowered to graph labels by the one translation all
annotations take, so `number` here is the `number` the graph knows. -/
partial def annotationTy (names : List String) (j : Json) :
    SourceTypes.Lowering DirectObligation.Ty := do
  -- `unknown` is top, which every value inhabits, including the `undefined`
  -- a plain call passes as its receiver.
  if (j.getObjVal? "top").toOption == some (toJson true) then return .top
  if let .ok name := paramName j then
    if !names.contains name then throw s!"undeclared type parameter '{name}'"
    return .rigid name
  if mentionsParam j then
    if let some element := Fragment.arrayElement j then
      return .array (← annotationTy names element)
    let [atom] ← jArr j "atoms"
      | throw "a rigid annotation is a binder, a function type over binders, or a ground type"
    if (← jStr (← jField atom "a")) != "function" then
      throw "a rigid annotation is a binder, a function type over binders, or a ground type"
    let receiver ← receiverTy names (← jField atom "this")
    let params ← (← jArr atom "params").mapM (annotationTy names)
    let result ← annotationTy names (← jField atom "result")
    match (atom.getObjVal? "rest").toOption with
    | some e => return .variadic receiver params (← annotationTy names e) result
    | none => return .arrow receiver params result
  return .ground (← Fragment.translate j)

/-- A receiver contract as a direct type, by the one annotation converter. -/
partial def receiverTy (names : List String) (j : Json) :
    SourceTypes.Lowering DirectObligation.Ty :=
  annotationTy names j
end

/-- A ground imported bound names a row installed from the source import
document. Raw source cannot supply this internal atom. -/
def importedBound (T : SourceTypes.Table) (bound : Json) : Except String Nat := do
  CellClaims.fieldsExactly bound ["top", "atoms"]
  if ← (← jField bound "top").getBool? then throw "a bound cannot be unknown"
  let [atom] ← jArr bound "atoms" | throw "expected one imported graph atom"
  CellClaims.fieldsExactly atom ["a", "label"]
  if (← jStr (← jField atom "a")) != "graph" then throw "expected an imported graph atom"
  let label ← (← jField atom "label").getNat?
  if label >= T.length then throw "imported bound graph label is absent"
  return label

/-- A binder's bound: `boolean`, an earlier binder, or a source-derived
imported graph node. -/
def boundOf (T : SourceTypes.Table) (seen : List Parameter) :
    Option Json → Except String (Option DirectObligation.Ty)
  | none => .ok none
  | some bound =>
    if isBooleanType bound then .ok (some (DirectObligation.Ty.ground [1, 2]))
    else match paramName bound with
      | .ok u =>
        if seen.any (·.name == u) then .ok (some (DirectObligation.Ty.rigid u))
        else .error "a type-parameter bound must name an earlier parameter"
      | .error _ => match importedBound T bound with
        | .ok label => .ok (some (.ground [label]))
        | .error _ => .error "only `extends boolean`, an earlier type parameter, or an imported graph type is in the fragment"

/-- Rigid binders in declaration order. A bound is `boolean`, an earlier
binder, or a source-derived imported graph node. Duplicate names, forward
references and cycles are refused.
`SourceJudgments.parametersOf_wellFormed` states what this establishes. -/
def parametersOf (T : SourceTypes.Table) (typeParams : List Fragment.TypeParam) : Except String (List Parameter) :=
  go [] typeParams
where
  go (seen : List Parameter) : List Fragment.TypeParam → Except String (List Parameter)
    | [] => .ok seen
    | tp :: rest =>
      if tp.name == "undefined" then .error "shadowing undefined is outside the fragment"
      else if seen.any (·.name == tp.name) then .error "duplicate type parameter"
      else match boundOf T seen tp.bound with
        | .error e => .error e
        | .ok upper => go (seen ++ [⟨tp.name, .quantified, upper⟩]) rest

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

def requireLeE (c : Ctx) (env : List (String × DirectObligation.Ty))
    (role : SourceRole) (subject : Subject) (actual expected : DirectObligation.Ty) :
    Except Failure Unit :=
  if actual.leUnder c.parameters expected then .ok ()
  else .error (.obligation ⟨subject.pos, role,
    .subtyping c.parameters (env.map fun (name, type) => ⟨name, type⟩) subject actual expected⟩)

private def liftE (x : Except Failure α) : M α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-! ### Bodies with lowered annotations

Lowering is the one translation every annotation takes and the only part of
checking that touches the type table. Everything after it is total and pure:
`SourceJudgments` states the declarative judgment it decides. -/

/-- A body whose annotations are already direct types. -/
inductive Body where
  | var (pos : Span) (name : String)
  | lit (pos : Span) (v : Claim.Val)
  | assign (pos : Span) (name : String) (rhs : Body)
  | call (pos : Span) (callee : Body) (args : List Body)
  | lambda (pos : Span) (params : List (String × DirectObligation.Ty))
      (result : DirectObligation.Ty) (body : Body)
  deriving Repr, Inhabited

def Body.span : Body → Span
  | .var pos _ | .lit pos _ | .assign pos _ _ | .call pos _ _ | .lambda pos _ _ _ => pos

/-- Lower a source expression's annotations. Forms the checker does not type
are refused here, by name, at their span. -/
def translate (names : List String) : Fragment.Expr → M Body
  | .var pos name => pure (.var pos name)
  | .lit pos v => pure (.lit pos v)
  -- A block body `{ return e; }` is its returned expression; the statement
  -- entry around it is a claim site of the stateful lowering, not a value.
  | .atEnv _ e => translate names e
  | .assign pos name _ rhs => do return .assign pos name (← translate names rhs)
  | .call pos callee args spreads => do
      if !spreads.isEmpty then
        throw (.refusal pos .schemeIntroduction "a spread argument is outside the rigid checker")
      let callee ← translate names callee
      let args ← args.attach.mapM fun ⟨a, _⟩ => translate names a
      return .call pos callee args
  | .lambda pos receiver tps ps defaults rest ret body => do
      if receiver.isSome then
        throw (.refusal pos .schemeIntroduction "an ordinary function is outside the rigid checker")
      if !tps.isEmpty then
        throw (.refusal pos .schemeIntroduction "a nested quantified closure is outside the checked fragment")
      if !defaults.isEmpty then
        throw (.refusal pos .schemeIntroduction "a defaulted closure parameter is outside the rigid checker")
      if rest then
        throw (.refusal pos .schemeIntroduction "a rest closure parameter is outside the rigid checker")
      let inner ← ps.mapM fun (q : String × Json) => do
        return (q.1, ← lower pos .schemeIntroduction (annotationTy names q.2))
      let declared ← lower pos .schemeIntroduction (annotationTy names ret)
      return .lambda pos inner declared (← translate names body)
  | e => throw (.refusal e.span .genericValidation
      "body requires a variable, a primitive literal, an assignment, a call or a closure")
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)

private def unsupported (pos : Span) : Failure :=
  .refusal pos .genericValidation
    "body requires a variable, a primitive literal, an assignment, a call or a closure"

mutual

/-- An expression's type, read from the source and never from its claim:
trusting a claimed type is exactly what would let a body that happens to fit
every observed instantiation pass as universally valid. A write into a cell
is an obligation on the value against the cell's fixed contract; no
instantiation retypes the cell. Written as explicit matches so that
`SourceJudgments` can follow every branch. -/
def exprTyB (c : Ctx) (env : List (String × DirectObligation.Ty)) :
    Body → Except Failure DirectObligation.Ty
  | .var pos name => match env.lookup name with
      | some t => .ok t
      | none => .error (.refusal pos .genericValidation s!"body refers to unbound variable '{name}'")
  | .lit _ .vnull => .ok (.ground [0])
  | .lit _ (.vbool true) => .ok (.ground [1])
  | .lit _ (.vbool false) => .ok (.ground [2])
  | .lit _ .vundef => .ok (.ground [3])
  | .lit pos _ => .error (unsupported pos)
  | .assign pos name rhs =>
      if !c.cells.contains name then
        .error (.refusal pos .storageWrite s!"assignment to '{name}', which is not a cell")
      else match env.lookup name with
        | none => .error (.refusal pos .storageWrite s!"assignment to unbound '{name}'")
        | some contract => match exprTyB c env rhs with
          | .error e => .error e
          | .ok actual => match requireLeE c env .storageWrite (.expression pos) actual contract with
            | .error e => .error e
            | .ok () => .ok actual
  | .call pos callee args =>
      -- A call to a callable the body knows over rigid types, such as a
      -- callback parameter `(arg: T) => number`: each argument is an
      -- obligation against that parameter, and the result is the callable's.
      match callee with
      | .var cpos name => match env.lookup name with
        | some (.arrow rc ps r) =>
          if !(DirectObligation.Ty.ground [3]).leUnder c.parameters rc then
            .error (.refusal pos .callArgument "a plain call passes `undefined`, which the callable's receiver does not admit")
          else if ps.length != args.length then
            .error (.refusal pos .callArgument "call arity differs from the callable's parameters")
          else match argsTyB c env ps args with
            | .error e => .error e
            | .ok () => .ok r
        | some (.variadic rc ps e r) =>
          if !(DirectObligation.Ty.ground [3]).leUnder c.parameters rc then
            .error (.refusal pos .callArgument "a plain call passes `undefined`, which the callable's receiver does not admit")
          else if ps.length > args.length then
            .error (.refusal pos .callArgument "variadic call omits a required fixed parameter")
          else match argsTyB c env (ps ++ List.replicate (args.length - ps.length) e) args with
            | .error e => .error e
            | .ok () => .ok r
        | _ => .error (.refusal cpos .callArgument s!"'{name}' is not a callable over rigid types")
      | _ => .error (.refusal pos .callArgument "a call in a rigid body names a callable binding")
  | .lambda pos ps declared body =>
      -- The compiled graph takes a nested closure's types from its claim, so
      -- the claim must be exactly the source annotation.
      match c.claims.exprs.lookup pos with
      | none => .error (.refusal pos .schemeIntroduction "nested closure has no claim")
      | some claim =>
        if claim = DirectObligation.Ty.arrow .top (ps.map Prod.snd) declared then
          closureTyB c env pos ps declared body
        else .error (.refusal pos .schemeIntroduction "nested closure claim differs from its source annotation")

/-- Arguments against parameters, left to right. -/
def argsTyB (c : Ctx) (env : List (String × DirectObligation.Ty)) :
    List DirectObligation.Ty → List Body → Except Failure Unit
  | p :: ps, a :: args => match exprTyB c env a with
      | .error e => .error e
      | .ok actual => match requireLeE c env .callArgument (.expression a.span) actual p with
        | .error e => .error e
        | .ok () => argsTyB c env ps args
  | _, _ => .ok ()

/-- A closure's type is its annotation once its body establishes that
annotation under the binders in scope. A quantified closure and every closure
nested in it are checked here alike; failure is an obligation at the body. -/
def closureTyB (c : Ctx) (env : List (String × DirectObligation.Ty)) (pos : Span)
    (ps : List (String × DirectObligation.Ty)) (declared : DirectObligation.Ty) (body : Body) :
    Except Failure DirectObligation.Ty :=
  match exprTyB c (ps ++ env) body with
  | .error e => .error e
  | .ok actual =>
    if actual.leUnder c.parameters declared then .ok (.arrow .top (ps.map Prod.snd) declared)
    else .error (.obligation ⟨body.span, .schemeIntroduction,
      .schemeIntroduction c.parameters ((ps ++ env).map fun (name, type) => Binding.mk name type)
        (.closureBody body.span) actual declared⟩)

end

/-- Lowering, then typing. -/
def exprTy (c : Ctx) (env : List (String × DirectObligation.Ty)) (e : Fragment.Expr) :
    M DirectObligation.Ty := do
  liftE (exprTyB c env (← translate (c.parameters.map (·.name)) e))

/-- A quantified closure's type. An ordinary function binds `this` at its
receiver annotation, which may name the closure's binders; an arrow has none
of its own. -/
def closureTy (c : Ctx) (env : List (String × DirectObligation.Ty))
    (pos : Span) (ps : List (String × Json)) (ret : Json) (body : Fragment.Expr)
    (receiver : Option Json := none) : M DirectObligation.Ty := do
  let names := c.parameters.map (·.name)
  let inner ← ps.mapM fun q => do return (q.1, ← lower pos .schemeIntroduction (annotationTy names q.2))
  let declared ← lower pos .schemeIntroduction (annotationTy names ret)
  match receiver with
  | none => liftE (closureTyB c env pos inner declared (← translate names body))
  | some annot =>
    let R ← lower pos .schemeIntroduction (receiverTy names annot)
    match ← liftE (closureTyB c (("this", R) :: env) pos inner declared (← translate names body)) with
    | .arrow _ ps r => pure (.arrow R ps r)
    | t => pure t

/-! ### Declaration bodies -/

structure BindingT where
  name : String
  annot : Option DirectObligation.Ty
  init : Body

inductive StmtT where
  | constants (pos : Span) (bindings : List BindingT)
  | ret (pos : Span) (e : Body)

/-- Lower a declaration body's annotations. Only immutable copies and a return
are statements of this fragment. -/
def translateStmts (names : List String) (origin : Span) : List Fragment.Stmt → M (List StmtT)
  | [] => pure []
  | .ret pos e :: rest => do
      let e ← translate names e
      return .ret pos e :: (← translateStmts names origin rest)
  | .constants pos bindings :: rest => do
      let bindings ← bindings.mapM fun b => do
        let init ← translate names b.init
        let annot ← match b.annot with
          | some annot => do pure (some (← lower pos .bindingAnnotation (annotationTy names annot)))
          | none => pure none
        pure (⟨b.name, annot, init⟩ : BindingT)
      return .constants pos bindings :: (← translateStmts names origin rest)
  | _ :: _ => throw (.refusal origin .genericValidation "generic claim checking requires a checked variable-copy body")

/-- Each binding's claimed type at an entry, in scope order, each an
obligation against what the body established for it. -/
def entryBindings (c : Ctx) (source env : List (String × DirectObligation.Ty)) (pos : Span) :
    List (String × DirectObligation.Ty) → Except Failure (List (String × DirectObligation.Ty))
  | [] => .ok []
  | (name, actual) :: rest => match source.lookup name with
      | none => .error (.refusal pos .entryClaim s!"missing generic binding '{name}'")
      | some expected => match requireLeE c env .entryClaim (.binding name pos) actual expected with
        | .error e => .error e
        | .ok () => match entryBindings c source env pos rest with
          | .error e => .error e
          | .ok H => .ok ((name, expected) :: H)

/-- No name twice. -/
def distinct : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

def entryClaimsB (c : Ctx) (env : List (String × DirectObligation.Ty)) (pos : Span) :
    Except Failure (List (String × DirectObligation.Ty)) :=
  match c.claims.entries.lookup pos.1 with
  | none => .error (.refusal pos .entryClaim "missing statement environment")
  | some source =>
    if !distinct (source.map Prod.fst) then
      .error (.refusal pos .entryClaim "duplicate binding")
    else if source.length != env.length || source.any (fun p => !(env.map Prod.fst).contains p.1) then
      .error (.refusal pos .entryClaim "bindings differ from the source scope")
    else entryBindings c source env pos env

def expressionClaimB (c : Ctx) (env : List (String × DirectObligation.Ty)) (e : Body) :
    Except Failure DirectObligation.Ty :=
  match c.claims.exprs.lookup e.span with
  | none => .error (.refusal e.span .expressionClaim "missing expression claim")
  | some expected => match exprTyB c env e with
    | .error err => .error err
    | .ok actual => match requireLeE c env .expressionClaim (.expression e.span) actual expected with
      | .error err => .error err
      | .ok () => .ok expected

private def Body.sites : Body → List Span
  | b@(.var ..) | b@(.lit ..) => [b.span]
  | .assign p _ rhs => p :: rhs.sites
  | .call p fn args => p :: fn.sites ++ args.attach.flatMap (fun ⟨a, _⟩ => a.sites)
  | .lambda p _ _ body => p :: body.sites
termination_by b => sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)

private def claimSites : List StmtT → List Nat × List Span
  | [] => ([], [])
  | .ret pos e :: rest =>
    let (entries, expressions) := claimSites rest
    (pos.1 :: entries, e.sites ++ expressions)
  | .constants pos bs :: rest =>
    let (entries, expressions) := claimSites rest
    (pos.1 :: entries, bs.flatMap (·.init.sites) ++ expressions)

/-- The declarators of one `const`, each seeing the earlier. Inference retains
the checked initializer type, never a producer-selected binding type: a
weakened expression claim can lose precision, not regain it. -/
def bindingsB (c : Ctx) (pos : Span) :
    List (String × DirectObligation.Ty) → List BindingT →
      Except Failure (List (String × DirectObligation.Ty))
  | H, [] => .ok H
  | H, b :: rest => match expressionClaimB c H b.init with
      | .error e => .error e
      | .ok actual =>
        let expected := b.annot.getD actual
        match requireLeE c H .bindingAnnotation (.binding b.name pos) actual expected with
        | .error e => .error e
        | .ok () => bindingsB c pos (H ++ [(b.name, expected)]) rest

/-- A declaration body: immutable copies, each seeing the earlier, then a
return. One entry per statement; each declarator's claim is checked in the
scope the earlier ones extend. -/
def bodyClaimsB (c : Ctx) (env : List (String × DirectObligation.Ty))
    (result : DirectObligation.Ty) (origin : Span) : List StmtT → Except Failure Unit
  | [.ret pos e] => match entryClaimsB c env pos with
      | .error err => .error err
      | .ok H => match expressionClaimB c H e with
        | .error err => .error err
        | .ok actual => requireLeE c H .returnContract (.returned pos) actual result
  | .constants pos bindings :: rest => match entryClaimsB c env pos with
      | .error err => .error err
      | .ok H => match bindingsB c pos H bindings with
        | .error err => .error err
        | .ok H => bodyClaimsB c H result origin rest
  | _ => .error (.refusal origin .genericValidation "generic claim checking requires a checked variable-copy body")

/-- Claims on operands are obligations too. Checking a call's result must not
silently discard the producer's claims on the callee or actuals. -/
private def nestedClaims (c : Ctx) (env : List (String × DirectObligation.Ty)) :
    Body → Except Failure Unit
  | b@(.var ..) | b@(.lit ..) => do
      let _ ← expressionClaimB c env b
      pure ()
  | b@(.assign _ _ rhs) => do
      let _ ← expressionClaimB c env b
      nestedClaims c env rhs
  | b@(.call _ callee args) => do
      let _ ← expressionClaimB c env b
      nestedClaims c env callee
      args.attach.forM fun ⟨arg, _⟩ => nestedClaims c env arg
  | b@(.lambda _ ps _ body) => do
      let _ ← expressionClaimB c env b
      nestedClaims c (ps ++ env) body
termination_by b => sizeOf b
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)

private def nestedStatementClaims (c : Ctx) (env : List (String × DirectObligation.Ty)) :
    List StmtT → Except Failure Unit
  | [] => pure ()
  | .ret pos e :: rest => do
      let H ← entryClaimsB c env pos
      nestedClaims c H e
      nestedStatementClaims c H rest
  | .constants pos bs :: rest => do
      let H ← entryClaimsB c env pos
      let H ← bs.foldlM (fun H b => do
        nestedClaims c H b.init
        bindingsB c pos H [b]) H
      nestedStatementClaims c H rest

/-- The declared signature and the claimed one must agree exactly; a bound
never identifies its endpoints. -/
def checkScheme (f : Fragment.Fn) (typeParams : List Fragment.TypeParam)
    (claims : Claims) : SourceTypes.Lowering Unit := do
  if f.name != claims.name || f.namePos != claims.namePos then
    throw "function claim identity mismatch"
  if typeParams.isEmpty then throw "generic body requires type parameters"
  let names := (← parametersOf (← get) typeParams).map (·.name)
  if f.params.isEmpty then throw "generic body requires a value parameter"
  if f.params.dropLast.any (·.rest) then throw "a rest parameter must be the last one"
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

private def proofLookup (name : String) :
    List (String × α) → Option (Nat × α)
  | [] => none
  | (candidate, type) :: rest =>
    if candidate == name then some (0, type)
    else (proofLookup name rest).map fun (index, found) => (index + 1, found)

private def proofShape (origin : Span) :
    List Fragment.Stmt → M (List Fragment.Binding × Fragment.Expr)
  | [.ret _ e] => pure ([], e)
  | .constants _ bindings :: rest => do
      let (tail, e) ← proofShape origin rest
      return (bindings ++ tail, e)
  | _ => throw (.refusal origin .genericValidation
      "generic body has no semantic certificate constructor")

/-- Only source forms with semantic proof constructors can reach certification.
The default refusal is intentional for future forms until a proof rule exists. -/
private partial def closureProof (c : Ctx) (env : List (String × GenericCertificate.Slot)) :
    Fragment.Expr → M (Option GenericCertificate.Proof)
  | .lit _ (.vnum _) | .lit _ (.vstr _) => pure none
  | .lit _ v => pure (some (.lit v))
  | .atEnv _ e => closureProof c env e
  | .var pos name => match proofLookup name env with
      | some (index, .value _) => pure (some (.var index))
      | some (index, .cell _) => pure (some (.read index))
      | some (_, .argument _) => throw (.refusal pos .schemeIntroduction
          "a raw argument is not an initialized source binding")
      | none => throw (.refusal pos .schemeIntroduction s!"unbound capture '{name}'")
  | .lambda pos receiver tps ps defaults rest ret body => do
      if receiver.isSome || !tps.isEmpty || !defaults.isEmpty || rest then return none
      let names := c.parameters.map (·.name)
      let inner ← ps.mapM fun q => do
        return (q.1, ← lower pos .schemeIntroduction (annotationTy names q.2))
      let result ← lower pos .schemeIntroduction (annotationTy names ret)
      -- An arrow's own receiver slot precedes its parameters; its source
      -- `this` would be a capture, never that slot.
      let slots := inner.map fun (name, A) => (name, GenericCertificate.Slot.value A)
      let some proof ← closureProof c (("", .value .top) :: slots ++ env) body | return none
      return some (.lambda .top (inner.map Prod.snd) (.widen result proof))
  | .call _ callee args spreads => do
      if !spreads.isEmpty then return none
      let some fn ← closureProof c env callee | return none
      let proofs ← args.mapM (closureProof c env)
      let some actuals := proofs.mapM id | return none
      let fn := match fn.check c.parameters (env.map Prod.snd) with
        | some (_, .variadic rc ps e r) =>
          GenericCertificate.Proof.widen
            (.arrow rc (ps ++ List.replicate (args.length - ps.length) e) r) fn
        | _ => fn
      return some (.call fn actuals)
  | _ => pure none

/-- Compile a declaration body to the independent semantic proof language,
through the same compiler as a closure body: a declaration is the depth-zero
case. Each immutable copy is a `let` widened to its checked binding type, and
the return is widened to the declared result. A form without a proof
constructor stays an explicit certification gap even though the checker types
it. `SourceJudgments` records the now-supported call and literal returns. -/
private def proofBody (c : Ctx) (initial : List (String × DirectObligation.Ty))
    (result : DirectObligation.Ty) (origin : Span)
    (statements : List Fragment.Stmt) : M GenericCertificate.Proof := do
  let (bindings, returned) ← proofShape origin statements
  let slotsOf (env : List (String × DirectObligation.Ty)) :=
    env.map fun (name, type) => (name, GenericCertificate.Slot.value type)
  let (env, initializers) ← bindings.foldlM (fun (env, initializers) b => do
    let some init ← closureProof c (slotsOf env) b.init
      | throw (.refusal b.init.span .genericValidation
          "generic expression has no semantic certificate constructor")
    let actual ← exprTy c env b.init
    let expected ← (match b.annot with
      | some annot => lower b.namePos .bindingAnnotation
          (annotationTy (c.parameters.map (·.name)) annot)
      | none => pure actual)
    unless actual.leUnder c.parameters expected do
      throw (.obligation ⟨b.namePos, .bindingAnnotation,
        .subtyping c.parameters ((env.filter (·.1 != "")).map fun (name, type) => ⟨name, type⟩)
          (.binding b.name b.namePos) actual expected⟩)
    return ((b.name, expected) :: env, initializers ++ [(.widen expected init)]))
    (initial, [])
  let some body ← closureProof c (slotsOf env) returned
    | throw (.refusal returned.span .genericValidation
        "generic expression has no semantic certificate constructor")
  return initializers.foldr GenericCertificate.Proof.letE (.widen result body)

/-- Default initialization is checked under the universal binders, preserving
source effect order and capture dependencies before body checking. It cannot
borrow types from observed calls. -/
def parameterDefaults (c : Ctx) (env : List (String × DirectObligation.Ty))
    (pos : Span) (ps : List (String × Json)) (defaults : List (Nat × Fragment.Expr)) : M Unit := do
  let mut scope := env
  let order ← refuse pos .schemeIntroduction (Fragment.parameterOrder ps defaults)
  for i in order do
    let some (name, annot) := ps[i]? | throw (.refusal pos .schemeIntroduction "invalid parameter schedule")
    let expected ← lower pos .schemeIntroduction (annotationTy (c.parameters.map (·.name)) annot)
    if let some init := defaults.lookup i then
      let actual ← exprTy c scope init
      liftE (requireLeE c scope .bindingAnnotation (.expression init.span) actual expected)
    scope := (name, expected) :: scope

/-- Reconstruct a universal closure certificate independently of observed calls.
The proof language handles immutable reads, closures and calls; a cell read must never be
compiled as a read of the cell identity. Missing constructors stay explicit at
the final certification boundary. -/
def closureCertificate (c : Ctx) (env : List (String × DirectObligation.Ty))
    (storage : List Fragment.Binding)
    (pos : Span) (ps : List (String × Json)) (ret : Json) (body : Fragment.Expr)
    (defaults : List (Nat × Fragment.Expr) := []) (rest : Bool := false)
    (receiver : Option Json := none) :
    M (Option GenericCertificate.ClosureCertificate) := do
  -- Runtime cell identities carry the source's fixed storage annotation. An
  -- entry claim about current contents cannot supply this lifetime contract.
  let captures ← env.mapM fun (name, actual) => do
    if c.cells.contains name then
      let some binding := storage.find? (·.name == name)
        | throw (.refusal pos .schemeIntroduction s!"missing storage declaration for '{name}'")
      let some annot := binding.annot
        | throw (.refusal binding.namePos .schemeIntroduction "captured storage needs a fixed annotation")
      let contract ← lower binding.namePos .schemeIntroduction (annotationTy [] annot)
      return (name, GenericCertificate.Slot.cell contract)
    else return (name, GenericCertificate.Slot.value actual)
  let names := c.parameters.map (·.name)
  let inner ← ps.mapM fun q => do
    return (q.1, ← lower pos .schemeIntroduction (annotationTy names q.2))
  let result ← lower pos .schemeIntroduction (annotationTy names ret)
  -- An ordinary function's receiver slot is `this`, at its annotation; an
  -- arrow's is anonymous and top.
  let (receiverName, R) ← match receiver with
    | some annot => do pure ("this", ← lower pos .schemeIntroduction (receiverTy names annot))
    | none => pure ("", DirectObligation.Ty.top)
  let (inner, restBinding) ← if rest then
    match inner.reverse with
    | (name, .array E) :: fixed => pure (fixed.reverse, some (name, E))
    | _ => throw (.refusal pos .schemeIntroduction "a quantified rest requires a mutable array contract")
    else pure (inner, none)
  let inputs := inner.zipIdx.map fun ((_, A), i) =>
    if (defaults.lookup i).isNone then GenericCertificate.Input.value A else .defaulted A
  let mut slots := ((inner.map Prod.fst).zip inputs).map fun (name, input) =>
    (if defaults.isEmpty then name else "", input.slot)
  -- The receiver slot precedes the parameters, after a rest array; an arrow
  -- never reads it.
  slots := (match restBinding with
    | none => []
    | some (name, E) => [(if defaults.isEmpty then name else "", .value (.array E))]) ++
    (receiverName, .value R) :: slots ++ captures
  let offset := if restBinding.isSome then 2 else 1
  let mut initializers : List GenericCertificate.Proof := []
  let order ← refuse pos .schemeIntroduction (Fragment.parameterOrder ps defaults)
  for i in order do
    if rest && i == inner.length then
      let some (name, E) := restBinding | throw (.refusal pos .schemeIntroduction "missing rest binding")
      slots := slots.set initializers.length (name, .value (.array E))
    else
      let some (name, A) := inner[i]? | throw (.refusal pos .schemeIntroduction "invalid parameter schedule")
      match defaults.lookup i with
      | none => slots := slots.set (initializers.length + offset + i) (name, .value A)
      | some init =>
        let some proof ← closureProof c slots init | return none
        initializers := initializers ++ [.defaultE (initializers.length + offset + i) proof]
        slots := (name, .value A) :: slots
  let some proof ← closureProof c slots body | return none
  return some ⟨c.parameters, inputs, captures.map Prod.snd, result,
    initializers.foldr GenericCertificate.Proof.letE (.widen result proof), restBinding.map Prod.snd,
    R⟩

/-- Both production and independent consumption reconstruct these obligations.
Every source entry and expression must occur exactly once; no supplied point is
silently ignored. -/
def check (f : Fragment.Fn) (typeParams : List Fragment.TypeParam) (claims : Claims) :
    M GenericCertificate.ClosureCertificate := do
  let parameters ← refuse f.namePos .genericValidation (parametersOf (← get) typeParams)
  let names := parameters.map (·.name)
  let c : Ctx := ⟨parameters, claims, []⟩
  let statements ← translateStmts names f.namePos f.body
  let (entries, expressions) := claimSites statements
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
  let result ← lower f.namePos .genericValidation (annotationTy names f.ret)
  liftE (nestedStatementClaims c env statements)
  liftE (bodyClaimsB c env result f.namePos statements)
  -- The remaining source-shape and exact-signature invariants, once the claim
  -- pass has exposed any failed inclusion.
  lower f.namePos .genericValidation (checkScheme f typeParams claims)
  let result ← lower f.namePos .genericValidation (annotationTy names f.ret)
  -- The body sees the rest array, then the receiver slot, which a declaration
  -- checked here never reads, then the fixed parameters.
  let (bodyEnv, fixed, rest) ← if f.params.any (·.rest) then
    match env.reverse with
    | (name, .array E) :: earlier =>
      pure ((name, .array E) :: ("", .top) :: earlier.reverse, earlier.reverse, some E)
    | _ => throw (.refusal f.namePos .genericValidation "a quantified rest requires a mutable array contract")
    else pure (("", .top) :: env, env, none)
  let proof ← proofBody c bodyEnv result f.namePos f.body
  let certificate : GenericCertificate.ClosureCertificate :=
    ⟨parameters, fixed.map (fun p => GenericCertificate.Input.value p.2), [], result, proof, rest,
      .top⟩
  if certificate.check.isNone then
    throw (.refusal f.namePos .genericValidation "generated generic certificate is invalid")
  return certificate

private def paramT : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "param"), ("name", toJson "T")]])]
private def T : DirectObligation.Ty := .rigid "T"
private def bool : DirectObligation.Ty := .ground [1, 2]
private def tpT : Fragment.TypeParam := ⟨"T", none⟩
private def tpTbool : Fragment.TypeParam := ⟨"T", some booleanType⟩

private def idFn : Fragment.Fn :=
  ⟨"id", (0, 2), [⟨"x", paramT, false⟩], paramT, [.ret (10, 18) (.var (17, 18) "x")]⟩
private def idClaims : Claims :=
  ⟨"id", (0, 2), [("x", T)], T, [(10, [("x", T)])], [((17, 18), T)]⟩
private def asBoolFn : Fragment.Fn :=
  ⟨"asBoolean", (0, 2), [⟨"x", paramT, false⟩], booleanType, [.ret (10, 18) (.var (17, 18) "x")]⟩
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
  ⟨"bind", (0, 2), [⟨"x", paramT, false⟩], paramT,
    [.cst (2, 3) "y" (some paramT) (.var (4, 5) "x"),
     .ret (6, 7) (.var (8, 9) "y")]⟩
private def bindClaims : Claims :=
  ⟨"bind", (0, 2), [("x", T)], T,
   [(2, [("x", T)]), (6, [("x", T), ("y", T)])], [((4, 5), T), ((8, 9), T)]⟩
private def fstFn : Fragment.Fn :=
  ⟨"fst", (0, 2), [⟨"x", paramT, false⟩, ⟨"y", paramT, false⟩], paramT,
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

end Verification.Model.GenericSource
