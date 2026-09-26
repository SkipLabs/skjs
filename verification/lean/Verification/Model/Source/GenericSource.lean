import Verification.Model.Source.Fragment
import Verification.Model.Programs.CellClaims
import Verification.Model.Types.GenericCertificate

/-! Bodies under rigid binders: the one checker for a generic declaration's
body and for a quantified closure's, whatever its nesting.

A body is a variable, a primitive literal, or a closure whose annotation names
the binders in scope; a declaration body is a sequence of immutable copies and
expression statements, then a return or the body's end. Everything is typed
from the source under distinct rigid parameters and forward upper bounds,
along `letE_safeP` and `var_safeP`; `T extends boolean` is the assumption
`T ≤ boolean`, and any ground bound, `T extends string | number` or a declared
`T extends Json`, is the assumption `T ≤` it. Both are walked by the direct relation whose
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
    let atoms ← jArr j "atoms"
    -- A union mentioning a binder, `string | T`: each alternative on its own.
    if atoms.length > 1 then
      return .mkUnion (← atoms.mapM fun atom =>
        annotationTy names (Json.mkObj [("top", toJson false), ("atoms", toJson [atom])]))
    let [atom] := atoms
      | throw "a rigid annotation is a binder, a function type over binders, or a ground type"
    if (← jStr (← jField atom "a")) != "function" then
      throw "a rigid annotation is a binder, a function type over binders, or a ground type"
    let receiver ← receiverTy names (← jField atom "this")
    let params ← (← jArr atom "params").mapM (annotationTy names)
    let result ← annotationTy names (← jField atom "result")
    match (atom.getObjVal? "rest").toOption with
    | some e => return .variadic receiver params (← annotationTy names e) result
    | none => return .arrow receiver params result
  -- A ground type holding `unknown`, as `void` does, is top, as its claim is.
  let A ← Fragment.translate j
  let T ← get
  if SourceTypes.reachesParameter T A then
    throw "a type over a binder's parameter row is the graph checker's"
  return if A.any (fun l => T[l]? == some (.clauses [.top])) then .top else .ground A

/-- A receiver contract as a direct type, by the one annotation converter. -/
partial def receiverTy (names : List String) (j : Json) :
    SourceTypes.Lowering DirectObligation.Ty :=
  annotationTy names j
end

/-- A ground bound names rows installed when the source declarations are
prepared, whatever its source form. Raw source cannot supply this internal
atom. -/
def declaredBound (T : SourceTypes.Table) (bound : Json) : Except String (List Nat) := do
  CellClaims.fieldsExactly bound ["top", "atoms"]
  if ← (← jField bound "top").getBool? then throw "a bound cannot be unknown"
  let atoms ← jArr bound "atoms"
  if atoms.isEmpty then throw "expected declared graph atoms"
  atoms.mapM fun atom => do
    CellClaims.fieldsExactly atom ["a", "label"]
    if (← jStr (← jField atom "a")) != "graph" then throw "expected a declared graph atom"
    let label ← (← jField atom "label").getNat?
    if label >= T.length then throw "declared bound graph label is absent"
    return label

/-- A binder's bound: an earlier binder, or a ground type, which the prepared
source states as graph rows (`boolean` also in its own spelling). -/
def boundOf (T : SourceTypes.Table) (seen : List Parameter) :
    Option Json → Except String (Option DirectObligation.Ty)
  | none => .ok none
  | some bound =>
    if isBooleanType bound then .ok (some (DirectObligation.Ty.ground [1, 2]))
    else match paramName bound with
      | .ok u =>
        if seen.any (·.name == u) then .ok (some (DirectObligation.Ty.rigid u))
        else .error "a type-parameter bound must name an earlier parameter"
      | .error _ => match declaredBound T bound with
        | .ok labels => .ok (some (.ground labels))
        | .error _ => .error "a type-parameter bound is a ground type or an earlier type parameter"

/-- Rigid binders in declaration order. A bound is an earlier binder or a
ground type. Duplicate names, forward
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

/-- A closure's result: its annotation, or, where the source states none, the
result of the closure's own claimed arrow, which must take exactly the
annotated parameters. Either way the body is then checked against it, so the
claim proposes the result and is never trusted for it. -/
def lambdaResult (names : List String) (claimed : List (Span × DirectObligation.Ty))
    (pos : Span) (inner : List (String × DirectObligation.Ty)) : Option Json → M DirectObligation.Ty
  | some ret => lower pos .schemeIntroduction (annotationTy names ret)
  | none => match claimed.lookup pos with
    | some (.arrow .top ps result) =>
      if ps == inner.map Prod.snd then pure result
      else throw (.refusal pos .schemeIntroduction "nested closure claim differs from its source annotation")
    | _ => throw (.refusal pos .schemeIntroduction "a closure under a binder without a result annotation needs its claimed arrow")

/-- Lower a source expression's annotations. Forms the checker does not type
are refused here, by name, at their span. `claimed` are the expression claims,
which supply the result of a closure the source does not annotate. -/
def translate (names : List String) (claimed : List (Span × DirectObligation.Ty)) :
    Fragment.Expr → M Body
  | .var pos name => pure (.var pos name)
  | .lit pos v => pure (.lit pos v)
  -- A block body `{ return e; }` is its returned expression; the statement
  -- entry around it is a claim site of the stateful lowering, not a value.
  | .atEnv _ e => translate names claimed e
  | .assign pos name _ rhs => do return .assign pos name (← translate names claimed rhs)
  | .call pos callee args spreads _ => do
      if !spreads.isEmpty then
        throw (.refusal pos .schemeIntroduction "a spread argument is outside the rigid checker")
      let callee ← translate names claimed callee
      let args ← args.attach.mapM fun ⟨a, _⟩ => translate names claimed a
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
      let declared ← lambdaResult names claimed pos inner ret
      return .lambda pos inner declared (← translate names claimed body)
  | e => throw (.refusal e.span .genericValidation
      "body requires a variable, a primitive literal, an assignment, a call or a closure: a quantified closure's body is checked by the rigid checker, which reads only these")
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)

private def unsupported (pos : Span) : Failure :=
  .refusal pos .genericValidation
    "body requires a variable, a primitive literal, an assignment, a call or a closure: a quantified closure's body is checked by the rigid checker, which reads only these"

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
  liftE (exprTyB c env (← translate (c.parameters.map (·.name)) c.claims.exprs e))

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
  | none => liftE (closureTyB c env pos inner declared (← translate names c.claims.exprs body))
  | some annot =>
    let R ← lower pos .schemeIntroduction (receiverTy names annot)
    match ← liftE (closureTyB c (("this", R) :: env) pos inner declared (← translate names c.claims.exprs body)) with
    | .arrow _ ps r => pure (.arrow R ps r)
    | t => pure t

/-! ### Declaration bodies -/

private def proofLookup (name : String) :
    List (String × α) → Option (Nat × α)
  | [] => none
  | (candidate, type) :: rest =>
    if candidate == name then some (0, type)
    else (proofLookup name rest).map fun (index, found) => (index + 1, found)

/-- Only source forms with semantic proof constructors can reach certification.
The default refusal is intentional for future forms until a proof rule exists. -/
private partial def closureProof (c : Ctx) (env : List (String × GenericCertificate.Slot)) :
    Fragment.Expr → M (Option GenericCertificate.Proof)
  | .lit _ (.vnum _) | .lit _ (.vstr _) | .lit _ (.vbigint _) => pure none
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
      let result ← lambdaResult names c.claims.exprs pos inner ret
      -- An arrow's own receiver slot precedes its parameters; its source
      -- `this` would be a capture, never that slot.
      let slots := inner.map fun (name, A) => (name, GenericCertificate.Slot.value A)
      let some proof ← closureProof c (("", .value .top) :: slots ++ env) body | return none
      return some (.lambda .top (inner.map Prod.snd) (.widen result proof))
  | .call _ callee args spreads _ => do
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
  -- The receiver slot precedes the parameters, after a rest array and the
  -- rest store it was wrapped from; an arrow never reads it.
  slots := (match restBinding with
    | none => []
    | some (name, E) => [(if defaults.isEmpty then name else "", .value (.array E)),
        ("", .value .top)]) ++
    (receiverName, .value R) :: slots ++ captures
  let offset := if restBinding.isSome then 3 else 1
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
  -- A rest array is allocated with `Array.prototype`, which the closure
  -- captures last, under a name no source identifier spells.
  let captured := captures.map Prod.snd ++
    (if rest then [.value (.ground [SourceTypes.arrayProtoLabel])] else [])
  return some ⟨c.parameters, inputs, captured, result,
    initializers.foldr GenericCertificate.Proof.letE (.widen result proof), restBinding.map Prod.snd,
    R, 2 + inputs.length + captures.length⟩

end Verification.Model.GenericSource
