import Verification.ExperimentState.SourceExtraction
import Verification.ExperimentState.TypeSchemes

/-! Strict producer-independent sidecars. A document carries its own type table,
which its labels index; the primitives are its first four rows. The external
parser supplies the source fingerprint; this module checks agreement, not hashing
or the parser's semantic correctness. Saved statuses are not part of the schema. -/
namespace Verification.ExperimentState.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction

/-- A rigid name refers to the enclosing source function's binder. It is never
interpreted as a ground graph label or replaced with its upper bound. -/
inductive ClaimType where
  | labels : List Nat → ClaimType
  | param : String → ClaimType
  | scheme : List (String × Option ClaimType) → List ClaimType → ClaimType → ClaimType
  | unavailable : String → ClaimType
  deriving Repr, BEq
instance : Coe (List Nat) ClaimType := ⟨ClaimType.labels⟩

private partial def ClaimType.toJson : ClaimType → Json
  | .labels A => Lean.toJson A
  | .param name => Json.mkObj [("param", Lean.toJson name)]
  | .scheme typeParams params result => Json.mkObj [("scheme", Json.mkObj [
      ("typeParams", Lean.toJson (typeParams.map fun p => Json.mkObj [
        ("name", Lean.toJson p.1), ("bound", p.2.map ClaimType.toJson |>.getD Json.null)])),
      ("params", Lean.toJson (params.map ClaimType.toJson)),
      ("result", ClaimType.toJson result)])]
  | .unavailable reason => Json.mkObj [("unavailable", Lean.toJson reason)]

instance : ToJson ClaimType where
  toJson := ClaimType.toJson

private partial def ClaimType.fromJson (j : Json) : Except String ClaimType :=
  match j with
  | .arr _ => ClaimType.labels <$> Lean.fromJson? j
  | _ => do
    if let .ok reason := j.getObjValAs? String "unavailable" then
      if j != Json.mkObj [("unavailable", Lean.toJson reason)] || reason.isEmpty then
        throw "invalid unavailable claim"
      return .unavailable reason
    if let .ok s := j.getObjVal? "scheme" then
      CellClaims.fieldsExactly j ["scheme"]
      CellClaims.fieldsExactly s ["typeParams", "params", "result"]
      let typeParams ← (← jArr s "typeParams").mapM fun p => do
        CellClaims.fieldsExactly p ["name", "bound"]
        let name ← jStr (← jField p "name")
        let bound ← jField p "bound"
        let bound ← if bound == .null then pure none else do
          pure (some (← ClaimType.fromJson bound))
        return (name, bound)
      let params ← (← jArr s "params").mapM ClaimType.fromJson
      return .scheme typeParams params (← ClaimType.fromJson (← jField s "result"))
    let name ← jStr (← jField j "param")
    if j != Json.mkObj [("param", Lean.toJson name)] || name.isEmpty then
      throw "invalid rigid parameter claim"
    return .param name

instance : FromJson ClaimType where
  fromJson? := ClaimType.fromJson
private def ClaimType.ground : ClaimType → SourceClaims.Candidate
  | .labels A => .ok A
  | .param _ => .error "rigid parameter outside generic function"
  | .scheme .. => .error "quantified callable requires scheme checking"
  | .unavailable reason => .error reason

/-- What a point currently holds, field by field: an object has one location
per named field, so an assertion about its contents names the field it is
about. A point that names no record carries none. -/
abbrev CurrentFields := List (String × List Nat)

structure Binding where
  name : String
  type : ClaimType
  current : Option CurrentFields := none
  deriving ToJson, FromJson
structure Entry where
  start : Nat
  bindings : List Binding
  deriving ToJson, FromJson
/-- The type arguments one call supplies for a scheme's binders. It is the
producer's proposed elimination, re-checked here; it is never itself evidence. -/
structure Instantiation where
  name : String
  type : ClaimType
  deriving ToJson, FromJson, BEq

structure Expression where
  pos : Span
  type : ClaimType
  current : Option CurrentFields := none
  instantiate : Option (List Instantiation) := none
  deriving FromJson

/-- `current` is required and explicitly `null`, because silence about a
record's contents is itself an assertion. Absence of `instantiate` asserts
nothing: the site simply calls no quantified callable, so it is omitted rather
than stated, and no producer has to write it at every expression. -/
instance : ToJson Expression where
  toJson e := Json.mkObj ([("pos", toJson e.pos), ("type", toJson e.type),
    ("current", toJson e.current)] ++
    (match e.instantiate with
     | none => []
     | some xs => [("instantiate", toJson xs)]))
structure Function where
  name : String
  namePos : Span
  params : List Binding
  result : ClaimType
  entries : List Entry
  expressions : List Expression
  deriving ToJson, FromJson
structure Document where
  file : String
  sourceSha256 : String
  types : SourceTypes.Table
  functions : List Function
  deriving ToJson, FromJson


def Function.normalized (f : Function) : SourceClaims.Function :=
  ⟨f.name,f.namePos,f.params.map (fun b => (b.name,b.type.ground)),f.result.ground,
    f.entries.map (fun e => (e.start,e.bindings.map (fun b => (b.name,b.type.ground)))),
    f.expressions.map (fun e => (e.pos,e.type.ground)),
    f.entries.map (fun e => (e.start,e.bindings.filterMap fun b => b.current.map (b.name,·))),
    f.expressions.filterMap (fun e => e.current.map (e.pos,·)),
    -- Scheme compilation supplies these; an ordinary document has none.
    []⟩

/-! ## Scheme compilation

The one interface between quantified source checking and the ordinary graph
evidence engine. Introduction is checked first, universally, once per allocated
closure and independently of how many calls the program makes or at what types.
Each elimination then validates its own explicit substitution. Only after both
does this section compile the checked eliminations into ordinary arrows.

The per-arrow body derivations that produces are consequences of the universal
result, never its justification: a closure that satisfies every observed call
but cannot produce an arbitrary rigid result fails the gate below, before any
arrow exists. Replacing this section with a first-class scheme certificate
changes neither Fragment, SourceClaims, nor the producer's semantic types. -/
private def claimHasScheme : ClaimType → Bool
  | .scheme .. => true
  | _ => false

private def Function.hasScheme (f : Function) : Bool :=
  claimHasScheme f.result || f.params.any (claimHasScheme ·.type) ||
    f.entries.any (fun e => e.bindings.any (claimHasScheme ·.type)) ||
    f.expressions.any (claimHasScheme ·.type)

/-- Direct rigid/scheme checks do not pretend to be ordinary graph sequents,
but their failures use the same mandatory located diagnostic channel. The
viewer consumes this record structurally; the prose is only its conclusion. -/
private def directFailure (T : SourceTypes.Table) (pos : Span) (role system statement : String)
    (context : List String := []) : String :=
  RequestJson.withDiagnostic s!"source direct obligation at [{pos.1},{pos.2}): {statement}"
    [("kind",toJson "direct-obligation"),("phase",toJson "request-validation"),
     ("outcome",toJson "not-established"),("id",toJson s!"{system}:{pos.1}"),
     ("sourceMap",toJson (SourceMapEntry.mk pos role none
       (context.map fun name => (Descriptor.mk name none)))),
     ("judgment",Json.mkObj [("system",toJson system),("statement",toJson statement)]),
     ("fuel",toJson 0),("types",toJson T)]

namespace Scheme

/-- A universal type: a rigid binder of the scheme under check, or a ground
graph type. No assignment identifies a ground type with an arbitrary binder,
which is what keeps the gate independent of the calls a program happens to make. -/
private inductive UTy where
  | rigid : String → UTy
  | ground : List Nat → UTy
  deriving BEq, Repr

private def UTy.le : UTy → UTy → Bool
  | .rigid a, .rigid b => a == b
  | .ground A, .ground B => A.all B.contains
  | _, _ => false

private def UTy.render (T : SourceTypes.Table) : UTy → String
  | .rigid a => a
  | .ground A => SourceTypes.render T A

private def ofClaim (role : String) : ClaimType → Except String UTy
  | .param name => pure (.rigid name)
  | .labels A => pure (.ground A)
  | .scheme .. => throw s!"a nested scheme is outside {role}"
  | .unavailable reason => throw reason

private def groundOf (role : String) : ClaimType → Except String (List Nat)
  | .labels A => pure A
  | .param name => throw s!"{role} is still the rigid parameter '{name}'"
  | .scheme .. => throw s!"{role} is a scheme, not a ground type"
  | .unavailable reason => throw reason

/-- The body's type is read from the source, never from its claim. Trusting a
claimed body type is exactly what would let a closure that happens to work at
every observed instantiation pass as universally valid. -/
private def bodyUTy (env : List (String × UTy)) : Fragment.Expr → Except String UTy
  | .var _ name => match env.lookup name with
      | some t => pure t
      | none => throw s!"quantified closure body refers to unbound '{name}'"
  | .lit _ .vnull => pure (.ground [0])
  | .lit _ (.vbool true) => pure (.ground [1])
  | .lit _ (.vbool false) => pure (.ground [2])
  | .lit _ .vundef => pure (.ground [3])
  | _ => throw "quantified closure body is outside the checked fragment: a variable or a primitive literal"

/-- Capture-avoiding: a nested scheme's own binders shadow the substitution. -/
private partial def subst (σ : List (String × ClaimType)) : ClaimType → ClaimType
  | .param name => (σ.lookup name).getD (.param name)
  | .scheme tps ps r =>
      let inner := σ.filter fun q => !(tps.map Prod.fst).contains q.1
      .scheme (tps.map fun q => (q.1, q.2.map (subst inner))) (ps.map (subst inner))
        (subst inner r)
  | c => c

/-- The wire presentation of a semantic scheme. `TypeSchemes.identityScheme` is
the one scheme with a universal allocation theorem (`identity_scheme_safe`);
the checker below is general and does not special-case it, so this keeps that
theorem's scheme recognisable in the claim language and makes a drift on either
side visible. It is a correspondence, not a proof that the checker implements
the rule. -/
private def ofScheme (names : List String) (s : TypeSchemes.Scheme Nat) :
    Option ClaimType := do
  let binder (i : Nat) : Option String := names[i-1]?
  let rigid (p : List Nat) : Option ClaimType := do
    let [i] := p | none
    return .param (← binder i)
  let [(ps, r)] := s.signatures | none
  guard (s.bounds.isEmpty && s.binders == (List.range names.length).map (· + 1))
  return .scheme (names.map (·, none)) (← ps.mapM rigid) (← rigid r)

#guard ofScheme ["T"] TypeSchemes.identityScheme
  == some (.scheme [("T", none)] [.param "T"] (.param "T"))

private structure Closure where
  span : Span
  binding : String
  binders : List String
  paramNames : List String
  params : List ClaimType
  result : ClaimType
  body : Fragment.Expr
  declStart : Nat

/-- One quantified closure per function in this slice. The declared signature
must name the closure's own binders; bounded binders are a later row. -/
private def find (f : Fragment.Fn) : Except String (Option Closure) := do
  let mut found : Option Closure := none
  for s in f.body do
    if let .constants pos bs := s then
      for b in bs do
        if let .lambda lpos tps ps ret body := b.init then
          if !tps.isEmpty then
            if found.isSome then
              throw "this slice checks one quantified closure per function"
            if tps.any (·.bound.isSome) then
              throw "a bounded quantified closure is not implemented yet"
            let names := tps.map (·.name)
            if names.eraseDups.length != names.length then throw "duplicate closure binder"
            let params ← ps.mapM fun q => do
              let n ← GenericSource.paramName q.2
              if !names.contains n then
                throw "a quantified closure parameter must name one of its own binders"
              pure (ClaimType.param n)
            let r ← GenericSource.paramName ret
            if !names.contains r then
              throw "a quantified closure result must name one of its own binders"
            found := some ⟨lpos, b.name, names, ps.map Prod.fst, params, .param r, body, pos.1⟩
  return found

/-- Introduction. The gate every accepted scheme passes, whatever its calls. -/
private def introduce (T : SourceTypes.Table) (c : Closure) (claims : Function) : Except String Unit := do
  let some entry := claims.entries.find? (·.start == c.declStart)
    | throw "quantified closure declaration has no entry claim"
  -- Captures keep the types they already have; no instantiation may retype them.
  let outer ← entry.bindings.mapM fun b => do
    return (b.name, ← ofClaim "a quantified closure's captured scope" b.type)
  let ps ← c.params.mapM (ofClaim "a quantified closure parameter")
  let actual ← bodyUTy (c.paramNames.zip ps ++ outer) c.body
  let expected ← ofClaim "a quantified closure result" c.result
  unless actual.le expected do
    let binders := String.intercalate ", " c.binders
    throw s!"quantified closure body does not satisfy its scheme universally: cannot establish {actual.render T} ≤ {expected.render T} for every instantiation of [{binders}]"

/-- Elimination, then compilation. Each call validates its own substitution;
the arrows are derived from the scheme signature by that substitution, so a
forged instantiation can only name another genuine instance of a scheme that
has already passed the universal gate. -/
private def compile (T : SourceTypes.Table) (f : Fragment.Fn) (claims : Function) :
    Except String (SourceTypes.Table × Function ×
      List (Span × List (List (Span × SourceClaims.Candidate)))) := do
  let some c ← find f
    | throw "a scheme claim has no quantified closure in its source"
  introduce T c claims
  let sites := claims.expressions.filterMap fun e => e.instantiate.map ((e.pos, ·))
  if sites.isEmpty then throw "a quantified closure has no checked instantiation"
  let subs ← sites.mapM fun (pos, inst) => do
    let names := inst.map (·.name)
    if names.eraseDups.length != names.length then
      throw s!"duplicate type argument at [{pos.1},{pos.2})"
    if names.length != c.binders.length || names.any (!c.binders.contains ·) then
      throw s!"type arguments at [{pos.1},{pos.2}) do not instantiate exactly the closure's binders"
    for i in inst do
      let _ ← groundOf s!"the type argument for '{i.name}' at [{pos.1},{pos.2})" i.type
    pure (inst.map fun i => (i.name, i.type))
  let σs := subs.foldl (fun acc σ => if acc.contains σ then acc else acc ++ [σ]) []
  let arrows ← σs.mapM fun σ => do
    let ps ← c.params.mapM fun q => groundOf "a substituted parameter" (subst σ q)
    let r ← groundOf "a substituted result" (subst σ c.result)
    pure (ps, r)
  let clause : PositiveNormalization.Clause (List Nat) := .arrs arrows
  let T := SourceTypes.intern T clause
  let arrow := SourceTypes.label T clause
  let expected : ClaimType := .scheme (c.binders.map (·, none)) c.params c.result
  let inside (p : Span) : Bool := c.span.1 ≤ p.1 && p.2 ≤ c.span.2
  let retype (pos : Span) (t : ClaimType) : Except String ClaimType :=
    match t with
    | .scheme .. =>
      if t == expected then pure (.labels [arrow])
      else throw s!"quantified claim at [{pos.1},{pos.2}) differs from its source scheme"
    | .param n =>
      if inside pos then pure t
      else throw s!"rigid parameter '{n}' escapes its closure at [{pos.1},{pos.2})"
    | _ => pure t
  let claims := { claims with
    result := ← retype claims.namePos claims.result
    params := ← claims.params.mapM fun b => do
      return { b with type := ← retype claims.namePos b.type }
    entries := ← claims.entries.mapM fun e => do
      return { e with bindings := ← e.bindings.mapM fun b => do
        return { b with type := ← retype (e.start, e.start + 1) b.type } }
    expressions := ← claims.expressions.mapM fun e => do
      return { e with type := ← retype e.pos e.type } }
  -- One source span, one type per instantiation: the interior claims are
  -- substituted rather than re-cast, which is what no single claim can do.
  let interior := claims.expressions.filter fun e => inside e.pos && e.pos != c.span
  let overlays := σs.map fun σ =>
    interior.map fun e => (e.pos, (subst σ e.type).ground)
  return (T, claims, [(c.span, overlays)])

end Scheme


/-- The table starts with the primitives and refers only to its own labels. -/
private def validTable (T : SourceTypes.Table) : Bool :=
  SourceTypes.initial.isPrefixOf T && (T.flatMap id |>.flatMap clauseTypes).all (validTy T.length)
private partial def validType (T : SourceTypes.Table) : ClaimType → Bool
  | .param name => !name.isEmpty
  | .scheme typeParams params result =>
      !typeParams.isEmpty &&
      (typeParams.map Prod.fst).eraseDups.length == typeParams.length &&
      typeParams.all (fun p => !p.1.isEmpty && p.2.all (validType T)) &&
      params.all (validType T) && validType T result
  | .unavailable reason => !reason.isEmpty
  | .labels A => validTy T.length A && A == A.mergeSort (· ≤ ·) && A.eraseDups == A
/-- Every asserted field is one the point's own record contract names, each at
most once, at a type this table has. The asserted type need not be finite: a
field the extractor cannot turn into a literal assertion becomes an obligation
that the storage contract already implies it. -/
private def validCurrent (T : SourceTypes.Table) (A : ClaimType) (current : Option CurrentFields) : Bool :=
  match current with
  | none => true
  | some fs =>
    !fs.isEmpty && (fs.map Prod.fst).eraseDups.length == fs.length &&
    (match PositiveRules.expand (SourceTypes.graph T) (A.ground.toOption.getD []) with
      | [.refs contract [] vs] => fs.all (fun p => (contract.lookup p.1).isSome || (vs.lookup p.1).isSome)
      | _ => false) &&
    fs.all (fun p => validType T (.labels p.2))
private def validBindings (T : SourceTypes.Table) (bs : List Binding) : Bool :=
  (bs.map (·.name)).eraseDups.length == bs.length &&
    bs.all (fun b => !b.name.isEmpty && validType T b.type && validCurrent T b.type b.current)
private def validSpan (p : Span) : Bool := p.1 < p.2
private def validFunction (T : SourceTypes.Table) (f : Function) : Bool :=
  !f.name.isEmpty && validSpan f.namePos && validBindings T f.params &&
  f.params.all (fun b => b.current.isNone) && validType T f.result &&
  (f.entries.map (·.start)).eraseDups.length == f.entries.length &&
  (f.expressions.map (·.pos)).eraseDups.length == f.expressions.length &&
  f.entries.all (fun e => validBindings T e.bindings) &&
  f.expressions.all (fun e => validSpan e.pos && validType T e.type && validCurrent T e.type e.current)

def decode (j : Json) : Except String Document := do
  let d : Document ← decodeStrict j
  if d.sourceSha256.length != 64 || !d.sourceSha256.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    throw "invalid source fingerprint"
  if !validTable d.types then
    throw "invalid source claims: the type table must start with the primitives and refer only to its own labels"
  if !d.functions.all (validFunction d.types) then
    throw "invalid source claims: duplicate identity, span, binding or type labels"
  if (d.functions.map (fun f => (f.name,f.namePos))).eraseDups.length != d.functions.length then
    throw "duplicate function claims"
  return d

private abbrev Sites := List Nat × List Span
private def joinSites (a b : Sites) : Sites := (a.1 ++ b.1,a.2 ++ b.2)
private partial def exprSites : Fragment.Expr → Sites
  | .var p _ | .lit p _ => ([],[p])
  | .shapeTest p _ _ e | .not p e | .cast p _ e | .read p _ e | .lambda p _ _ _ e => joinSites ([],[p]) (exprSites e)
  | .alloc p _ es => es.foldl (fun acc a => joinSites acc (exprSites a)) ([],[p])
  | .withValue p a b _ _ | .write p _ a b | .singletonTest p _ _ _ a b | .equality p _ a b | .coalesce p a b | .logical p _ a b => joinSites ([],[p]) (joinSites (exprSites a) (exprSites b))
  -- An assignment is an expression site, and the name it assigns is not one:
  -- the producer claims the value written, not the location.
  | .index p _ a b | .arith p _ a b | .logicalAssign p _ a b | .elemAt p a b => joinSites ([],[p]) (joinSites (exprSites a) (exprSites b))
  | .arrayLit p es => es.foldl (fun acc a => joinSites acc (exprSites a)) ([],[p])
  | .arrayAssign p targets rhs => targets.foldl (fun acc q => match q.default_ with
      | some d => joinSites acc (exprSites d) | none => acc) (joinSites ([],[p]) (exprSites rhs))
  | .elemWrite p a b c => joinSites ([],[p]) (joinSites (exprSites a) (joinSites (exprSites b) (exprSites c)))
  | .update p _ a none _ => joinSites ([],[p]) (exprSites a)
  | .update p _ a (some r) _ => joinSites ([],[p]) (joinSites (exprSites a) (exprSites r))
  | .indexWrite p _ a b c => joinSites ([],[p]) (joinSites (exprSites a) (joinSites (exprSites b) (exprSites c)))
  | .nullishAssign p _ np e => joinSites ([],[p,np]) (exprSites e)
  | .assign p _ _ e => joinSites ([],[p]) (exprSites e)
  | .atEnv p e => joinSites ([p.1],[]) (exprSites e)
  | .bindWithReceiver p f receiver args | .callWithReceiver p f receiver args => args.foldl (fun acc a => joinSites acc (exprSites a))
      (joinSites ([],[p]) (joinSites (exprSites f) (exprSites receiver)))
  | .call p f args => args.foldl (fun acc a => joinSites acc (exprSites a)) (joinSites ([],[p]) (exprSites f))
  | .done _ => ([],[])
  | .seqBody p a b | .letBody p _ _ a b => joinSites ([p.1],[]) (joinSites (exprSites a) (exprSites b))
  | .ifBody p result a b c => joinSites (if result.isSome then ([p.1],[]) else ([],[p])) (joinSites (exprSites a) (joinSites (exprSites b) (exprSites c)))
private partial def stmtSites : Fragment.Stmt → Sites
  | .brk p | .cont p => ([p.1],[])
  | .ret p e | .effect p e => joinSites ([p.1],[]) (exprSites e)
  -- One entry for the statement; every declarator's initializer is a site.
  | .constants p bs | .mutables p bs => bs.foldl (fun acc b => joinSites acc (exprSites b.init)) ([p.1],[])
  -- The initializer and each default are sites; the pattern's reads are not.
  | .pattern p props init => props.foldl (fun acc q => match q.default_ with
      | some d => joinSites acc (exprSites d) | none => acc) (joinSites ([p.1],[]) (exprSites init))
  | .arrayPattern p elems init => elems.foldl (fun acc q => match q.default_ with
      | some d => joinSites acc (exprSites d) | none => acc) (joinSites ([p.1],[]) (exprSites init))
  | .loop p c body => joinSites ([p.1],[]) (joinSites (exprSites c)
      (body.foldl (fun s st => joinSites s (stmtSites st)) ([],[])))
  | .ite p c a b =>
    joinSites ([p.1],[]) (joinSites (exprSites c)
      ((a ++ b.getD []).foldl (fun s st => joinSites s (stmtSites st)) ([],[])))

def functionSites (f : Fragment.Fn) : List Nat × List Span :=
  f.body.foldl (fun s st => joinSites s (stmtSites st)) ([],[])

private def genericType (T : SourceTypes.Table) : ClaimType → Except String Json
  | .unavailable reason => throw reason
  | .param name => pure (Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj [("a",toJson "param"),("name",toJson name)]])])
  | .scheme .. => throw "nested quantified callable requires scheme checking"
  | .labels A => do
    let rows := PositiveRules.expand (SourceTypes.graph T) A
    -- Semantic top passes through as itself: it permits nothing.
    if rows == [.top] then return Json.mkObj [("top",toJson true),("atoms",toJson ([] : List Json))]
    if rows != [.bool] && rows != [.boolLit true,.boolLit false] && rows != [.boolLit false,.boolLit true] then
      throw "generic claim requires a rigid parameter or boolean"
    return Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj [("a",toJson "boolean")]])]
private def Function.genericClaims (T : SourceTypes.Table) (c : Function) : Except String Fragment.Claims := do
  if c.entries.any (fun e => e.bindings.any (fun b => b.current.isSome)) ||
      c.expressions.any (fun e => e.current.isSome) then throw "generic claims cannot assert current contents"
  return ⟨c.name,c.namePos,← c.params.mapM (fun b => do return (b.name,← genericType T b.type)),
    ← genericType T c.result,
    -- `this` is a claimed binding of every function and no source name.
    ← c.entries.mapM (fun e => do return (e.start,← (e.bindings.filter (·.name != "this")).mapM
      (fun b => do return (b.name,← genericType T b.type)))),
    ← c.expressions.mapM (fun e => do return (e.pos,← genericType T e.type))⟩

inductive FunctionPlan where
  | graph (name : String) (namePos : Span) (request : SourceRequest)
  | generic (name : String) (namePos : Span)

/-- Projection for the graph evidence engine. Unlike the former `Option` plus
`filterMap`, every omitted request is named by the `generic` constructor and
was checked by the direct rigid-parameter checker while building the plan. -/
def FunctionPlan.requests : List FunctionPlan → List SourceRequest
  | [] => []
  | .graph _ _ request :: rest => request :: FunctionPlan.requests rest
  | .generic .. :: rest => FunctionPlan.requests rest

def extractPlans (ast claims : Json) (fileKey : String) : Except String (List FunctionPlan) := do
  let d ← decode claims
  if d.file != fileKey || (← jStr (← jField ast "file")) != fileKey then throw "source claim file identity mismatch"
  if (← jStr (← jField ast "sourceSha256")) != d.sourceSha256 then throw "source claim fingerprint mismatch"
  let aliases ← GenericAlias.decodeAliases ast
  for a in aliases do GenericAlias.admit a
  let decoded ← Fragment.decodeAstWithParams ast
  let decoded ← decoded.mapM fun (f,tps) => do
    return (← GenericAlias.expandFn aliases f,tps)
  let fs := decoded.map Prod.fst
  if fs.isEmpty then throw "no source functions to verify"
  if (fs.map (fun f => (f.name,f.namePos))).eraseDups.length != fs.length then throw "duplicate source function identities"
  if fs.length != d.functions.length then throw "function claim count mismatch"
  decoded.mapM fun (f,tps) => do
    let c ← match d.functions.find? (fun c => c.name == f.name && c.namePos == f.namePos) with
      | some c => pure c
      | none => throw s!"missing claims for '{f.name}'"
    let sites := functionSites f
    if !c.entries.all (fun e => sites.1.contains e.start) ||
        !c.expressions.all (fun e => sites.2.contains e.pos) then
      throw "claim site is not an entry or expression of the named source function"
    if !tps.isEmpty then
      let genericClaims ← c.genericClaims d.types
      match GenericSource.check f tps genericClaims with
      | .ok () => return .generic f.name f.namePos
      | .error reason =>
        throw (directFailure d.types f.namePos "generic-validation" "generic" reason
          (f.params.map (·.name)))
    if c.hasScheme then
      let schemePos ← match Scheme.find f with
        | .ok (some closure) => pure closure.span
        | .ok none => pure f.namePos
        | .error reason =>
          throw (directFailure d.types f.namePos "scheme-validation" "scheme" reason
            (f.params.map (·.name)))
      match Scheme.compile d.types f c with
      | .ok (T, c, overlays) =>
        return .graph f.name f.namePos
          (← extractNormalizedFn T f { c.normalized with schemeArrows := overlays })
      | .error reason =>
        throw (directFailure d.types schemePos "scheme-validation" "scheme" reason
          (f.params.map (·.name)))
    return .graph f.name f.namePos (← extractNormalizedFn d.types f c.normalized)

/-- Graph-only projection for proof fixtures that inspect extracted programs.
The name makes its loss of successfully checked direct-generic plans explicit;
production and checking use `extractPlans`, whose result has exactly one
constructor per decoded source function. -/
def extractGraphRequests (ast claims : Json) (fileKey : String) : Except String (List SourceRequest) := do
  return FunctionPlan.requests (← extractPlans ast claims fileKey)

def checkJson (ast claims : Json) (fileKey : String) (evidence : Json) : Except String Unit := do
  let plans ← extractPlans ast claims fileKey
  let rs := FunctionPlan.requests plans
  let b : Bundle ← decodeStrict evidence
  if checkRequests rs b then return ()
  throw "source evidence does not justify the extracted program and exact claims"

def produceJson (ast claims : Json) (fileKey : String) (fuel : Nat) : Except String Json := do
  let plans ← extractPlans ast claims fileKey
  let rs := FunctionPlan.requests plans
  let es ← rs.mapM fun r => ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length fuel r.obligations
  let cs ← (rs.zip es).mapM fun (r,proofs) => do
    let j ← RequestJson.produceJson (toJson r.toRequest) fuel [] proofs r.sourceMap (some r.searchLabels) r.assertions r.cuts
    decodeResponse r.toRequest j
  let evidence := toJson (Bundle.mk cs es)
  checkJson ast claims fileKey evidence
  return evidence

/-- Acceptance uses the same proved consumer as SKJS-backed extraction. -/
theorem checkJson_checked {ast claims evidence : Json} {fileKey : String}
    (h : checkJson ast claims fileKey evidence = .ok ()) :
    ∃ plans b, extractPlans ast claims fileKey = .ok plans ∧
      decodeStrict evidence = .ok b ∧
      checkRequests (FunctionPlan.requests plans) b = true := by
  unfold checkJson at h
  cases he : extractPlans ast claims fileKey with
  | error e => simp only [he] at h; contradiction
  | ok plans =>
    cases hb : (decodeStrict evidence : Except String Bundle) with
    | error e => simp only [he, hb] at h; contradiction
    | ok b =>
      simp only [he, hb] at h
      change (if checkRequests (FunctionPlan.requests plans) b = true then Except.ok () else
        Except.error "source evidence does not justify the extracted program and exact claims") = .ok () at h
      split at h
      · exact ⟨plans,b,rfl,rfl,by assumption⟩
      · contradiction

#print axioms checkJson_checked
end Verification.ExperimentState.SourceClaimJson
