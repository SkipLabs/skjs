import Verification.Model.Source.SourceExtraction
import Verification.Model.Source.DeclarationGraph
import Verification.Model.Types.TypeSchemes

/-! Strict producer-independent sidecars. A document carries its own type table,
which its labels index; the primitives are its first four rows. The external
parser supplies the source fingerprint; this module checks agreement, not hashing
or the parser's semantic correctness. Saved statuses are not part of the schema. -/
namespace Verification.Model.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules

/-- A rigid name refers to the enclosing source function's binder. It is never
interpreted as a ground graph label or replaced with its upper bound. -/
inductive ClaimType where
  | labels : List Nat → ClaimType
  | union : List ClaimType → ClaimType
  | param : String → ClaimType
  | array : ClaimType → ClaimType
  /-- Binders, receiver, parameters, rest element and result. -/
  | scheme : List (String × Option ClaimType) → ClaimType → List ClaimType → Option ClaimType →
      ClaimType → ClaimType
  | unavailable : String → ClaimType
  deriving Repr, BEq, Inhabited
instance : Coe (List Nat) ClaimType := ⟨ClaimType.labels⟩

private partial def ClaimType.toJson : ClaimType → Json
  | .labels A => Lean.toJson A
  | .union ts => Json.mkObj [("union", Lean.toJson (ts.map ClaimType.toJson))]
  | .array e => Json.mkObj [("array", e.toJson)]
  | .param name => Json.mkObj [("param", Lean.toJson name)]
  | .scheme typeParams receiver params rest result => Json.mkObj [("scheme", Json.mkObj [
      ("typeParams", Lean.toJson (typeParams.map fun p => Json.mkObj [
        ("name", Lean.toJson p.1), ("bound", p.2.map ClaimType.toJson |>.getD Json.null)])),
      ("this", ClaimType.toJson receiver),
      ("params", Lean.toJson (params.map ClaimType.toJson)),
      ("rest", rest.map ClaimType.toJson |>.getD Json.null),
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
    if let .ok _ := j.getObjVal? "union" then
      CellClaims.fieldsExactly j ["union"]
      return .union (← (← jArr j "union").mapM ClaimType.fromJson)
    if let .ok e := j.getObjVal? "array" then
      CellClaims.fieldsExactly j ["array"]
      return .array (← ClaimType.fromJson e)
    if let .ok s := j.getObjVal? "scheme" then
      CellClaims.fieldsExactly j ["scheme"]
      CellClaims.fieldsExactly s ["typeParams", "this", "params", "rest", "result"]
      let typeParams ← (← jArr s "typeParams").mapM fun p => do
        CellClaims.fieldsExactly p ["name", "bound"]
        let name ← jStr (← jField p "name")
        let bound ← jField p "bound"
        let bound ← if bound == .null then pure none else do
          pure (some (← ClaimType.fromJson bound))
        return (name, bound)
      let receiver ← ClaimType.fromJson (← jField s "this")
      let params ← (← jArr s "params").mapM ClaimType.fromJson
      let rest ← jField s "rest"
      let rest ← if rest == .null then pure none else some <$> ClaimType.fromJson rest
      return .scheme typeParams receiver params rest (← ClaimType.fromJson (← jField s "result"))
    let name ← jStr (← jField j "param")
    if j != Json.mkObj [("param", Lean.toJson name)] || name.isEmpty then
      throw "invalid rigid parameter claim"
    return .param name

instance : FromJson ClaimType where
  fromJson? := ClaimType.fromJson
private partial def ClaimType.ground : ClaimType → SourceClaims.Candidate
  | .union ts => do
      let arms ← ts.mapM ClaimType.ground
      return (arms.flatten.eraseDups.mergeSort (· ≤ ·))
  | .labels A => .ok A
  | .array _ => .error "array over a rigid parameter requires scheme checking"
  | .param _ => .error "rigid parameter outside generic function"
  | .scheme .. => .error "quantified callable requires scheme checking"
  | .unavailable reason => .error reason

/-- What a point currently holds, field by field: an object has one location
per named field, so an assertion about its contents names the field it is
about. A point that names no record carries none. -/
abbrev CurrentFields := List (PropKey × List Nat)

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
/-- Interior claims for one closure, one set per signature of its claimed
callable type, in that order. A closure advertising several signatures has one
body and a different obligation at each: the producer states the claims that
body has under each, as scheme compilation states them under each checked
instantiation. -/
structure ArrowRow where
  expressions : List Expression
  entries : List Entry := []
  deriving ToJson, FromJson
structure ArrowClaims where
  pos : Span
  rows : List ArrowRow
  deriving ToJson, FromJson
structure Function where
  name : String
  namePos : Span
  params : List Binding
  result : ClaimType
  entries : List Entry
  expressions : List Expression
  /-- Omitted by a document whose closures each advertise one signature. -/
  arrows : Option (List ArrowClaims) := none
  deriving FromJson

/-- Absence asserts nothing: a document whose closures each advertise one
signature states no per-arrow claims, and no producer writes an empty list. -/
instance : ToJson Function where
  toJson f := Json.mkObj ([("name", toJson f.name), ("namePos", toJson f.namePos),
    ("params", toJson f.params), ("result", toJson f.result),
    ("entries", toJson f.entries), ("expressions", toJson f.expressions)] ++
    (match f.arrows with
     | none | some [] => []
     | some rows => [("arrows", toJson rows)]))
/-- Claims for the module's initialization: the code unit that runs the
file's top-level code. It has no parameters, and completes with `undefined`. -/
structure InitClaims where
  entries : List Entry
  expressions : List Expression
  arrows : Option (List ArrowClaims) := none
  deriving FromJson
instance : ToJson InitClaims where
  toJson i := Json.mkObj ([("entries", toJson i.entries), ("expressions", toJson i.expressions)] ++
    (match i.arrows with
     | none | some [] => []
     | some rows => [("arrows", toJson rows)]))
structure Document where
  file : String
  sourceSha256 : String
  types : SourceTypes.Table
  functions : List Function
  /-- Present exactly when the source has module initialization code. -/
  init : Option InitClaims := none
  deriving FromJson

/-- Absence asserts nothing: a source with no initialization code has no
initialization claims, and no producer writes an empty one. -/
instance : ToJson Document where
  toJson d := Json.mkObj ([("file", toJson d.file), ("sourceSha256", toJson d.sourceSha256),
    ("types", toJson d.types), ("functions", toJson d.functions)] ++
    (match d.init with
     | none => []
     | some i => [("init", toJson i)]))


def Function.normalized (f : Function) : SourceClaims.Function :=
  ⟨f.name,f.namePos,f.params.map (fun b => (b.name,b.type.ground)),f.result.ground,
    f.entries.map (fun e => (e.start,e.bindings.map (fun b => (b.name,b.type.ground)))),
    f.expressions.map (fun e => (e.pos,e.type.ground)),
    f.entries.map (fun e => (e.start,e.bindings.filterMap fun b => b.current.map (b.name,·))),
    f.expressions.filterMap (fun e => e.current.map (e.pos,·)),
    -- Stated by the producer for an overloaded closure, and supplied by scheme
    -- compilation for a quantified one.
    (f.arrows.getD []).map (fun a => (a.pos, a.rows.map (fun row =>
      ⟨row.expressions.map (fun e => (e.pos,e.type.ground)),
       row.entries.map (fun e => (e.start,e.bindings.map (fun b => (b.name,b.type.ground)))),
       row.entries.map (fun e => (e.start,e.bindings.filterMap fun b => b.current.map (b.name,·))),
       row.expressions.filterMap (fun e => e.current.map (e.pos,·)), none⟩)))⟩

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
private partial def ofClaim (T : SourceTypes.Table) (role : String) :
    ClaimType → Except String DirectObligation.Ty
  | .array e => return .array (← ofClaim T role e)
  | .param name => pure (.rigid name)
  | .union _ => throw s!"a union containing rigid types is outside {role}"
  -- A union holding `unknown` is `unknown`: the direct checker's top, as an
  -- annotation of it is.
  | .labels A => pure (if A.any (fun l => T[l]? == some [.top]) then .top else .ground A)
  | .scheme [] rc ps rest r => do
    let receiver ← ofClaim T role rc
    let params ← ps.mapM (ofClaim T role)
    let result ← ofClaim T role r
    match rest with
    | none => return .arrow receiver params result
    | some e => return .variadic receiver params (← ofClaim T role e) result
  | .scheme .. => throw s!"a nested scheme is outside {role}"
  | .unavailable reason => throw reason

/-- The sidecar's claims as direct types, decoded once for the rigid checker.
A generic declaration's claims must all be direct. A function holding a
quantified closure also claims that closure's scheme at its sites; those are
the scheme compiler's concern, not the body checker's, and are left out when
`withinScheme` — the checker never looks a quantified scheme up. -/
private def Function.directClaims (c : Function) (T : SourceTypes.Table)
    (withinScheme : Bool := false) : Except String GenericSource.Claims := do
  if c.entries.any (fun e => e.bindings.any (fun b => b.current.isSome)) ||
      c.expressions.any (fun e => e.current.isSome) then
    throw "generic claims cannot assert current contents"
  let quantified : ClaimType → Bool
    | .scheme (_ :: _) _ _ _ _ => true
    | _ => false
  let ty := ofClaim T "a rigid claim"
  let keep (t : ClaimType) : Bool := !(withinScheme && quantified t)
  return ⟨c.name, c.namePos,
    ← (c.params.filter (keep ·.type)).mapM (fun b => do return (b.name, ← ty b.type)),
    ← (if keep c.result then ty c.result else pure (.ground [])),
    -- `this` is a claimed binding of every function and no source name.
    ← c.entries.mapM (fun e => do return (e.start,
      ← (e.bindings.filter fun b => b.name != "this" && keep b.type).mapM
        (fun b => do return (b.name, ← ty b.type)))),
    ← (c.expressions.filter (keep ·.type)).mapM (fun e => do return (e.pos, ← ty e.type))⟩

private def claimHasScheme : ClaimType → Bool
  | .scheme .. => true
  | _ => false

private def Function.hasScheme (f : Function) : Bool :=
  claimHasScheme f.result || f.params.any (claimHasScheme ·.type) ||
    f.entries.any (fun e => e.bindings.any (claimHasScheme ·.type)) ||
    f.expressions.any (claimHasScheme ·.type)

/-- Direct rigid/scheme checks do not pretend to be ordinary graph sequents,
but their failures use the same mandatory located diagnostic channel. The
viewer consumes this record structurally and derives all prose from it. -/
private def directFailure (T : SourceTypes.Table) (failure : DirectObligation.Located) : String :=
  -- A substituted bound at a call is a subtyping judgment like a generic one,
  -- but it belongs to the scheme it eliminates, and says so.
  let system := if failure.role == .schemeElimination then "scheme" else failure.judgment.system
  let words : DirectObligation.SourceRole → Option String
    | .entryClaim => some "entry claim" | .expressionClaim => some "expression claim"
    | .returnContract => some "return contract" | .bindingAnnotation => some "binding annotation"
    | .storageWrite => some "captured storage write"
    | .callArgument => some "call argument"
    | _ => none
  let message := if failure.role == .schemeElimination
    then s!"quantified call does not satisfy the closure's bound: cannot establish {failure.judgment.render T}"
    else match words failure.role with
      | some role => s!"generic {role} at [{failure.pos.1},{failure.pos.2}): cannot establish {failure.judgment.render T}"
      | none => failure.judgment.message T
  let context := failure.judgment.context.map fun binding => binding.name
  RequestJson.withDiagnostic s!"source direct obligation at [{failure.pos.1},{failure.pos.2}): {message}"
    [("kind",toJson "direct-obligation"),("phase",toJson "request-validation"),
     ("outcome",toJson "not-established"),("id",toJson s!"{system}:{failure.pos.1}"),
     ("sourceMap",toJson (SourceMapEntry.mk failure.pos failure.role.wire none
       (context.map fun name => (Descriptor.mk name none)))),
     ("judgment",failure.judgment.toJson),
     ("fuel",toJson 0),("types",toJson T)]

private def sourceRefusal (T : SourceTypes.Table) (pos : Span)
    (role : DirectObligation.SourceRole) (reason : String) : String :=
  RequestJson.withDiagnostic s!"source refusal at [{pos.1},{pos.2}): {reason}"
    [("kind",toJson "source-refusal"),("phase",toJson "request-validation"),
     ("outcome",toJson "not-established"),("id",toJson s!"refusal:{pos.1}"),
     ("sourceMap",toJson (SourceMapEntry.mk pos role.wire none [])),
     ("reason",toJson reason),("fuel",toJson 0),("types",toJson T)]

namespace Scheme

/-- A direct type in the claim language: the wire form of what the checker
established. Top is the table's `unknown` row. -/
private partial def claimOfTy : DirectObligation.Ty → SourceTypes.Lowering ClaimType
  | .variadic rc ps e r => do
    return .scheme [] (← claimOfTy rc) (← ps.mapM claimOfTy) (some (← claimOfTy e)) (← claimOfTy r)
  | .array e => do return .array (← claimOfTy e)
  | .rigid name => pure (.param name)
  | .ground A => pure (.labels A)
  | .top => do return .labels [← SourceTypes.use .top]
  | .arrow rc ps r => do
    return .scheme [] (← claimOfTy rc) (← ps.mapM claimOfTy) none (← claimOfTy r)

/-- A quantified closure's annotation, in the claim language, by the one
converter every annotation takes. -/
private def claimOfType (names : List String) (j : Json) : SourceTypes.Lowering ClaimType := do
  claimOfTy (← GenericSource.annotationTy names j)

/-- Ground a claim, interning any callable it contains. Only after substitution
does a rigid arrow such as `() => T` have a graph row. -/
private partial def groundIn (T : SourceTypes.Table) :
    ClaimType → Except String (SourceTypes.Table × List Nat)
  | .union ts => do
      let (T, arms) ← ts.foldlM (fun (T, acc) t => do
        let (T, A) ← groundIn T t
        pure (T, acc ++ A)) (T, [])
      pure (T, arms.eraseDups.mergeSort (· ≤ ·))
  | .labels A => pure (T, A)
  | .array e => do
      let (T, E) ← groundIn T e
      let store := PositiveNormalization.Clause.list ⟨[], [], some E, false⟩ []
      let T := SourceTypes.intern T store
      let array := PositiveNormalization.Clause.refs [(CallArguments.arrayStoreField, [SourceTypes.label T store])] [] []
      let T := SourceTypes.intern T array
      pure (T, [SourceTypes.label T array])
  | .scheme [] rc ps rest r => do
      let (T, rc) ← groundIn T rc
      let (T, ps) ← ps.foldlM (fun (T, acc) p => do
        let (T, a) ← groundIn T p
        pure (T, acc ++ [a])) (T, [])
      let (T, r) ← groundIn T r
      let (T, clause) ← match rest with
        | none => pure (T, PositiveNormalization.Clause.arrs [(rc, ps, r)] [])
        | some e => do
          let (T, E) ← groundIn T e
          pure (T, PositiveNormalization.Clause.arrs [] [(rc, ps, E, r)])
      let T := SourceTypes.intern T clause
      pure (T, [SourceTypes.label T clause])
  | .param name => throw s!"still the rigid parameter '{name}'"
  | .scheme .. => throw "a scheme is not a ground type"
  | .unavailable reason => throw reason

private def groundOf (role : String) : ClaimType → Except String (List Nat)
  | .array _ => throw s!"{role} requires grounding an array"
  | .union _ => throw s!"{role} requires grounding a union"
  | .labels A => pure A
  | .param name => throw s!"{role} is still the rigid parameter '{name}'"
  | .scheme .. => throw s!"{role} is a scheme, not a ground type"
  | .unavailable reason => throw reason

/-- Capture-avoiding: a nested scheme's own binders shadow the substitution. -/
private partial def subst (σ : List (String × ClaimType)) : ClaimType → ClaimType
  | .array e => .array (subst σ e)
  | .union ts => .union (ts.map (subst σ))
  | .param name => (σ.lookup name).getD (.param name)
  | .scheme tps rc ps rest r =>
      let inner := σ.filter fun q => !(tps.map Prod.fst).contains q.1
      .scheme (tps.map fun q => (q.1, q.2.map (subst inner))) (subst inner rc) (ps.map (subst inner))
        (rest.map (subst inner)) (subst inner r)
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
  let [(rc, ps, r)] := s.signatures | none
  guard (s.variadic.isEmpty && s.bounds.isEmpty && s.binders == (List.range names.length).map (· + 1))
  return .scheme (names.map (·, none)) (.labels rc) (← ps.mapM rigid) none (← rigid r)

#guard ofScheme ["T"] TypeSchemes.identityScheme
  == some (.scheme [("T", none)] (.labels [2]) [.param "T"] none (.param "T"))

private structure Closure where
  span : Span
  binding : String
  /-- Declared in order; a bound names an earlier binder or `boolean`. -/
  parameters : List DirectObligation.Parameter
  /-- The source parameter and result annotations, as written. -/
  sourceParams : List (String × Json)
  /-- Initialization is part of the source closure, never discard it while
  selecting the universal certificate path. -/
  defaults : List (Nat × Fragment.Expr)
  rest : Option ClaimType
  sourceResult : Json
  /-- An ordinary function's receiver annotation; none for an arrow. -/
  sourceReceiver : Option Json
  /-- The receiver the claim states: the annotation, or top for an arrow, which
  never reads it. -/
  receiver : ClaimType
  params : List ClaimType
  result : ClaimType
  body : Fragment.Expr
  declStart : Nat

/-- One quantified closure per function in this slice. The declared signature
must name the closure's own binders. A bound names an earlier binder or
`boolean`, exactly as for generic declarations. -/
private def find (f : Fragment.Fn) : SourceTypes.Lowering (Option Closure) := do
  let mut found : Option Closure := none
  for s in f.body do
    if let .constants pos bs := s then
      for b in bs do
        if let .lambda lpos receiverAnnot tps ps defaults rest ret body := b.init then
          if !tps.isEmpty then
            if found.isSome then
              throw "this slice checks one quantified closure per function"
            let names := tps.map (·.name)
            if names.eraseDups.length != names.length then throw "duplicate closure binder"
            let parameters ← GenericSource.parametersOf (← get) tps
            let params : List ClaimType ← ps.zipIdx.mapM fun (q,i) => do
              let t ← claimOfType names q.2
              if (defaults.lookup i).isNone then pure t
              else match t with
                | .labels A => pure (.labels ((A ++ [3]).eraseDups |>.mergeSort (· ≤ ·)))
                | _ => pure (.union [t, .labels [3]])
            let (params, element) ← if rest then
              match params.reverse with
              | .array e :: fixed => pure (fixed.reverse, some e)
              | _ => throw "a quantified rest requires a mutable array contract"
              else pure (params, none)
            let r ← claimOfType names ret
            let receiver ← match receiverAnnot with
              | some annot => claimOfType names annot
              | none => claimOfTy .top
            found := some ⟨lpos, b.name, parameters, ps, defaults, element, ret, receiverAnnot,
              receiver, params, r, body, pos.1⟩
  return found

/-- Introduction. The gate every accepted scheme passes, whatever its calls:
the quantified closure is checked as a closure under its own binders, in the
scope its declaration sees, by the same checker as a generic declaration. The
enclosing function's cells are the only names it may assign; each keeps its
fixed contract at every instantiation. Returns the table, grown by any ground
annotation met on the way. -/
private def introduce (T : SourceTypes.Table) (f : Fragment.Fn) (c : Closure) (claims : Function) :
    Except DirectObligation.Failure (SourceTypes.Table × Option GenericCertificate.ClosureCertificate) := do
  let refuse := DirectObligation.Failure.refusal c.span .schemeIntroduction
  let some entry := claims.entries.find? (·.start == c.declStart)
    | throw (refuse "quantified closure declaration has no entry claim")
  -- Captures keep the types they already have; no instantiation may retype them.
  let outer ← entry.bindings.mapM fun b => do
    return (b.name, ← (ofClaim T "a quantified closure's captured scope" b.type).mapError refuse)
  let direct ← (claims.directClaims T (withinScheme := true)).mapError refuse
  let storage := f.body.flatMap fun
    | .mutables _ bs => bs
    | _ => []
  let cells := storage.map (·.name)
  let ctx : GenericSource.Ctx := ⟨c.parameters, direct, cells⟩
  let (_, T) ← (GenericSource.parameterDefaults ctx outer c.span c.sourceParams c.defaults).run T
  let (_, T) ← (GenericSource.closureTy ctx outer c.span c.sourceParams c.sourceResult c.body
    c.sourceReceiver).run T
  let (certificate, T) ← (GenericSource.closureCertificate ctx outer storage c.span
    c.sourceParams c.sourceResult c.body c.defaults c.rest.isSome c.sourceReceiver).run T
  return (T, certificate)

/-- Elimination, then compilation. Each call validates its own substitution;
the arrows are derived from the scheme signature by that substitution, so a
forged instantiation can only name another genuine instance of a scheme that
has already passed the universal gate. -/
private def compile (T : SourceTypes.Table) (f : Fragment.Fn) (claims : Function) :
    Except DirectObligation.Failure (SourceTypes.Table × Function ×
      List (Span × List SourceClaims.Overlay)) := do
  let refuse (pos : Span) (reason : String) : DirectObligation.Failure :=
    .refusal pos .schemeElimination reason
  let (c, T) ← match (find f).run T with
    | .ok (some c, T) => pure (c, T)
    | .ok (none, _) => throw (refuse f.namePos "a scheme claim has no quantified closure in its source")
    | .error reason => throw (refuse f.namePos reason)
  let parameters := c.parameters
  let names := parameters.map (·.name)
  let lowered : SourceTypes.Lowering (List (String × Option ClaimType)) :=
    parameters.mapM fun (q : DirectObligation.Parameter) => do
      return (q.name, ← q.upper.mapM claimOfTy)
  let (binders, T) ← match lowered.run T with
    | .ok r => pure r
    | .error reason => throw (refuse c.span reason)
  let sites := claims.expressions.filterMap fun e => e.instantiate.map ((e.pos, ·))
  if sites.isEmpty then throw (refuse c.span "a quantified closure has no checked instantiation")
  let subs ← sites.mapM fun (pos, inst) => do
    let given := inst.map (·.name)
    if given.eraseDups.length != given.length then
      throw (refuse pos "duplicate type argument")
    if given.length != names.length || given.any (!names.contains ·) then
      throw (refuse pos "type arguments do not instantiate exactly the closure's binders")
    for i in inst do
      let _ ← (groundOf s!"the type argument for '{i.name}'" i.type).mapError (refuse pos)
    let σ := inst.map fun i => (i.name, i.type)
    -- Elimination proves every substituted bound. The obligation is located at
    -- the call, under the closure's declared parameters, so a reversed bound
    -- is shown as the inclusion that failed rather than refused by name.
    for (name, bound) in binders do
      if let some upper := bound then
        let some argument := σ.lookup name | throw (refuse pos s!"no type argument for '{name}'")
        let actual ← (groundOf s!"the type argument for '{name}'" argument).mapError (refuse pos)
        let required ← (groundOf s!"the bound of '{name}'" (subst σ upper)).mapError (refuse pos)
        let actual := DirectObligation.Ty.ground actual
        let required := DirectObligation.Ty.ground required
        unless actual.le required do
          throw (.obligation ⟨pos, .schemeElimination,
            .subtyping parameters [] (.expression pos) actual required⟩)
    pure σ
  let σs := subs.foldl (fun acc σ => if acc.contains σ then acc else acc ++ [σ]) []
  let (T, arrows, variadic) ← σs.foldlM (fun (T, acc, rest) σ => do
    let (T, rc) ← (groundIn T (subst σ c.receiver)).mapError (refuse c.span)
    let (T, ps) ← c.params.foldlM (fun (T, ps) q => do
      let (T, p) ← (groundIn T (subst σ q)).mapError (refuse c.span)
      pure (T, ps ++ [p])) (T, [])
    let (T, r) ← (groundIn T (subst σ c.result)).mapError (refuse c.span)
    match c.rest with
    | none => pure (T, acc ++ [(rc, ps, r)], rest)
    | some e => do
      let (T, E) ← (groundIn T (subst σ e)).mapError (refuse c.span)
      pure (T, acc, rest ++ [(rc, ps, E, r)])) (T, [], [])
  let clause : PositiveNormalization.Clause (List Nat) := .arrs arrows variadic
  let T := SourceTypes.intern T clause
  let arrow := SourceTypes.label T clause
  let expected : ClaimType := .scheme binders c.receiver c.params c.rest c.result
  let inside (p : Span) : Bool := c.span.1 ≤ p.1 && p.2 ≤ c.span.2
  let retype (pos : Span) (t : ClaimType) : Except DirectObligation.Failure ClaimType :=
    match t with
    | .scheme [] _ _ _ _ =>
      if inside pos then pure t
      else throw (refuse pos "a callable over a rigid parameter escapes its closure")
    | .scheme .. =>
      if t == expected then pure (.labels [arrow])
      else throw (refuse pos "quantified claim differs from its source scheme")
    | .param n =>
      if inside pos then pure t
      else throw (refuse pos s!"rigid parameter '{n}' escapes its closure")
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
  let init : SourceTypes.Table × List SourceClaims.Overlay := (T, [])
  let (T, overlays) ← σs.foldlM (fun (T, acc) σ => do
    let (T, overlay) ← interior.foldlM (fun (T, overlay) e => do
      match groundIn T (subst σ e.type) with
      | .ok (T, A) => pure (T, overlay ++ [(e.pos, (.ok A : SourceClaims.Candidate))])
      | .error reason => pure (T, overlay ++ [(e.pos, (.error reason : SourceClaims.Candidate))])) (T, [])
    let (original, T) ← match (c.sourceParams.mapM fun q => claimOfType names q.2).run T with
      | .ok (ps, T) => pure (ps, T)
      | .error reason => throw (refuse c.span reason)
    let (T, initialized) ← original.foldlM (fun (T, acc) q => do
      let (T, A) ← (groundIn T (subst σ q)).mapError (refuse c.span)
      pure (T, acc ++ [A])) (T, [])
    pure (T, acc ++ [({ exprs := overlay, initializedParams := some initialized } : SourceClaims.Overlay)])) init
  return (T, claims, [(c.span, overlays)])

/-- A generic module value reached from a unit (a generic module function,
or a generic imported one): the unit's calls name its instances. Each call's
type arguments must be ground and name exactly its binders, and every bound,
at those arguments, must hold by the graph's certified subtyping. Each instance
is the signature at those arguments, a ground callable; the slot holds them
all as one callable with several signatures. A generic module function is
certified for every admissible instantiation by its own unit, and an imported
one is assumed at its declared type, so each instance, and their conjunction,
holds of the value. Returns the grown table, the slot's type in claim form,
and the spans of the callee reads and of the calls. -/
def moduleInstances (T : SourceTypes.Table) (g : DeclarationGraph.Instantiable)
    (unit : List Fragment.Stmt) (claims : Function) :
    Except DirectObligation.Failure (SourceTypes.Table × Json × List Span × List Span) := do
  let refuse (pos : Span) (reason : String) : DirectObligation.Failure :=
    .refusal pos .schemeElimination reason
  let calls := (unit.flatMap Fragment.Stmt.callees).filter (·.2.2 == g.name)
  let graph (A : List Nat) : Json := Json.mkObj [("top", toJson false),
    ("atoms", toJson (A.map fun l => Json.mkObj [("a", toJson "graph"), ("label", toJson l)]))]
  let sites ← calls.mapM fun (pos, _, _) => do
    let some inst := (claims.expressions.find? (·.pos == pos)).bind (·.instantiate)
      | throw (refuse pos s!"a call to the generic function '{g.name}' needs its type arguments")
    let given := inst.map (·.name)
    if given.eraseDups.length != given.length then throw (refuse pos "duplicate type argument")
    if given.length != g.binders.length || given.any (!g.binders.contains ·) then
      throw (refuse pos s!"type arguments do not instantiate exactly the binders of '{g.name}'")
    let σ ← inst.mapM fun i => do
      let A ← (groundOf s!"the type argument for '{i.name}'" i.type).mapError (refuse pos)
      pure (i.name, A)
    pure (pos, σ)
  let mut T := T
  let mut seen : List (List (String × List Nat)) := []
  let mut instances : List Json := []
  for (pos, σ) in sites do
    if seen.contains σ then continue
    seen := seen ++ [σ]
    let ((callable, bounds), grown) ← ((g.instantiate (σ.map fun (n, A) => (n, graph A))).run T).mapError (refuse pos)
    T := grown
    for (n, bound) in bounds do
      if let some upper := bound then
        let some actual := σ.lookup n | throw (refuse pos s!"no type argument for '{n}'")
        let (required, grown) ← ((Fragment.translate upper).run T).mapError (refuse pos)
        T := grown
        let G := SourceTypes.graph T
        let pool := (actual :: required :: (List.range T.length).map (fun m => [m])).eraseDups
        let proved := match CertificateProducer.subtype G pool actual required with
          | some proof => PositiveCertificates.check G actual required proof
          | none => false
        unless proved do
          throw (.obligation ⟨pos, .schemeElimination,
            .subtyping [] [] (.expression pos) (.ground actual) (.ground required)⟩)
    let some atom := (callable.getObjVal? "atoms").toOption.bind (fun a => (a.getArr?.toOption.bind (·[0]?)))
      | throw (refuse pos s!"'{g.name}' is not one callable")
    instances := instances ++ [atom]
  let some first := instances.head? | throw (refuse g.pos s!"'{g.name}' has no call to instantiate")
  let callable := if instances.length == 1 then first else first.setObjVal! "and" (toJson instances.tail)
  return (T, Json.mkObj [("top", toJson false), ("atoms", toJson [callable])],
    calls.map (·.2.1), calls.map (·.1))

end Scheme


/-- The table starts with the primitives and refers only to its own labels. -/
private def validTable (T : SourceTypes.Table) : Bool :=
  SourceTypes.initial.isPrefixOf T && (T.flatMap id |>.flatMap clauseTypes).all (validTy T.length)
private partial def validType (T : SourceTypes.Table) : ClaimType → Bool
  | .union ts => !ts.isEmpty && ts.all (validType T)
  | .array e => validType T e
  | .param name => !name.isEmpty
  | .scheme typeParams receiver params rest result =>
      -- With no binders of its own this is a callable that mentions an
      -- enclosing rigid parameter, such as a returned `() => T`.
      (typeParams.map Prod.fst).eraseDups.length == typeParams.length &&
      typeParams.all (fun p => !p.1.isEmpty && p.2.all (validType T)) &&
      validType T receiver && params.all (validType T) && rest.all (validType T) &&
      validType T result
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
private def validInterior (T : SourceTypes.Table) (entries : List Entry)
    (expressions : List Expression) : Bool :=
  (entries.map (·.start)).eraseDups.length == entries.length &&
  (expressions.map (·.pos)).eraseDups.length == expressions.length &&
  entries.all (fun e => validBindings T e.bindings) &&
  expressions.all (fun e => validSpan e.pos && validType T e.type && validCurrent T e.type e.current)
private def validFunction (T : SourceTypes.Table) (f : Function) : Bool :=
  !f.name.isEmpty && validSpan f.namePos && validBindings T f.params &&
  f.params.all (fun b => b.current.isNone) && validType T f.result &&
  validInterior T f.entries f.expressions &&
  let arrows := f.arrows.getD []
  (arrows.map (·.pos)).eraseDups.length == arrows.length &&
  arrows.all (fun a => validSpan a.pos && !a.rows.isEmpty && a.rows.all (fun row =>
    validInterior T row.entries row.expressions &&
    -- These are ground overload rows. Quantified eliminations are checked by
    -- the scheme gate, never silently discarded during ground normalization.
    row.expressions.all (fun e => e.instantiate.isNone)))

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
  if let some i := d.init then
    if !validInterior d.types i.entries i.expressions then
      throw "invalid source claims: duplicate identity, span, binding or type labels"
  return d

private abbrev Sites := List Nat × List Span × List Span
private def joinSites (a b : Sites) : Sites := (a.1 ++ b.1,a.2.1 ++ b.2.1,a.2.2 ++ b.2.2)
private partial def exprSites : Fragment.Expr → Sites
  | .var p _ | .lit p _ => ([],[p],[])
  -- A defaulted parameter's expression is an ordinary source expression, so it
  -- is a claim site like any other; the parameter name is not one.
  | .lambda p _ _ _ defaults _ _ e =>
    defaults.attach.foldl (fun acc ⟨d,_⟩ => joinSites acc (exprSites d.2))
      (joinSites ([],[p],[p]) (exprSites e))
  | .shapeTest p _ _ e | .not p e | .cast p _ e | .read p _ e => joinSites ([],[p],[]) (exprSites e)
  | .alloc p _ es => es.foldl (fun acc a => joinSites acc (exprSites a)) ([],[p],[])
  | .withValue p a b _ _ | .write p _ a b | .singletonTest p _ _ _ a b | .equality p _ a b | .coalesce p a b | .logical p _ a b => joinSites ([],[p],[]) (joinSites (exprSites a) (exprSites b))
  -- An assignment is an expression site, and the name it assigns is not one:
  -- the producer claims the value written, not the location.
  | .index p _ a b | .arith p _ a b | .logicalAssign p _ a b | .elemAt p a b => joinSites ([],[p],[]) (joinSites (exprSites a) (exprSites b))
  | .arrayLit p es => es.foldl (fun acc a => joinSites acc (exprSites a)) ([],[p],[])
  | .arrayAssign p targets rhs => targets.foldl (fun acc q => match q.default_ with
      | some d => joinSites acc (exprSites d) | none => acc) (joinSites ([],[p],[]) (exprSites rhs))
  | .elemWrite p a b c => joinSites ([],[p],[]) (joinSites (exprSites a) (joinSites (exprSites b) (exprSites c)))
  | .update p _ a none _ => joinSites ([],[p],[]) (exprSites a)
  | .update p _ a (some r) _ => joinSites ([],[p],[]) (joinSites (exprSites a) (exprSites r))
  | .indexWrite p _ a b c => joinSites ([],[p],[]) (joinSites (exprSites a) (joinSites (exprSites b) (exprSites c)))
  | .nullishAssign p _ np e => joinSites ([],[p,np],[]) (exprSites e)
  | .assign p _ _ e => joinSites ([],[p],[]) (exprSites e)
  | .atEnv p e => joinSites ([p.1],[],[]) (exprSites e)
  | .bindWithReceiver p f receiver args | .callWithReceiver p f receiver args => args.foldl (fun acc a => joinSites acc (exprSites a))
      (joinSites ([],[p],[]) (joinSites (exprSites f) (exprSites receiver)))
  | .call p f args _ | .invoke p f args _ => args.foldl (fun acc a => joinSites acc (exprSites a)) (joinSites ([],[p],[]) (exprSites f))
  -- A class value is one expression; its constructor's body has its own sites.
  | .ctor p (.lambda _ _ _ _ _ _ _ e) => joinSites ([],[p],[]) (exprSites e)
  | .ctor p _ => ([],[p],[])
  | .construct p f args => args.foldl (fun acc a => joinSites acc (exprSites a)) (joinSites ([],[p],[]) (exprSites f))
  | .applyWithReceiver p f receiver list =>
    joinSites ([],[p],[]) (joinSites (exprSites f) (joinSites (exprSites receiver)
      ((list.map exprSites).getD ([],[],[]))))
  | .done _ => ([],[],[])
  | .seqBody p a b | .letBody p _ _ a b => joinSites ([p.1],[],[]) (joinSites (exprSites a) (exprSites b))
  | .ifBody p result a b c => joinSites (if result.isSome then ([p.1],[],[]) else ([],[p],[])) (joinSites (exprSites a) (joinSites (exprSites b) (exprSites c)))
private partial def stmtSites : Fragment.Stmt → Sites
  | .brk p | .cont p => ([p.1],[],[])
  | .ret p e | .effect p e => joinSites ([p.1],[],[]) (exprSites e)
  -- One entry for the statement; every declarator's initializer is a site.
  | .constants p bs | .mutables p bs => bs.foldl (fun acc b => joinSites acc (exprSites b.init)) ([p.1],[],[])
  -- The initializer and each default are sites; the pattern's reads are not.
  | .pattern p props init => props.foldl (fun acc q => match q.default_ with
      | some d => joinSites acc (exprSites d) | none => acc) (joinSites ([p.1],[],[]) (exprSites init))
  | .arrayPattern p elems init => elems.foldl (fun acc q => match q.default_ with
      | some d => joinSites acc (exprSites d) | none => acc) (joinSites ([p.1],[],[]) (exprSites init))
  | .loop p c body => joinSites ([p.1],[],[]) (joinSites (exprSites c)
      (body.foldl (fun s st => joinSites s (stmtSites st)) ([],[],[])))
  | .ite p c a b =>
    joinSites ([p.1],[],[]) (joinSites (exprSites c)
      ((a ++ b.getD []).foldl (fun s st => joinSites s (stmtSites st)) ([],[],[])))

private def allFunctionSites (f : Fragment.Fn) : Sites :=
  f.body.foldl (fun s st => joinSites s (stmtSites st)) ([],[],[])

def functionSites (f : Fragment.Fn) : List Nat × List Span :=
  let sites := allFunctionSites f
  (sites.1, sites.2.1)

inductive FunctionPlan where
  | graph (name : String) (namePos : Span) (request : SourceRequest)
  | scheme (name : String) (namePos : Span) (request : SourceRequest)
      (types : SourceTypes.Table) (certificate : Option GenericCertificate.ClosureCertificate)
  | generic (name : String) (namePos : Span) (types : SourceTypes.Table)
      (certificate : GenericCertificate.ClosureCertificate)

/-- A plan admitted by the top-level verified outcome. Graph evidence is
consumed separately. Generic and scheme plans store the successful checks of
their direct-body and universal-invocation certificates. Adding a source-plan
variant cannot silently enter this exhaustive boundary through a projection. -/
inductive CertifiedPlan where
  | graph (name : String) (namePos : Span) (request : SourceRequest)
  | scheme (name : String) (namePos : Span) (request : SourceRequest)
      (types : SourceTypes.Table) (certificate : GenericCertificate.ClosureCertificate)
      (term : Tm) (checked : certificate.check = some term)
      (primitives : GenericCertificate.Primitives (SourceTypes.graph types))
  | generic (name : String) (namePos : Span) (types : SourceTypes.Table)
      (certificate : GenericCertificate.ClosureCertificate) (term : Tm)
      (checked : certificate.check = some term)
      (primitives : GenericCertificate.Primitives (SourceTypes.graph types))

def CertifiedPlan.requests : List CertifiedPlan → List SourceRequest
  | [] => []
  | .graph _ _ request :: rest => request :: CertifiedPlan.requests rest
  | .scheme _ _ request .. :: rest => request :: CertifiedPlan.requests rest
  | .generic .. :: rest => CertifiedPlan.requests rest

/-- Semantic obligations beyond the graph execution, by plan variant. Keep this
match exhaustive so extending the accepted language also requires deciding its
universal guarantee in the headline theorem. Graph plans need no extra premise. -/
def CertifiedPlan.UniversalSafety : CertifiedPlan → Prop
  | .graph .. => True
  | .generic _ _ types certificate .. => certificate.Safe (SourceTypes.graph types)
  | .scheme _ _ _ types certificate .. => certificate.Safe (SourceTypes.graph types)

/-- Graph projection for search and inspection. This is intentionally not the
acceptance boundary: a scheme has useful ground graph evidence while its
universal certificate is still missing. -/
def FunctionPlan.requests : List FunctionPlan → List SourceRequest
  | [] => []
  | .graph _ _ request :: rest => request :: FunctionPlan.requests rest
  | .scheme _ _ request .. :: rest => request :: FunctionPlan.requests rest
  | .generic .. :: rest => FunctionPlan.requests rest

/-- The table's first four rows are the primitives. Every decoded table has
them; a certificate's literal types name them. -/
def primitiveRows (T : SourceTypes.Table) : Prop :=
  T[0]? = some [.nul] ∧ T[1]? = some [.boolLit true] ∧
    T[2]? = some [.boolLit false] ∧ T[3]? = some [.undef]

instance (T : SourceTypes.Table) : Decidable (primitiveRows T) := by
  unfold primitiveRows; infer_instance

theorem primitives_of_rows {T : SourceTypes.Table} (h : primitiveRows T) :
    GenericCertificate.Primitives (SourceTypes.graph T) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact ⟨by simp [SourceTypes.graph, h0], by simp [SourceTypes.graph, h1],
    by simp [SourceTypes.graph, h2], by simp [SourceTypes.graph, h3]⟩

/-- The sole conversion into the verified-plan type. Missing semantic
certificates are ordinary located source limitations. Exhaustive matching makes
a new `FunctionPlan` constructor a compile error here. -/
def FunctionPlan.certify : FunctionPlan → Except String CertifiedPlan
  | .graph name pos request => pure (.graph name pos request)
  | .scheme _ pos _ types none => throw (sourceRefusal types pos .schemeIntroduction
      "quantified callable has no universal semantic certificate")
  | .scheme name pos request types (some certificate) => match h : certificate.check with
      | some term =>
        if hp : primitiveRows types then
          pure (.scheme name pos request types certificate term h (primitives_of_rows hp))
        else throw (sourceRefusal types pos .schemeIntroduction "type table lacks the primitive rows")
      | none => throw (sourceRefusal types pos .schemeIntroduction
          "quantified callable semantic certificate is invalid")
  | .generic name pos types certificate => match h : certificate.check with
      | some term =>
        if hp : primitiveRows types then
          pure (.generic name pos types certificate term h (primitives_of_rows hp))
        else throw (sourceRefusal types pos .genericValidation "type table lacks the primitive rows")
      | none => throw (sourceRefusal types pos .genericValidation
          "generic semantic certificate is invalid")

def certifyPlans (plans : List FunctionPlan) : Except String (List CertifiedPlan) :=
  plans.mapM FunctionPlan.certify

/-- A module constant holds no value until its declaration runs. Walking the
top-level code in order, a step may reach a module function, directly or
through the functions that one mentions, only when every module constant those
functions mention already holds its value. Mentions over-approximate calls, so
this refuses some safe orders and admits no unsafe one. -/
private def checkInitializationOrder (T : SourceTypes.Table)
    (fns : List (Fragment.Fn × List Fragment.TypeParam)) (init : List Fragment.Stmt) :
    Except String Unit := do
  let constants := init.flatMap fun
    | .constants _ bs => bs.map (·.name)
    | _ => []
  let bodies := fns.map fun (g, _) => (g.name, g.body.flatMap stmtNames)
  let isFunction (n : String) := bodies.any (·.1 == n)
  let reach (start : List String) : List String := Id.run do
    let mut seen := start.filter isFunction |>.eraseDups
    for _ in List.range (bodies.length + 1) do
      let next := seen.flatMap (fun g => (bodies.lookup g).getD []) |>.filter isFunction
      seen := (seen ++ next).eraseDups
    return seen
  let mut ready : List String := []
  for s in init do
    let reached := reach (stmtNames s)
    let read := reached.flatMap (fun g => (bodies.lookup g).getD []) |>.filter constants.contains
    if let some c := read.find? (fun c => !ready.contains c) then
      throw (sourceRefusal T s.pos .initializationOrder
        s!"a module function this step reaches reads '{c}' before its declaration runs")
    if let .constants _ bs := s then ready := ready ++ bs.map (·.name)

/-- `only` selects one function of the file, named with its position: the
others remain its module, reachable at their signatures, and need no claims. -/
def extractPlans (ast claims : Json) (fileKey : String) (only : Option (String × Span) := none) :
    Except String (List FunctionPlan) := do
  let d ← decode claims
  if d.file != fileKey || (← jStr (← jField ast "file")) != fileKey then throw "source claim file identity mismatch"
  if (← jStr (← jField ast "sourceSha256")) != d.sourceSha256 then throw "source claim fingerprint mismatch"
  -- Every declaration application in the source becomes a graph row, or, over
  -- a rigid binder, the claim type of its expanded source equation.
  let (ast, types, imported, generics) ← DeclarationGraph.prepare ast d.types
  let d := { d with types }
  if !validTable d.types then throw "declaration graph has an invalid type reference"
  let all ← Fragment.decodeAstWithParams ast
  let fs := all.map Prod.fst
  if fs.isEmpty then throw "no source functions to verify"
  if (fs.map (fun f => (f.name,f.namePos))).eraseDups.length != fs.length then throw "duplicate source function identities"
  let init ← Fragment.decodeInit ast
  -- A body reaches the file's other ordinary functions at their annotated
  -- signatures, and a function also reaches the module's constants at their
  -- annotations; each of those is established by its own unit.
  -- Imported values join them at the types their declarations state.
  let moduleFunctions : List SourceExtraction.ModuleValue :=
    (all.filterMap fun (g, tps) => if tps.isEmpty then some (g.name, g.namePos, moduleArrow g) else none) ++
    imported.map fun (name, span, ty) => (name, span, .ok ty)
  let moduleConstants : List SourceExtraction.ModuleValue := init.flatMap fun
    | .constants _ bs => bs.map fun b => (b.name, b.namePos, match b.annot with
        | some ty => .ok ty
        | none => .error s!"module constant '{b.name}' is read by a function, so it needs an annotation")
    | _ => []
  -- The initialization unit: the top-level code, as a body with no
  -- parameters that completes with `undefined`.
  let initUnit : List (Fragment.Fn × List Fragment.TypeParam × Function) ← match init, d.init with
    | [], none => pure []
    | [], some _ => throw "module initialization claims for a source without initialization code"
    | _ :: _, none => throw "missing claims for the module initialization"
    | first :: _, some c =>
      let span := (first.pos.1, (init.getLast?.map (·.pos.2)).getD first.pos.2)
      let undefinedType := Json.mkObj [("top", toJson false),
        ("atoms", toJson [Json.mkObj [("a", toJson "undefined")]])]
      pure [(⟨"", span, [], undefinedType, init⟩, [],
        ⟨"", span, [], .labels [3], c.entries, c.expressions, c.arrows⟩)]
  let decoded := match only with
    | none => all
    | some (name, pos) => all.filter fun (f, _) => f.name == name && f.namePos == pos
  let initUnit := match only with
    | none => initUnit
    | some (name, pos) => initUnit.filter fun (f, _, _) => f.name == name && f.namePos == pos
  if only.isSome && decoded.length + initUnit.length != 1 then
    throw "the selected function is not in the source"
  -- Initialization order is the initialization unit's own obligation.
  if !initUnit.isEmpty then checkInitializationOrder d.types all init
  if decoded.length != d.functions.length then throw "function claim count mismatch"
  let units := decoded.map (fun (f, tps) => (f, tps, none)) ++
    initUnit.map (fun (f, tps, c) => (f, tps, some c))
  units.mapM fun (f,tps,initClaims) => do
    let module := if initClaims.isSome then moduleFunctions else moduleFunctions ++ moduleConstants
    let mut c ← match initClaims with
      | some c => pure c
      | none => match d.functions.find? (fun c => c.name == f.name && c.namePos == f.namePos) with
        | some c => pure c
        | none => throw s!"missing claims for '{f.name}'"
    -- A generic module function this unit calls: its slot holds the instances
    -- the calls name, and those reads and calls are claimed at them.
    let mut module := module
    let mut d := d
    if tps.isEmpty then
      for g in generics do
        if (f.body.flatMap Fragment.Stmt.callees).any (·.2.2 == g.name) then
          match Scheme.moduleInstances d.types g f.body c with
          | .ok (T, slot, reads, calls) =>
            d := { d with types := T }
            -- The callee reads are claimed at the slot's type, which the
            -- source fixes; the producer's reading of them is not needed.
            let (A, T) ← match (Fragment.translate slot).run d.types with
              | .ok r => pure r
              | .error reason => throw (sourceRefusal d.types g.pos .schemeElimination reason)
            d := { d with types := T }
            module := module ++ [(g.name, g.pos, .ok slot)]
            c := { c with expressions := c.expressions.map fun e =>
              if reads.contains e.pos then { e with type := .labels A }
              else if calls.contains e.pos then { e with instantiate := none } else e }
          | .error (.obligation failure) => throw (directFailure d.types failure)
          | .error (.refusal pos role reason) => throw (sourceRefusal d.types pos role reason)
    let sites := functionSites f
    if !c.entries.all (fun e => sites.1.contains e.start) ||
        !c.expressions.all (fun e => sites.2.contains e.pos) then
      throw "claim site is not an entry or expression of the named source function"
    let closures := (allFunctionSites f).2.2
    for a in c.arrows.getD [] do
      if !closures.contains a.pos then throw "per-arrow claims must name a source closure"
      for row in a.rows do
        if !row.entries.all (fun e => sites.1.contains e.start && a.pos.1 ≤ e.start && e.start < a.pos.2) ||
            !row.expressions.all (fun e => sites.2.contains e.pos && a.pos != e.pos &&
              a.pos.1 ≤ e.pos.1 && e.pos.2 ≤ a.pos.2) then
          throw "per-arrow claim site is outside its source closure"
    if (!tps.isEmpty || c.hasScheme) && !(c.arrows.getD []).isEmpty then
      throw "per-arrow source claims are for ground closures, not quantified schemes"
    if !tps.isEmpty then
      let direct ← match c.directClaims d.types with
        | .ok claims => pure claims
        | .error reason =>
          throw (sourceRefusal d.types f.namePos .genericValidation reason)
      match (GenericSource.check f tps direct).run d.types with
      | .ok (certificate, types) => return .generic f.name f.namePos types certificate
      | .error (.obligation failure) => throw (directFailure d.types failure)
      | .error (.refusal pos role reason) => throw (sourceRefusal d.types pos role reason)
    if c.hasScheme then
      let (closure, T) ← match (Scheme.find f).run d.types with
        | .ok (some closure, T) => pure (closure, T)
        | .ok (none, _) => throw (sourceRefusal d.types f.namePos .schemeIntroduction
            "a scheme claim has no quantified closure in its source")
        | .error reason =>
          throw (sourceRefusal d.types f.namePos .schemeIntroduction reason)
      let (T, certificate) ← match Scheme.introduce T f closure c with
        | .error (.obligation failure) => throw (directFailure d.types failure)
        | .error (.refusal pos role reason) => throw (sourceRefusal d.types pos role reason)
        | .ok result => pure result
      match Scheme.compile T f c with
      | .ok (T, compiled, overlays) =>
        return .scheme f.name f.namePos
          (← extractNormalizedFn T f { compiled.normalized with arrowClaims := overlays } module) T certificate
      | .error (.obligation failure) => throw (directFailure d.types failure)
      | .error (.refusal pos role reason) => throw (sourceRefusal d.types pos role reason)
    return .graph f.name f.namePos (← extractNormalizedFn d.types f c.normalized module)

/-- Graph-only projection for proof fixtures that inspect extracted programs. -/
def extractGraphRequests (ast claims : Json) (fileKey : String) : Except String (List SourceRequest) := do
  return FunctionPlan.requests (← extractPlans ast claims fileKey)

def checkJson (ast claims : Json) (fileKey : String) (evidence : Json)
    (only : Option (String × Span) := none) : Except String Unit := do
  let plans ← extractPlans ast claims fileKey only
  let certified ← certifyPlans plans
  let rs := CertifiedPlan.requests certified
  let b : Bundle ← decodeStrict evidence
  if checkRequests rs b then return ()
  throw "source evidence does not justify the extracted program and exact claims"

def produceJson (ast claims : Json) (fileKey : String) (fuel : Nat)
    (only : Option (String × Span) := none) : Except String Json := do
  let plans ← extractPlans ast claims fileKey only
  let rs := FunctionPlan.requests plans
  let es ← rs.mapM fun r => ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length fuel r.obligations
  let cs ← (rs.zip es).mapM fun (r,proofs) => do
    let j ← RequestJson.produceJson (toJson r.toRequest) fuel [] proofs r.sourceMap (some r.searchLabels) r.assertions r.cuts
    decodeResponse r.toRequest j
  let evidence := toJson (Bundle.mk cs es)
  -- Search may expose the graph consequences of an uncertified scheme. It
  -- does not turn those consequences into top-level semantic acceptance.
  let b : Bundle ← decodeStrict evidence
  if !checkRequests rs b then
    throw "source evidence does not justify the extracted graph requests"
  return evidence

/-- Every extracted plan crosses the exhaustive certification boundary. Graph
requests prove the enclosing execution safe; direct generic and scheme plans
add their universal semantic guarantees, independently of observed calls. -/
theorem checkJson_safe {ast claims evidence : Json} {fileKey : String}
    {only : Option (String × Span)}
    (h : checkJson ast claims fileKey evidence only = .ok ()) :
    ∃ plans certified b, extractPlans ast claims fileKey only = .ok plans ∧
      certifyPlans plans = .ok certified ∧
      decodeStrict evidence = .ok b ∧
      checkRequests (CertifiedPlan.requests certified) b = true ∧
      (∀ r c, (r,c) ∈ (CertifiedPlan.requests certified).zip b.functions →
        ∀ n W heap ρ, EnvOk (RequestJson.graph r.toRequest) r.inputs ρ n W →
          WorldAdm W → HeapOk n W heap →
          SafeGraph r.program (meaning (RequestJson.graph r.toRequest) r.result)
            n W heap (.at r.start ρ)) ∧
      ∀ plan ∈ certified, plan.UniversalSafety := by
  unfold checkJson at h
  cases he : extractPlans ast claims fileKey only with
  | error e =>
    rw [he] at h
    contradiction
  | ok plans =>
    rw [he] at h
    simp only [Bind.bind, Except.bind] at h
    cases hc : certifyPlans plans with
    | error e =>
      rw [hc] at h
      contradiction
    | ok certified =>
      rw [hc] at h
      cases hb : (decodeStrict evidence : Except String Bundle) with
      | error e =>
        rw [hb] at h
        contradiction
      | ok b =>
        rw [hb] at h
        by_cases hx : checkRequests (CertifiedPlan.requests certified) b = true
        · refine ⟨plans,certified,b,rfl,hc,rfl,hx,?_,?_⟩
          intro r c hm n W heap ρ he hw hh
          exact checkRequests_safe hx hm n W heap ρ he hw hh
          intro plan _
          cases plan with
          | graph => trivial
          | generic _ _ _ certificate _ checked primitives =>
            exact GenericCertificate.ClosureCertificate.check_safe primitives checked
          | scheme _ _ _ _ certificate _ checked primitives =>
            exact GenericCertificate.ClosureCertificate.check_safe primitives checked
        · simp [hx] at h

#print axioms checkJson_safe
end Verification.Model.SourceClaimJson
