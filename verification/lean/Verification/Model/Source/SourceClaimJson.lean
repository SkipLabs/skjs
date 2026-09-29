import Verification.Model.Source.SourceExtraction
import Verification.Model.Source.DeclarationGraph

/-! Strict producer-independent sidecars. A document carries its own type table,
which its row labels index, and label trees name the rows only the verifier
builds (`Label`); the primitives are the table's first four rows. The external
parser supplies the source fingerprint; this module checks agreement, not hashing
or the parser's semantic correctness. Saved statuses are not part of the schema. -/
namespace Verification.Model.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction ControlFlow PositiveGraphs PositiveRules LabelStore

/-- A rigid name refers to the enclosing source function's binder. It is never
interpreted as a ground graph label or replaced with its upper bound. -/
inductive ClaimType (ι : Type) where
  | labels : List ι → ClaimType ι
  | union : List (ClaimType ι) → ClaimType ι
  | param : String → ClaimType ι
  | array : ClaimType ι → ClaimType ι
  /-- Binders, receiver, parameters, rest element and result. -/
  | scheme : List (String × Option (ClaimType ι)) → ClaimType ι → List (ClaimType ι) → Option (ClaimType ι) →
      ClaimType ι → CallEffects.Effect → ClaimType ι
  | unavailable : String → ClaimType ι
  deriving Repr, BEq, Inhabited
instance : Coe (List ι) (ClaimType ι) := ⟨ClaimType.labels⟩

private partial def ClaimType.toJson [ToJson ι] : ClaimType ι → Json
  | .labels A => Lean.toJson A
  | .union ts => Json.mkObj [("union", Lean.toJson (ts.map ClaimType.toJson))]
  | .array e => Json.mkObj [("array", e.toJson)]
  | .param name => Json.mkObj [("param", Lean.toJson name)]
  | .scheme typeParams receiver params rest result effect => Json.mkObj [("scheme", Json.mkObj [
      ("typeParams", Lean.toJson (typeParams.map fun p => Json.mkObj [
        ("name", Lean.toJson p.1), ("bound", p.2.map ClaimType.toJson |>.getD Json.null)])),
      ("this", ClaimType.toJson receiver),
      ("params", Lean.toJson (params.map ClaimType.toJson)),
      ("rest", rest.map ClaimType.toJson |>.getD Json.null),
      ("result", ClaimType.toJson result), ("effect", Lean.toJson effect)])]
  | .unavailable reason => Json.mkObj [("unavailable", Lean.toJson reason)]

instance [ToJson ι] : ToJson (ClaimType ι) where
  toJson := ClaimType.toJson

private partial def ClaimType.fromJson [FromJson ι] (j : Json) : Except String (ClaimType ι) :=
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
      CellClaims.fieldsExactly s ["typeParams", "this", "params", "rest", "result", "effect"]
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
        (← Lean.fromJson? (← jField s "effect"))
    let name ← jStr (← jField j "param")
    if j != Json.mkObj [("param", Lean.toJson name)] || name.isEmpty then
      throw "invalid rigid parameter claim"
    return .param name

instance [FromJson ι] : FromJson (ClaimType ι) where
  fromJson? := ClaimType.fromJson
private partial def ClaimType.ground [Labels ι] : ClaimType ι → Except String (Ty ι)
  | .union ts => do
      let arms ← ts.mapM ClaimType.ground
      return (arms.flatten.eraseDups.mergeSort Labels.le)
  | .labels A => .ok A
  | .array _ => .error "array over a rigid parameter requires scheme checking"
  | .param _ => .error "rigid parameter outside generic function"
  | .scheme .. => .error "quantified callable requires scheme checking"
  | .unavailable reason => .error reason

/-- What a point currently holds, field by field: an object has one location
per named field, so an assertion about its contents names the field it is
about. A point that names no record carries none. -/
abbrev CurrentFields (ι : Type) := List (PropKey × List ι)

structure Binding (ι : Type) where
  name : String
  type : ClaimType ι
  current : Option (CurrentFields ι) := none
  deriving ToJson, FromJson
structure Entry (ι : Type) where
  start : Nat
  bindings : List (Binding ι)
  deriving ToJson, FromJson
/-- The type arguments one call supplies for a scheme's binders. It is the
producer's proposed elimination, re-checked here; it is never itself evidence. -/
structure Instantiation (ι : Type) where
  name : String
  type : ClaimType ι
  deriving ToJson, FromJson, BEq

structure Expression (ι : Type) where
  pos : Span
  type : ClaimType ι
  current : Option (CurrentFields ι) := none
  instantiate : Option (List (Instantiation ι)) := none
  deriving FromJson

/-- `current` is required and explicitly `null`, because silence about a
record's contents is itself an assertion. Absence of `instantiate` asserts
nothing: the site simply calls no quantified callable, so it is omitted rather
than stated, and no producer has to write it at every expression. -/
instance [ToJson ι] : ToJson (Expression ι) where
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
structure ArrowRow (ι : Type) where
  expressions : List (Expression ι)
  entries : List (Entry ι) := []
  deriving ToJson, FromJson
structure ArrowClaims (ι : Type) where
  pos : Span
  rows : List (ArrowRow ι)
  deriving ToJson, FromJson
structure Function (ι : Type) where
  name : String
  namePos : Span
  params : List (Binding ι)
  result : ClaimType ι
  entries : List (Entry ι)
  expressions : List (Expression ι)
  /-- Omitted by a document whose closures each advertise one signature. -/
  arrows : Option (List (ArrowClaims ι)) := none
  deriving FromJson

/-- Absence asserts nothing: a document whose closures each advertise one
signature states no per-arrow claims, and no producer writes an empty list. -/
instance [ToJson ι] : ToJson (Function ι) where
  toJson f := Json.mkObj ([("name", toJson f.name), ("namePos", toJson f.namePos),
    ("params", toJson f.params), ("result", toJson f.result),
    ("entries", toJson f.entries), ("expressions", toJson f.expressions)] ++
    (match f.arrows with
     | none | some [] => []
     | some rows => [("arrows", toJson rows)]))
/-- Claims for the module's initialization: the code unit that runs the
file's top-level code. It has no parameters, and completes with `undefined`. -/
structure InitClaims (ι : Type) where
  entries : List (Entry ι)
  expressions : List (Expression ι)
  arrows : Option (List (ArrowClaims ι)) := none
  deriving FromJson
instance [ToJson ι] : ToJson (InitClaims ι) where
  toJson i := Json.mkObj ([("entries", toJson i.entries), ("expressions", toJson i.expressions)] ++
    (match i.arrows with
     | none | some [] => []
     | some rows => [("arrows", toJson rows)]))
/-- A document with every label a row: the wire's once `FiniteLayout.finite`
has given its label trees rows, or one whose producer names only rows. -/
structure Document (σ ι : Type) where
  file : String
  sourceSha256 : String
  types : σ
  functions : List (Function ι)
  /-- Present exactly when the source has module initialization code. -/
  init : Option (InitClaims ι) := none
  deriving FromJson

/-- Absence asserts nothing: a source with no initialization code has no
initialization claims, and no producer writes an empty one. -/
instance [ToJson σ] [ToJson ι] : ToJson (Document σ ι) where
  toJson d := Json.mkObj ([("file", toJson d.file), ("sourceSha256", toJson d.sourceSha256),
    ("types", toJson d.types), ("functions", toJson d.functions)] ++
    (match d.init with
     | none => []
     | some i => [("init", toJson i)]))

section
variable {σ ι : Type} [Labels ι] [Store σ ι]

def Function.normalized (f : Function ι) : SourceClaims.Function ι :=
  ⟨f.name,f.namePos,f.params.map (fun b => (b.name,b.type.ground)),f.result.ground,
    f.entries.map (fun e => (e.start,e.bindings.map (fun b => (b.name,b.type.ground)))),
    f.expressions.map (fun e => (e.pos,e.type.ground)),
    f.entries.map (fun e => (e.start,e.bindings.filterMap fun b => b.current.map (b.name,·))),
    f.expressions.filterMap (fun e => e.current.map (e.pos,·)),
    -- Stated by the producer for an overloaded closure.
    (f.arrows.getD []).map (fun a => (a.pos, a.rows.map (fun row =>
      ⟨row.expressions.map (fun e => (e.pos,e.type.ground)),
       row.entries.map (fun e => (e.start,e.bindings.map (fun b => (b.name,b.type.ground)))),
       row.entries.map (fun e => (e.start,e.bindings.filterMap fun b => b.current.map (b.name,·))),
       row.expressions.filterMap (fun e => e.current.map (e.pos,·))⟩)))⟩

private def claimHasScheme : ClaimType ι → Bool
  | .scheme .. => true
  | _ => false

private def Function.hasScheme (f : Function ι) : Bool :=
  claimHasScheme f.result || f.params.any (claimHasScheme ·.type) ||
    f.entries.any (fun e => e.bindings.any (claimHasScheme ·.type)) ||
    f.expressions.any (claimHasScheme ·.type)

/-- A generic module value's instance checks (`moduleInstances`) are not
ordinary graph sequents, but their failures use the same mandatory located
diagnostic channel. The viewer consumes this record structurally and derives
all prose from it. A type argument outside its binder's bound belongs to the
scheme the call eliminates, and says so. -/
private def directFailure (T : σ) (failure : DirectObligation.Located ι) : String :=
  let message :=
    s!"quantified call does not satisfy the closure's bound: cannot establish {failure.judgment.render T}"
  RequestJson.withDiagnostic s!"source direct obligation at [{failure.pos.1},{failure.pos.2}): {message}"
    [("kind",toJson "direct-obligation"),("phase",toJson "request-validation"),
     ("outcome",toJson "not-established"),("id",toJson s!"scheme:{failure.pos.1}"),
     ("sourceMap",toJson (SourceMapEntry.mk failure.pos failure.role.wire none [])),
     ("judgment",failure.judgment.toJson),
     ("fuel",toJson 0),("types",toJson T)]

private def sourceRefusal (T : σ) (pos : Span)
    (role : DirectObligation.SourceRole) (reason : String) : String :=
  RequestJson.withDiagnostic s!"source refusal at [{pos.1},{pos.2}): {reason}"
    [("kind",toJson "source-refusal"),("phase",toJson "request-validation"),
     ("outcome",toJson "not-established"),("id",toJson s!"refusal:{pos.1}"),
     ("sourceMap",toJson (SourceMapEntry.mk pos role.wire none [])),
     ("reason",toJson reason),("fuel",toJson 0),("types",toJson T)]

namespace Scheme

/-- Ground a claim, interning any callable it contains. Only after substitution
does a rigid arrow such as `() => T` have a graph row. -/
private partial def groundIn (T : σ) :
    ClaimType ι → Except String (σ × List ι)
  | .union ts => do
      let (T, arms) ← ts.foldlM (fun (T, acc) t => do
        let (T, A) ← groundIn T t
        pure (T, acc ++ A)) (T, [])
      pure (T, arms.eraseDups.mergeSort Labels.le)
  | .labels A => pure (T, A)
  | .array e => do
      let (T, E) ← groundIn T e
      let (T, store) := Store.intern T [.list ⟨[], [], some E, false, .readable⟩ []]
      let (T, array) := Store.intern T [SourceTypes.arrayOf T store false]
      pure (T, [array])
  | .scheme [] rc ps rest r effect => do
      let (T, rc) ← groundIn T rc
      let (T, ps) ← ps.foldlM (fun (T, acc) p => do
        let (T, a) ← groundIn T p
        pure (T, acc ++ [a])) (T, [])
      let (T, r) ← groundIn T r
      let (T, clause) ← match rest with
        | none => pure (T, PositiveNormalization.Clause.arrs [⟨rc, ps, r, effect⟩] [])
        | some e => do
          -- A rest's type is the pack of any number of actuals at its element.
          let (T, E) ← groundIn T e
          let (T, pack) := Store.intern T [.pack ⟨[], [], some E, false, .dense⟩ []]
          pure (T, PositiveNormalization.Clause.arrs [] [⟨rc, (ps, [pack]), r, effect⟩])
      let (T, l) := Store.intern T [clause]
      pure (T, [l])
  | .param name => throw s!"still the rigid parameter '{name}'"
  | .scheme .. => throw "a scheme is not a ground type"
  | .unavailable reason => throw reason

private def groundOf (role : String) : ClaimType ι → Except String (List ι)
  | .array _ => throw s!"{role} requires grounding an array"
  | .union _ => throw s!"{role} requires grounding a union"
  | .labels A => pure A
  | .param name => throw s!"{role} is still the rigid parameter '{name}'"
  | .scheme .. => throw s!"{role} is a scheme, not a ground type"
  | .unavailable reason => throw reason

/-- Capture-avoiding: a nested scheme's own binders shadow the substitution. -/
private partial def subst (θ : List (String × (ClaimType ι))) : ClaimType ι → ClaimType ι
  | .array e => .array (subst θ e)
  | .union ts => .union (ts.map (subst θ))
  | .param name => (θ.lookup name).getD (.param name)
  | .scheme tps rc ps rest r effect =>
      let inner := θ.filter fun q => !(tps.map Prod.fst).contains q.1
      .scheme (tps.map fun q => (q.1, q.2.map (subst inner))) (subst inner rc) (ps.map (subst inner))
        (rest.map (subst inner)) (subst inner r) effect
  | c => c

/-- Explicit type arguments are a requirement on a call's instance: the call
is typed at the instance they state, binder by binder in declaration order,
even where another would fit. `θ` is the claimed instance, ground. -/
def explicitInstance (T : σ) (pos : Span) (binders : List String)
    (written : List Json) (θ : List (String × List ι)) :
    Except (DirectObligation.Failure ι) σ := do
  let refuse (reason : String) := DirectObligation.Failure.refusal pos .schemeElimination reason
  if written.length > binders.length then
    throw (refuse "more explicit type arguments than the callee has binders")
  let mut T := T
  for (binder, annotation) in binders.zip written do
    let (stated, grown) ← ((Fragment.translate annotation).run T).mapError refuse
    T := grown
    let some claimed := θ.lookup binder | throw (refuse s!"no type argument for '{binder}'")
    unless sameMeaning T stated claimed do
      throw (refuse "the call's instance is not the one its explicit type arguments state")
  return T

/-- A generic module value reached from a unit (a generic module function,
or a generic imported one): the unit's calls name its instances. Each call's
type arguments must be ground and name exactly its binders, and every bound,
at those arguments, must hold by the graph's certified subtyping. Each instance
is the signature at those arguments, a ground callable; the slot holds them
all as one callable with several signatures. A generic module function is
certified for every admissible instantiation by its own unit, and an imported
one is assumed at its declared type, so each instance, and their conjunction,
holds of the value. Returns the grown table, the slot's type in claim form,
and the spans of the callee reads and of the calls. A failure carries the table
its labels index: translating a bound may grow it. -/
def moduleInstances (T : σ) (g : DeclarationGraph.Instantiable σ)
    (unit : List Fragment.Stmt) (claims : Function ι) :
    Except ((DirectObligation.Failure ι) × σ)
      (σ × Json × List Span × List Span) := do
  let refuse (pos : Span) (reason : String) : DirectObligation.Failure ι × σ :=
    (.refusal pos .schemeElimination reason, T)
  let calls := (unit.flatMap Fragment.Stmt.callees).filter (·.2.2.1 == g.name)
  let graph (A : List ι) : Json := Json.mkObj [("top", toJson false),
    ("atoms", toJson (A.map fun l => Json.mkObj [("a", toJson "graph"), ("label", toJson l)]))]
  let sites ← calls.mapM fun (pos, _, _, written) => do
    let some inst := (claims.expressions.find? (·.pos == pos)).bind (·.instantiate)
      | throw (refuse pos s!"a call to the generic function '{g.name}' needs its type arguments")
    let given := inst.map (·.name)
    if given.eraseDups.length != given.length then throw (refuse pos "duplicate type argument")
    if given.length != g.binders.length || given.any (!g.binders.contains ·) then
      throw (refuse pos s!"type arguments do not instantiate exactly the binders of '{g.name}'")
    let θ ← inst.mapM fun i => do
      let A ← (groundOf s!"the type argument for '{i.name}'" i.type).mapError (refuse pos)
      pure (i.name, A)
    pure (pos, θ, written)
  let mut T := T
  let mut seen : List (List (String × List ι)) := []
  let mut instances : List Json := []
  for (pos, θ, written) in sites do
    T ← (explicitInstance T pos g.binders written θ).mapError (·, T)
    if seen.contains θ then continue
    seen := seen ++ [θ]
    let ((callable, bounds), grown) ← ((g.instantiate (θ.map fun (n, A) => (n, graph A))).run T).mapError (refuse pos)
    T := grown
    for (n, bound) in bounds do
      if let some upper := bound then
        let some actual := θ.lookup n | throw (refuse pos s!"no type argument for '{n}'")
        let (required, grown) ← ((Fragment.translate upper).run T).mapError (refuse pos)
        T := grown
        let G := SourceTypes.graph T
        let pool := CertificateProducer.reachablePool G actual required
        let proved := match CertificateProducer.subtype G pool actual required with
          | some proof => PositiveCertificates.check G actual required proof
          | none => false
        unless proved do
          throw (.obligation ⟨pos, .schemeElimination,
            .subtyping pos actual required⟩, T)
    let some atom := (callable.getObjVal? "atoms").toOption.bind (fun a => (a.getArr?.toOption.bind (·[0]?)))
      | throw (refuse pos s!"'{g.name}' is not one callable")
    instances := instances ++ [atom]
  let some first := instances.head? | throw (refuse g.pos s!"'{g.name}' has no call to instantiate")
  let callable := if instances.length == 1 then first else first.setObjVal! "and" (toJson instances.tail)
  return (T, Json.mkObj [("top", toJson false), ("atoms", toJson [callable])],
    calls.map (·.2.1), calls.map (·.1))

/-- A claim with a generic unit's binders read as their parameter rows, in
ground form. A claim that does not ground keeps the reason at its site, as
`ground` does, so only a site the extraction reads refuses. -/
private def atRows (θ : List (String × (ClaimType ι))) (t : ClaimType ι) :
    StateM σ (ClaimType ι) := modifyGet fun T =>
  match groundIn T (subst θ t) with
  | .ok (T, A) => (.labels A, T)
  | .error reason => (.unavailable reason, T)

/-! ### Generic closures as graph code

A generic closure is graph code at a scheme row (`HasTyUsing.funScheme`): its code
is checked once, at the scheme's signatures with the scheme's binders as
parameter rows, and a table entry holds at every assignment of the parameter
rows (`ProgramCertificates.CodesSound`), so at every instantiation. Here each
generic closure's claimed scheme becomes a scheme row whose binders are fresh
value parameter rows; every claim and annotation inside the closure reads its
binders as those rows; and a call of a scheme-typed local is claimed at the
instance the call names, which the checker relates to the scheme by a checked
instance (`Sub.inst`). -/

/-- A generic closure of a unit's source: its span and its binders. -/
structure GenericClosure where
  span : Span
  binders : List Fragment.TypeParam

/-- The generic closures a source tree creates, outer before inner. -/
partial def genericClosures : Json → List GenericClosure
  | .arr xs => xs.toList.flatMap genericClosures
  | .obj kvs =>
    let j := Json.obj kvs
    let here : List GenericClosure :=
      if (j.getObjValAs? String "k").toOption == some "lambda" then
        match (j.getObjValAs? Span "pos").toOption,
            (j.getObjVal? "typeParams").toOption.bind (·.getArr?.toOption) with
        | some pos, some tps =>
          if tps.isEmpty then [] else
          match tps.toList.mapM Fragment.decodeTypeParam with
          | .ok binders => [⟨pos, binders⟩]
          | .error _ => []
        | _, _ => []
      else []
    here ++ kvs.toList.flatMap fun (_, v) => genericClosures v
  | _ => []

/-- Scheme rows made so far: a scheme claim, its enclosing binders already
read as rows, with its row and its binders' rows. -/
abbrev Registry (ι : Type) := List ((ClaimType ι) × ι × List (String × ι))

private abbrev SchemeM (σ ι : Type) := StateT (σ × (Registry ι)) (Except String)

private def internS (c : PositiveNormalization.Clause (List ι)) : SchemeM σ ι ι :=
  modifyGet fun (T, reg) =>
    let (T, l) := Store.intern T [c]
    (l, (T, reg))

/-- A parameter row `l` with a bound of rows `B`: the meet of the two when `B`
is of clause rows, the row itself otherwise. -/
private def boundedRow (l : ι) (B : List ι) : SchemeM σ ι ι := do
  let (T, reg) ← get
  let G := SourceTypes.graph T
  if B.isEmpty || !G.plainTy B then return l
  let (T, m) := Store.bounded T l (B.flatMap G) []
  set (T, reg)
  return m

mutual
/-- A claim, its binders already rows, in ground form: a scheme with binders
of its own is a scheme row, the same row for the same scheme. -/
private partial def groundT : ClaimType ι → SchemeM σ ι (List ι)
  | .labels A => pure A
  | .union ts => do
    let arms ← ts.mapM groundT
    pure (arms.flatten.eraseDups.mergeSort Labels.le)
  | .array e => do
    let E ← groundT e
    let store ← internS (.list ⟨[], [], some E, false, .readable⟩ [])
    let (T, _) ← get
    pure [← internS (SourceTypes.arrayOf T store false)]
  | .scheme [] rc ps rest r effect => do
    let rc ← groundT rc
    let ps ← ps.mapM groundT
    let r ← groundT r
    match rest with
    | none => pure [← internS (.arrs [⟨rc, ps, r, effect⟩] [])]
    | some e => do
      let E ← groundT e
      let pack ← internS (.pack ⟨[], [], some E, false, .dense⟩ [])
      pure [← internS (.arrs [] [⟨rc, (ps, [pack]), r, effect⟩])]
  | .scheme tps rc ps rest r effect => do
    return [(← schemeRowOf (.scheme tps rc ps rest r effect)).1]
  | .param name => throw s!"the rigid parameter '{name}' is not in scope"
  | .unavailable reason => throw reason

/-- Whether a claim names one of `names` as a binder. -/
private partial def mentions (names : List String) : ClaimType ι → Bool
  | .param n => names.contains n
  | .union ts => ts.any (mentions names)
  | .array e => mentions names e
  | .scheme tps rc ps rest r effect =>
    let names := names.filter fun n => !(tps.map Prod.fst).contains n
    tps.any (fun q => q.2.any (mentions names)) || mentions names rc || ps.any (mentions names) ||
      rest.any (mentions names) || mentions names r
  | _ => false

/-- The row of a scheme with binders: its binders fresh value parameter rows,
its signature over them. A binder with a bound of clause rows is read, in the
signature and inside the closure, as the meet of its row and its bound, as a
generic unit's is (`binderRows`): at every instantiation within the bound the
meet is the binder, and elsewhere the scheme promises nothing. Such a bound is
read outside the binders and is the scheme's bound too. A binder bounded by an
earlier one of the same scheme, `U extends T`, is the meet of the two
parameter rows, within `T`'s clauses if it has any (`dependentMeet`), as a
generic unit's is: its bound reads a binder, which the scheme's bounds do not,
so the meet alone states it. Returns the row and what each binder is read as. -/
private partial def schemeRowOf (t : ClaimType ι) : SchemeM σ ι (ι × List (String × ι)) := do
  if let some (_, l, rows) := (← get).2.find? (·.1 == t) then return (l, rows)
  let .scheme tps rc ps rest r effect := t | throw "not a scheme"
  let names := tps.map Prod.fst
  let (T, reg) ← get
  let (T, binders) := Store.binders T names
  set (T, reg)
  let params := names.zip binders
  let meetRow (p : ι) (cs : List (PositiveNormalization.Clause (List ι))) (also : List ι) :
      SchemeM σ ι ι := do
    let (T, reg) ← get
    let (T, m) := Store.bounded T p cs also
    set (T, reg)
    return m
  let mut rows : List (String × ι) := []
  let mut bounds : List (ι × List ι) := []
  for ((n, l), (_, b)) in params.zip tps do
    match b with
    | none => rows := rows ++ [(n, l)]
    | some (.param m) =>
      if !names.contains m then
        let B ← groundT (.param m)
        rows := rows ++ [(n, ← boundedRow l B)]
        bounds := bounds ++ [(l, B)]
      else match rows.lookup m with
        | some r =>
          match SourceTypes.dependentMeet (← get).1 r with
          | some (cs, also) => rows := rows ++ [(n, ← meetRow l cs also)]
          | none => rows := rows ++ [(n, l)]
        | none => throw "a type-parameter bound must name an earlier parameter"
    | some bound =>
      if mentions names bound then
        throw "a type-parameter bound is a ground type or an earlier type parameter"
      let B ← groundT bound
      rows := rows ++ [(n, ← boundedRow l B)]
      bounds := bounds ++ [(l, B)]
  let θ := rows.map fun (n, l) => (n, ClaimType.labels [l])
  let rc ← groundT (subst θ rc)
  let ps ← ps.mapM fun q => groundT (subst θ q)
  let r ← groundT (subst θ r)
  let (sigs, rests) ← match rest with
    | none => pure ([⟨rc, ps, r, effect⟩], [])
    | some e => do
      let E ← groundT (subst θ e)
      let pack ← internS (.pack ⟨[], [], some E, false, .dense⟩ [])
      pure ([], [⟨rc, (ps, [pack]), r, effect⟩])
  let boundRows := bounds
  let (T, reg) ← get
  let (T, label) := Store.scheme T binders sigs boundRows rests
  set (T, reg ++ [(t, label, rows)])
  return (label, rows)
end

/-- The innermost scope, among `scopes`, strictly containing the span `p`. -/
private def scopeAt (scopes : List (Span × List (String × ι))) (outer : List (String × ι))
    (p : Span) : List (String × ι) :=
  let inside := scopes.filter fun (q, _) => q.1 ≤ p.1 && p.2 ≤ q.2 && q != p
  match inside.foldl (fun (best : Option (Span × List (String × ι))) x => match best with
      | some b => if x.1.2 - x.1.1 < b.1.2 - b.1.1 then some x else some b
      | none => some x) none with
  | some (_, rows) => rows
  | none => outer

/-- A unit's claims with its generic closures' schemes as scheme rows, each
claim inside a closure reading the closure's binders as that row's binders,
and a call of a scheme-typed local claimed at the instance it names. `outer`
reads the unit's own binders, if any, as their rows. Returns the grown
table, the claims and the binder scope of each closure. -/
def closureRows (T : σ) (outer : List (String × ι))
    (closures : List GenericClosure) (calls : List (Span × Span × String × List Json))
    (c : Function ι) :
    Except String (σ × (Function ι) × List (Span × List (String × ι))) := do
  let asClaims (rows : List (String × ι)) : List (String × (ClaimType ι)) :=
    rows.map fun (n, l) => (n, .labels [l])
  let run : SchemeM σ ι ((Function ι) × List (Span × List (String × ι))) := do
    -- Each closure's scheme, outer closures first: a closure's binders are
    -- in scope for the closures inside it.
    let mut scopes : List (Span × List (String × ι)) := []
    for gc in closures do
      let enclosing := scopeAt scopes outer gc.span
      let some e := c.expressions.find? (·.pos == gc.span)
        | throw "a generic closure has no claim"
      let .scheme tps _ _ _ _ _ := e.type
        | throw "a generic closure is claimed at no scheme"
      if tps.map Prod.fst != gc.binders.map (·.name) then
        throw "a generic closure's claimed scheme names other binders than its own"
      if gc.binders.any fun b => (enclosing.lookup b.name).isSome then
        throw "a generic closure's binder hides an enclosing binder of its name"
      let (_, rows) ← schemeRowOf (subst (asClaims enclosing) e.type)
      scopes := scopes ++ [(gc.span, rows ++ enclosing)]
    -- A call of a local whose claim is a scheme: its callee is claimed at the
    -- instance the call names.
    let mut instances : List (Span × (ClaimType ι)) := []
    let mut named : List Span := []
    for (p, q, _, _) in calls do
      let some e := c.expressions.find? (·.pos == p) | continue
      let some inst := e.instantiate | continue
      let some callee := c.expressions.find? (·.pos == q) | continue
      let θ := asClaims (scopeAt scopes outer q)
      let .scheme tps rc ps rest r effect := subst θ callee.type | continue
      if tps.isEmpty then continue
      let given := inst.map (·.name)
      if given.eraseDups.length != given.length || given.length != tps.length ||
          given.any (fun n => !(tps.map Prod.fst).contains n) then
        throw "type arguments do not instantiate exactly the scheme's binders"
      let θp := asClaims (scopeAt scopes outer p)
      -- A bounded binder is read as a meet row, so its instance is the meet
      -- of the type arguments of the row's parameters with the row's
      -- clauses: the clause row an instance table maps the meet row to
      -- (`meetOk`), in the order it reads them.
      let args := inst.map fun i => (i.name, subst θp i.type)
      let (sl, rows) ← schemeRowOf (.scheme tps rc ps rest r effect)
      let binders := match Store.row (← get).1 sl with
        | .scheme bs .. => bs
        | _ => []
      let nameOf := binders.zip (tps.map Prod.fst)
      let θi ← args.mapM fun (n, U) => do
        let some l := rows.lookup n | pure (n, U)
        let .meet b cs also := Store.row (← get).1 l | pure (n, U)
        let st ← get
        let meet : SchemeM σ ι (Option ι) := do
          let Us ← (b :: also).mapM fun q => do
            let some m := nameOf.lookup q | throw "a meet row's parameter is no binder of its scheme"
            let some A := args.lookup m | throw s!"no type argument for '{m}'"
            groundT A
          let (T, reg) ← get
          let G := SourceTypes.graph T
          if !Us.all G.plainTy then return none
          let cs := PositiveRules.meetMany (Us.map (PositiveRules.clausesOf G) ++ [cs])
          if cs.isEmpty then return none
          let (T, l) := Store.intern T cs
          set (T, reg)
          return some l
        match meet.run st with
        | .ok (some l, st) => set st; pure (n, .labels [l])
        | _ => pure (n, U)
      instances := instances ++ [(q, .scheme [] (subst θi rc) (ps.map (subst θi))
        (rest.map (subst θi)) (subst θi r) effect)]
      named := named ++ [p]
    let go (at_ : Span) (t : ClaimType ι) : SchemeM σ ι (ClaimType ι) := do
      let t := ((instances.find? (·.1 == at_)).map (·.2)).getD t
      let st ← get
      match (groundT (subst (asClaims (scopeAt scopes outer at_)) t)).run st with
      | .ok (A, st) => set st; pure (.labels A)
      | .error reason => pure (.unavailable reason)
    let entry (e : Entry ι) : SchemeM σ ι (Entry ι) := do
      return { e with bindings := ← e.bindings.mapM fun b => do
        return { b with type := ← go (e.start, e.start + 1) b.type } }
    let params ← c.params.mapM fun b => do return { b with type := ← go (0, 0) b.type }
    let result ← go (0, 0) c.result
    let entries ← c.entries.mapM entry
    let expressions ← c.expressions.mapM fun e => do
      let type ← go e.pos e.type
      let instantiate ← if named.contains e.pos then pure none else
        e.instantiate.mapM (·.mapM fun i => do return { i with type := ← go e.pos i.type })
      return { e with type, instantiate }
    return ({ c with params, result, entries, expressions }, scopes)
  let ((c, scopes), (T, _)) ← run.run (T, [])
  return (T, c, scopes)

/-- A source annotation in claim form with each binder read as its row: the
unit's binders by `θ`, a generic closure's, inside it, by its scope. -/
partial def annotationAtScopes (scopes : List (Span × List (String × ι)))
    (θ : List (String × ι)) : Json → Json
  | .arr xs => .arr (xs.map (annotationAtScopes scopes θ))
  | .obj kvs =>
    let j := Json.obj kvs
    match (j.getObjValAs? String "a").toOption, (j.getObjValAs? String "name").toOption with
    | some "param", some name =>
      match θ.lookup name with
      | some l => if j == Json.mkObj [("a", toJson "param"), ("name", toJson name)] then
          Json.mkObj [("a", toJson "graph"), ("label", toJson l)] else j
      | none => j
    | _, _ =>
      let θ := if (j.getObjValAs? String "k").toOption == some "lambda" then
          match (j.getObjValAs? Span "pos").toOption.bind (fun p => scopes.lookup p) with
          | some rows => rows
          | none => θ
        else θ
      Json.mkObj (kvs.toList.map fun (k, v) =>
        (k, if k == "typeParams" then v else annotationAtScopes scopes θ v))
  | j => j

end Scheme

/-- A generic unit's claims with each binder read as its parameter row
(`rows`): the unit is then an ordinary graph request over those rows, which
the graph checker certifies at every assignment of them
(`Parametricity.accepted_at`). The instantiations its calls state are read
the same way, so a call of a generic module function at a binder names the
instance at that binder's row. -/
def Function.atRows (c : Function ι) (T : σ) (rows : List (String × ι)) :
    σ × (Function ι) :=
  let θ := rows.map fun (n, l) => (n, ClaimType.labels [l])
  let go := Scheme.atRows θ
  let entry (e : Entry ι) : StateM σ (Entry ι) := do
    return { e with bindings := ← e.bindings.mapM fun b => do return { b with type := ← go b.type } }
  let run : StateM σ (Function ι) := do
    let params ← c.params.mapM fun b => do return { b with type := ← go b.type }
    let result ← go c.result
    let entries ← c.entries.mapM entry
    let expressions ← c.expressions.mapM fun e => do
      let type ← go e.type
      let instantiate ← e.instantiate.mapM (·.mapM fun i => do return { i with type := ← go i.type })
      return { e with type, instantiate }
    let arrows ← c.arrows.mapM (·.mapM fun a => do
      let rows ← a.rows.mapM fun r => do
        let expressions ← r.expressions.mapM fun e => do return { e with type := ← go e.type }
        let entries ← r.entries.mapM entry
        return { r with expressions, entries }
      return { a with rows })
    return { c with params, result, entries, expressions, arrows }
  let (c, T) := run.run T
  (T, c)



/-- The table starts with the primitives and refers only to its own labels. -/
private def validTable (T : SourceTypes.Table) : Bool :=
  SourceTypes.initial.isPrefixOf T && RequestJson.validRows T
private partial def validType (T : σ) : ClaimType ι → Bool
  | .union ts => !ts.isEmpty && ts.all (validType T)
  | .array e => validType T e
  | .param name => !name.isEmpty
  | .scheme typeParams receiver params rest result effect =>
      -- With no binders of its own this is a callable that mentions an
      -- enclosing rigid parameter, such as a returned `() => T`.
      (typeParams.map Prod.fst).eraseDups.length == typeParams.length &&
      typeParams.all (fun p => !p.1.isEmpty && p.2.all (validType T)) &&
      validType T receiver && params.all (validType T) && rest.all (validType T) &&
      validType T result
  | .unavailable reason => !reason.isEmpty
  | .labels A => validTy (Store.valid T) A && A == A.mergeSort Labels.le && A.eraseDups == A
/-- Every asserted field is one the point's own record contract names, each at
most once, at a type this table has. The asserted type need not be finite: a
field the extractor cannot turn into a literal assertion becomes an obligation
that the storage contract already implies it. -/
private def validCurrent (T : σ) (A : ClaimType ι) (current : Option (CurrentFields ι)) : Bool :=
  match current with
  | none => true
  | some fs =>
    !fs.isEmpty && (fs.map Prod.fst).eraseDups.length == fs.length &&
    -- Every record the binding may hold names the field: a fact is about
    -- the location the field is at, whichever record the object is.
    (match PositiveRules.expand (SourceTypes.graph T) (A.ground.toOption.getD []) with
      | [] => false
      | cs => cs.all fun
        | .refs contract [] vs .. => fs.all (fun p => (contract.lookup p.1).isSome || (vs.lookup p.1).isSome)
        | _ => false) &&
    fs.all (fun p => validType T (.labels p.2))
private def validBindings (T : σ) (bs : List (Binding ι)) : Bool :=
  (bs.map (·.name)).eraseDups.length == bs.length &&
    bs.all (fun b => !b.name.isEmpty && validType T b.type && validCurrent T b.type b.current)
private def validSpan (p : Span) : Bool := p.1 < p.2
private def validInterior (T : σ) (entries : List (Entry ι))
    (expressions : List (Expression ι)) : Bool :=
  (entries.map (·.start)).eraseDups.length == entries.length &&
  (expressions.map (·.pos)).eraseDups.length == expressions.length &&
  entries.all (fun e => validBindings T e.bindings) &&
  expressions.all (fun e => validSpan e.pos && validType T e.type && validCurrent T e.type e.current)
private def validFunction (T : σ) (f : Function ι) : Bool :=
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

def decode (j : Json) : Except String (Document SourceTypes.Table Nat) := do
  let d : Document SourceTypes.Table Nat ← decodeStrict j
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

/-! ### Labels

A label on the wire is a row of the document's own table or a tree naming a
row the producer does not build: an application of the declaration at a
position of the declaration document's `definitions`, with every argument
(none for a nullary one), an intersection of its parts, an array over its
store's row, or a binder in scope (SOURCE-CLAIMS.md, "Encoding"). Each
form has one spelling, and a label list is in canonical order. -/

inductive Label where
  | row (index : Nat)
  | decl (position : Nat) (args : List (List Label))
  | meet (parts : List (List Label))
  | array (store : List Label) (readonly : Bool)
  | binder (name : String)
  deriving Inhabited

namespace Label

private def rank : Label → Nat
  | .row _ => 0
  | .decl .. => 1
  | .meet _ => 2
  | .array .. => 3
  | .binder _ => 4

private def lex : Ordering → Ordering → Ordering
  | .eq, o => o
  | o, _ => o

mutual
/-- The canonical order: rows by index, then declarations, intersections,
arrays and binders, each by its fields in order, lists lexicographically. -/
partial def cmp : Label → Label → Ordering
  | .row a, .row b => compare a b
  | .decl k A, .decl k' A' => lex (compare k k') (cmpLists A A')
  | .meet P, .meet P' => cmpLists P P'
  | .array S r, .array S' r' => lex (cmpList S S') (compare r r')
  | .binder a, .binder b => compare a b
  | a, b => compare a.rank b.rank
partial def cmpList : List Label → List Label → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => lex (cmp a b) (cmpList as bs)
partial def cmpLists : List (List Label) → List (List Label) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => lex (cmpList a b) (cmpLists as bs)
end

instance : BEq Label := ⟨fun a b => a.cmp b == .eq⟩

/-- Whether a label list is in canonical order, each label once. -/
def canonical (ls : List Label) : Bool := (ls.zip ls.tail).all fun (a, b) => a.cmp b == .lt

partial def toJson : Label → Json
  | .row n => Lean.toJson n
  | .decl k [] => Json.mkObj [("decl", Lean.toJson k)]
  | .decl k args => Json.mkObj [("decl", Lean.toJson k),
      ("args", Json.arr (args.map fun A => Json.arr (A.map toJson).toArray).toArray)]
  | .meet parts => Json.mkObj [("meet", Json.arr (parts.map fun A => Json.arr (A.map toJson).toArray).toArray)]
  | .array store readonly => Json.mkObj [("array", Json.arr (store.map toJson).toArray),
      ("readonly", Lean.toJson readonly)]
  | .binder name => Json.mkObj [("binder", Lean.toJson name)]

mutual
partial def fromJson (j : Json) : Except String Label := do
  match j with
  | .num _ => return .row (← j.getNat?)
  | .obj _ =>
    if let .ok k := j.getObjVal? "decl" then
      let k ← k.getNat?
      match j.getObjVal? "args" with
      | .ok args =>
        CellClaims.fieldsExactly j ["decl", "args"]
        let args ← (← args.getArr?).toList.mapM listFromJson
        if args.isEmpty then throw "a nullary declaration's label leaves its arguments out"
        return .decl k args
      | .error _ =>
        CellClaims.fieldsExactly j ["decl"]
        return .decl k []
    if let .ok parts := j.getObjVal? "meet" then
      CellClaims.fieldsExactly j ["meet"]
      let parts ← (← parts.getArr?).toList.mapM listFromJson
      if parts.length < 2 then throw "an intersection's label has at least two parts"
      return .meet parts
    if let .ok store := j.getObjVal? "array" then
      CellClaims.fieldsExactly j ["array", "readonly"]
      return .array (← listFromJson store) (← (← j.getObjVal? "readonly").getBool?)
    if let .ok name := j.getObjVal? "binder" then
      CellClaims.fieldsExactly j ["binder"]
      let name ← name.getStr?
      if name.isEmpty then throw "a binder's label names it"
      return .binder name
    throw "a label tree is a declaration's application, an intersection, an array or a binder"
  | _ => throw "a label is a row index or a label tree"
/-- A label list, in canonical order. -/
partial def listFromJson (j : Json) : Except String (List Label) := do
  let ls ← (← j.getArr?).toList.mapM fromJson
  if !canonical ls then throw "a label list is in canonical order, each label once"
  return ls
end

instance : ToJson Label := ⟨toJson⟩
instance : FromJson Label := ⟨fromJson⟩

end Label

/-! ### The finite layout: a temporary adapter

TEMPORARY: deleted at the cutover, stage S6 of "Recursive equations" in
[DESIGN](DESIGN.md#status), when lowering builds equations over tree labels.
Until then `DeclarationGraph.prepare` and everything after it read the finite
layout the wire had before tree labels, and this is the only place that knows
it: the four primitives, an empty row per nullary declaration, the
producer's other rows, then, as the labels first name them, an empty row per
application, array and intersection, listed for `prepare` to fill, and a
parameter row per binder name. Every label is rewritten as its row. -/
namespace FiniteLayout

structure State where
  /-- The producer's rows, the primitives included. -/
  size : Nat
  /-- Each definition's parameter count, by position. -/
  arities : Array Nat
  /-- The positions of the nullary definitions, in order. -/
  nullary : List Nat
  /-- Each tree label given a row, with the row. -/
  given : List (Label × Nat) := []
  /-- The rows given, in order, after the producer's. -/
  rows : List Json := []
  applications : List (Nat × Nat × List (List Nat)) := []
  arrays : List (Nat × Nat × Bool) := []
  meets : List (Nat × List (List Nat)) := []

abbrev M := StateT State (Except String)

private def give (l : Label) (row : Nat → Json) (record : Nat → State → State) : M Nat :=
  modifyGet fun s =>
    let r := s.size + s.nullary.length + s.rows.length
    (r, record r { s with given := s.given ++ [(l, r)], rows := s.rows ++ [row r] })

private def emptyRow : Nat → Json := fun _ => Json.arr #[]

mutual
/-- A label's row, giving a tree label one when it first occurs, after its
arguments' or parts' rows. -/
partial def resolve (l : Label) : M Nat := do
  let s ← get
  match l with
  | .row n =>
    if n ≥ s.size then throw "a label names no row of the table"
    return if n < 4 then n else n + s.nullary.length
  | .decl k [] =>
    match s.arities[k]? with
    | none => throw "a declaration's label names no declaration"
    | some 0 => return 4 + (s.nullary.filter (· < k)).length
    | some _ => throw "a generic declaration's label states its arguments"
  | _ =>
    if let some r := s.given.lookup l then return r
    match l with
    | .decl k args =>
      match s.arities[k]? with
      | none => throw "a declaration's label names no declaration"
      | some n =>
        if n != args.length then
          throw "a declaration's label states one argument per parameter"
        let args ← args.mapM resolveList
        give l emptyRow fun row s => { s with applications := s.applications ++ [(row, k, args)] }
    | .meet parts =>
      let parts ← parts.mapM resolveList
      give l emptyRow fun row s => { s with meets := s.meets ++ [(row, parts)] }
    | .array store readonly =>
      let [store] ← resolveList store | throw "an array's label names its store's one row"
      give l emptyRow fun row s => { s with arrays := s.arrays ++ [(row, store, readonly)] }
    | .binder name =>
      give l (fun row => Lean.toJson (PositiveGraphs.GraphRow.param row name .value : Row)) fun _ s => s
    | .row _ => throw "a row label has no tree"
/-- A union's rows, sorted. -/
partial def resolveList (ls : List Label) : M (List Nat) := do
  return ((← ls.mapM resolve).mergeSort (· ≤ ·)).eraseDups
end

/-- One of the producer's rows: a clause row or a scheme row. A binder and
an intersection are labels, never rows the producer writes. -/
private def row (j : Json) : M Json := do
  let r : PositiveGraphs.GraphRow Label (List Label) ← decodeStrict j
  let unions := match r with
    | .clauses cs => cs.flatMap PositiveNormalization.Clause.operands
    | .scheme _ sigs bounds rests => sigs.flatMap CallEffects.Arrow.operands ++
        bounds.map (fun (b : Label × List Label) => b.2) ++ rests.flatMap CallEffects.RestArrow.operands
    | .param .. | .meet .. => []
  match r with
  | .param .. | .meet .. =>
    throw "a producer's row is a clause row or a scheme row; binders and intersections are labels"
  | _ => pure ()
  if !unions.all Label.canonical then throw "a label list is in canonical order, each label once"
  for A in r.operands do
    for l in A do discard (resolve l)
  let s ← get
  let at_ (l : Label) : Nat := ((resolve l).run' s).toOption.getD 0
  return Lean.toJson (r.map at_ (fun A => ((A.map at_).mergeSort (· ≤ ·)).eraseDups) : Row)

private def labels (j : Json) : M Json := do
  return Lean.toJson (← resolveList (← Label.listFromJson j))

/-- `j` with field `k`, where it has one, rewritten by `f`. -/
private def update (j : Json) (k : String) (f : Json → M Json) : M Json := do
  match j.getObjVal? k with
  | .ok v => return j.setObjVal! k (← f v)
  | .error _ => return j

private def each (f : Json → M Json) : Json → M Json
  | .arr xs => return .arr (← xs.mapM f)
  | j => return j

private def nullable (f : Json → M Json) : Json → M Json
  | .null => return .null
  | j => f j

/-- A claim type: labels, or a form over claim types. -/
private partial def claim (j : Json) : M Json := do
  match j with
  | .arr _ => labels j
  | _ =>
    let j ← update j "union" (each claim)
    let j ← update j "array" claim
    update j "scheme" fun s => do
      let s ← update s "typeParams" (each fun p => update p "bound" (nullable claim))
      let s ← update s "this" claim
      let s ← update s "params" (each claim)
      let s ← update s "rest" (nullable claim)
      update s "result" claim

/-- A point: its type, what it asserts of each field, and the type arguments
of the call it is. -/
private def point (j : Json) : M Json := do
  let j ← update j "type" claim
  let j ← update j "current" (nullable (each fun
    | .arr #[k, A] => return .arr #[k, ← labels A]
    | f => return f))
  update j "instantiate" (nullable (each fun i => update i "type" claim))

/-- A unit's claims: a function's, or the initialization's. -/
private def unit (j : Json) : M Json := do
  let entries := each fun e => update e "bindings" (each point)
  let j ← update j "params" (each point)
  let j ← update j "result" claim
  let j ← update j "entries" entries
  let j ← update j "expressions" (each point)
  update j "arrows" (each fun a => update a "rows" (each fun r => do
    let r ← update r "expressions" (each point)
    update r "entries" entries))

/-- The document in the finite layout, and the rows `prepare` fills: each
application's `(row, declaration position, arguments)`, each array's
`(row, store, readonly)` and each intersection's `(row, parts)`. -/
def finite (ast claims : Json) : Except String
    (Json × List (Nat × Nat × List (List Nat)) × List (Nat × Nat × Bool) × List (Nat × List (List Nat))) := do
  let definitions := (((ast.getObjVal? "declarations").toOption.bind
    fun d => (d.getObjVal? "definitions").toOption).bind (·.getArr?.toOption)).getD #[]
  let arities := definitions.map fun d =>
    (((d.getObjVal? "parameters").toOption.bind (·.getArr?.toOption)).map (·.size)).getD 0
  let types ← (← claims.getObjVal? "types").getArr?
  let run : M Json := do
    let rows ← types.toList.mapM row
    let claims ← update claims "functions" (each unit)
    let claims ← update claims "init" unit
    let s ← get
    let table := rows.take 4 ++ s.nullary.map (fun _ => Json.arr #[]) ++ rows.drop 4 ++ s.rows
    return claims.setObjVal! "types" (.arr table.toArray)
  let start : State := {
    size := types.size
    arities := arities
    nullary := (List.range arities.size).filter fun k => arities[k]? == some 0 }
  let (j, s) ← run.run start
  return (j, s.applications, s.arrays, s.meets)

end FiniteLayout

private abbrev Sites := List Nat × List Span × List Span
private def joinSites (a b : Sites) : Sites := (a.1 ++ b.1,a.2.1 ++ b.2.1,a.2.2 ++ b.2.2)
/-- The spans of a pattern's array rests: each is a fresh array, claimed like
an array literal. -/
private partial def restSpans : Fragment.Pattern Fragment.Expr → List Span
  | .name .. => []
  | .object _ props rest => props.flatMap (fun (_, t, _) => restSpans t) ++
      match rest with
      | some (q, t) => q :: restSpans t
      | none => []
  | .array _ elems rest => elems.flatMap (fun (_, t, _) => restSpans t) ++
      match rest with
      | some (_, q, _, t) => q :: restSpans t
      | none => []
mutual
private partial def exprSites : Fragment.Expr → Sites
  | .var p _ | .lit p _ => ([],[p],[])
  -- A defaulted parameter's expression is an ordinary source expression, so it
  -- is a claim site like any other; the parameter name is not one.
  | .lambda p _ _ _ defaults _ _ e =>
    defaults.attach.foldl (fun acc ⟨d,_⟩ => joinSites acc (exprSites d.2))
      (joinSites ([],[p],[p]) (exprSites e))
  | .shapeTest p _ _ e | .not p e | .unary p _ e | .cast p _ e | .read p _ e => joinSites ([],[p],[]) (exprSites e)
  | .alloc p _ es | .build p _ es => es.foldl (fun acc a => joinSites acc (exprSites a)) ([],[p],[])
  | .withValue p a b _ _ | .write p _ a b | .singletonTest p _ _ _ a b | .equality p _ a b | .coalesce p a b | .logical p _ a b => joinSites ([],[p],[]) (joinSites (exprSites a) (exprSites b))
  -- An assignment is an expression site, and the name it assigns is not one:
  -- the producer claims the value written, not the location.
  | .index p _ a b | .arith p _ a b | .logicalAssign p _ a b | .elemAt p a b | .comma p a b | .inKeys p a b => joinSites ([],[p],[]) (joinSites (exprSites a) (exprSites b))
  | .arrayLit p es => es.foldl (fun acc a => joinSites acc (exprSites a)) ([],[p],[])
  | .objectAssign p t ss => ss.foldl (fun acc a => joinSites acc (exprSites a))
      (joinSites ([],[p],[]) (exprSites t))
  | .arrayAssign p targets rest rhs => targets.foldl (fun acc q => match q.default_ with
      | some d => joinSites acc (exprSites d) | none => acc)
      (joinSites ([],p :: (rest.map (·.1)).toList,[]) (exprSites rhs))
  | .elemWrite p a b c => joinSites ([],[p],[]) (joinSites (exprSites a) (joinSites (exprSites b) (exprSites c)))
  | .update p _ a none _ => joinSites ([],[p],[]) (exprSites a)
  | .update p _ a (some r) _ => joinSites ([],[p],[]) (joinSites (exprSites a) (exprSites r))
  | .indexWrite p _ a b c => joinSites ([],[p],[]) (joinSites (exprSites a) (joinSites (exprSites b) (exprSites c)))
  | .nullishAssign p _ np e => joinSites ([],[p,np],[]) (exprSites e)
  | .assign p _ _ e => joinSites ([],[p],[]) (exprSites e)
  | .bindWithReceiver p f receiver args | .callWithReceiver p f receiver args => args.foldl (fun acc a => joinSites acc (exprSites a))
      (joinSites ([],[p],[]) (joinSites (exprSites f) (exprSites receiver)))
  | .call p f args _ _ | .invoke p f args _ _ => args.foldl (fun acc a => joinSites acc (exprSites a)) (joinSites ([],[p],[]) (exprSites f))
  -- A class value is one expression; its constructor's body has its own sites.
  | .ctor p (.lambda _ _ _ _ _ _ _ e) => joinSites ([],[p],[]) (exprSites e)
  | .ctor p _ => ([],[p],[])
  | .construct p f args _ => args.foldl (fun acc a => joinSites acc (exprSites a)) (joinSites ([],[p],[]) (exprSites f))
  | .applyWithReceiver p f receiver list =>
    joinSites ([],[p],[]) (joinSites (exprSites f) (joinSites (exprSites receiver)
      ((list.map exprSites).getD ([],[],[]))))
  -- The saved receiver's read, spelled at the `?.` token, is a site of its own.
  | .optional p _ r b => joinSites ([],[p],[]) (joinSites (exprSites r) (exprSites b))
  | .ifBody p a b c => joinSites ([],[p],[]) (joinSites (exprSites a) (joinSites (exprSites b) (exprSites c)))
  -- A closure's statements are its body's sites, as a function's are.
  | .block _ ss => ss.foldl (fun s st => joinSites s (stmtSites st)) ([],[],[])
private partial def stmtSites : Fragment.Stmt → Sites
  | .brk p _ | .cont p => ([p.1],[],[])
  | .ret p e | .effect p e | .throw p e => joinSites ([p.1],[],[]) (exprSites e)
  -- A `try` is an entry; its blocks' statements have their own.
  | .tryStmt p body handler finalizer =>
    (body ++ ((handler.map (·.2)).getD []) ++ finalizer.getD []).foldl
      (fun s st => joinSites s (stmtSites st)) ([p.1],[],[])
  -- One entry for the statement; every declarator's initializer is a site.
  | .constants p bs | .mutables p bs => bs.foldl (fun acc b => joinSites acc (exprSites b.init)) ([p.1],[],[])
  -- The initializer, each default and each array rest, a fresh array like a
  -- literal, are sites; the pattern's reads are not.
  | .destructure p target d init =>
    (d.toList ++ target.defaults).foldl (fun acc e => joinSites acc (exprSites e))
      (joinSites ([p.1],restSpans target,[]) (exprSites init))
  | .loop p c body update => joinSites ([p.1],[],[]) (joinSites (exprSites c)
      ((body ++ update).foldl (fun s st => joinSites s (stmtSites st)) ([],[],[])))
  -- A block has no entry of its own.
  | .block _ _ body => body.foldl (fun s st => joinSites s (stmtSites st)) ([],[],[])
  -- An iterator's closing region is an entry, as a `try` is; its body's and
  -- its close's statements have their own.
  | .closing p close body =>
    (body ++ close).foldl (fun s st => joinSites s (stmtSites st)) ([p.1],[],[])
  | .ite p c a b =>
    joinSites ([p.1],[],[]) (joinSites (exprSites c)
      ((a ++ b.getD []).foldl (fun s st => joinSites s (stmtSites st)) ([],[],[])))
  -- The loop's span is its iteration intrinsic's call's, and the element is
  -- claimed at the name it binds.
  | .forOf p _ np _ i body => joinSites ([p.1],[p, np],[]) (joinSites (exprSites i)
      (body.foldl (fun s st => joinSites s (stmtSites st)) ([],[],[])))

end
private def allFunctionSites (f : Fragment.Fn) : Sites :=
  f.body.foldl (fun s st => joinSites s (stmtSites st)) ([],[],[])

def functionSites (f : Fragment.Fn) : List Nat × List Span :=
  let sites := allFunctionSites f
  (sites.1, sites.2.1)

/-- A unit's plan: its graph request. Every unit is one, a generic unit and a
generic closure included, their binders parameter rows the graph checks at
every assignment. -/
inductive FunctionPlan (σ ι : Type) where
  | graph (name : String) (namePos : Span) (request : SourceRequest σ ι)

/-- A plan admitted by the top-level verified outcome. Graph evidence is
consumed separately. Adding a source-plan variant cannot silently enter this
exhaustive boundary through a projection. -/
inductive CertifiedPlan (σ ι : Type) where
  | graph (name : String) (namePos : Span) (request : SourceRequest σ ι)

def CertifiedPlan.requests : List (CertifiedPlan σ ι) → List (SourceRequest σ ι)
  | [] => []
  | .graph _ _ request :: rest => request :: CertifiedPlan.requests rest

/-- Graph projection for search and inspection. This is intentionally not the
acceptance boundary. -/
def FunctionPlan.requests : List (FunctionPlan σ ι) → List (SourceRequest σ ι)
  | [] => []
  | .graph _ _ request :: rest => request :: FunctionPlan.requests rest

/-- The sole conversion into the verified-plan type. Exhaustive matching makes
a new `FunctionPlan` constructor a compile error here. -/
def FunctionPlan.certify : FunctionPlan σ ι → Except String (CertifiedPlan σ ι)
  | .graph name pos request => pure (.graph name pos request)

def certifyPlans (plans : List (FunctionPlan σ ι)) : Except String (List (CertifiedPlan σ ι)) :=
  plans.mapM FunctionPlan.certify

/-- A module constant holds no value until its declaration runs. Walking the
top-level code in order, a step may reach a module function, directly or
through the functions that one mentions, only when every module constant those
functions mention already holds its value. Mentions over-approximate calls, so
this refuses some safe orders and admits no unsafe one. -/
private def checkInitializationOrder (T : σ)
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

/-- A prepared ground bound's graph labels. -/
private def boundLabels (j : Json) : Option (List ι) := do
  if (j.getObjVal? "top").toOption != some (toJson false) then none
  let atoms ← ((j.getObjVal? "atoms").toOption).bind (·.getArr?.toOption)
  atoms.toList.mapM fun a => do
    if (a.getObjValAs? String "a").toOption != some "graph" then none
    (a.getObjValAs? ι "label").toOption

/-- A prepared bound naming exactly one binder: that binder's name. -/
private def boundBinder (j : Json) : Option String := do
  if (j.getObjVal? "top").toOption != some (toJson false) then none
  let atoms ← ((j.getObjVal? "atoms").toOption).bind (·.getArr?.toOption)
  let #[a] := atoms | none
  if a != Json.mkObj [("a", toJson "param"), ("name", a.getObjValD "name")] then none
  (a.getObjValAs? String "name").toOption

/-- The row that stands for each of a generic unit's binders: its parameter
row (`SourceTypes.binderRow`), met with its bound when the bound is a ground
type of clause rows, `T extends { length: number }` read as `T ⊓ { length:
number }`, or when the bound is an earlier binder, `U extends T` read as
`U ⊓ T` (`SourceTypes.dependentMeet`). Every assignment of the parameter row
is an instance: one within the bound is the binder itself, and the body is
certified at all of them. Any other bound leaves the parameter row alone. -/
private def binderRows (T : σ) (tps : List Fragment.TypeParam) :
    Except String (σ × List (String × ι)) := do
  let (rows, T) ← (tps.foldlM (fun (rows : List (String × ι)) (tp : Fragment.TypeParam) => do
    let p ← SourceTypes.binderRow tp.name
    let G := SourceTypes.graph (← get)
    let row : ι ← match tp.bound.bind boundLabels, tp.bound.bind boundBinder with
      | some B, _ =>
        if B.isEmpty || !G.plainTy B then pure p
        else SourceTypes.bounded p (B.flatMap G)
      | none, some m =>
        match rows.lookup m with
        | some r => match SourceTypes.dependentMeet (← get) r with
          | some (cs, also) => SourceTypes.bounded p cs also
          | none => pure p
        | none => pure p
      | none, none => pure p
    return rows ++ [(tp.name, row)]) []).run T
  return (T, rows)

/-- Whether a source function's tree declares type parameters below its own:
a generic closure, whose binders the unit's rows do not stand for. -/
private partial def nestedBinders : Json → Bool
  | .arr xs => xs.any nestedBinders
  | .obj kvs =>
    -- A class's binders are its declaring unit's, not a closure's.
    let isClass := kvs.toList.lookup "k" == some (.str "ctor")
    kvs.toList.any fun (k, v) =>
      (k == "typeParams" && !isClass && v != Json.arr #[]) || nestedBinders v
  | _ => false

/-- The ctor nodes' binder lists in a tree. -/
private partial def ctorBinderLists : Json → List Json
  | .arr xs => xs.toList.flatMap ctorBinderLists
  | .obj kvs =>
    let here := if kvs.toList.lookup "k" == some (.str "ctor") then
        match kvs.toList.lookup "typeParams" with
        | some (.arr ps) => ps.toList
        | _ => []
      else []
    here ++ kvs.toList.flatMap fun (_, v) => ctorBinderLists v
  | _ => []

/-- The names the top-level code binds generic classes to. -/
private def genericClassNames (j : Json) : List String :=
  match j with
  | .arr sts => sts.toList.flatMap fun st =>
    match (st.getObjVal? "bindings").toOption with
    | some (.arr bs) => bs.toList.filterMap fun b =>
      match (b.getObjVal? "init").toOption with
      | some init =>
        if (init.getObjValAs? String "k").toOption == some "ctor" &&
            ((init.getObjVal? "typeParams").toOption.bind (·.getArr?.toOption)).any (!·.isEmpty)
        then (b.getObjValAs? String "name").toOption else none
      | none => none
    | _ => []
  | _ => []

/-- The binders of the generic classes the module's top-level code declares:
the initialization unit's, read as parameter rows. One spelling is one row,
so two classes may share a binder's name only with the same bound. -/
private def classBinders (j : Json) : Except String (List Fragment.TypeParam) := do
  let mut out : List Fragment.TypeParam := []
  for p in ctorBinderLists j do
    let tp ← Fragment.decodeTypeParam p
    match out.find? (·.name == tp.name) with
    | some q => if q.bound != tp.bound then
        throw s!"two generic classes bind '{tp.name}' with different bounds"
    | none => out := out ++ [tp]
  return out

/-- A source's claims read into a store, and what the source's declarations
give its units: the source tree with its annotations in claim form, the
claims over the store's labels, the imported values at their declared types
and the generic module values. -/
structure Prepared (σ ι : Type) where
  ast : Json
  document : Document σ ι
  imported : List (String × Span × Json)
  generics : List (DeclarationGraph.Instantiable σ)

/-- How a store is prepared from a source and its claims, for the function
`only` selects or for every unit. -/
abbrev Front (σ ι : Type) :=
  (ast claims : Json) → (fileKey : String) → (only : Option (String × Span)) →
    Except String (Prepared σ ι)

/-- The claims are about the source: its file and its fingerprint. -/
def checkIdentity (d : Document σ ι) (ast : Json) (fileKey : String) : Except String Unit := do
  if d.file != fileKey || (← jStr (← jField ast "file")) != fileKey then throw "source claim file identity mismatch"
  if (← jStr (← jField ast "sourceSha256")) != d.sourceSha256 then throw "source claim fingerprint mismatch"

/-- `only` selects one function of the file, named with its position: the
others remain its module, reachable at their signatures, and need no claims. -/
def extractPlansWith [Meets σ ι] (front : Front σ ι) (ast claims : Json) (fileKey : String)
    (only : Option (String × Span) := none) : Except String (List (FunctionPlan σ ι)) := do
  -- A source with arrays lists `ArrayProto`: its units see `Array.prototype`.
  let arrays := match (ast.getObjVal? "declarations").toOption.bind
      (fun doc => (doc.getObjVal? "definitions").toOption) with
    | some (.arr ds) => ds.any fun d =>
        ((d.getObjVal? "declaration").toOption.bind fun i => (i.getObjVal? "module").toOption) ==
          some (Json.str "skjs/array-prototype")
    | _ => false
  let ⟨ast, d, imported, generics⟩ ← front ast claims fileKey only
  let functionJsons := ((ast.getObjVal? "functions").toOption.bind (·.getArr?.toOption)).getD #[]
  let all ← Fragment.decodeAstWithParams ast
  let fs := all.map Prod.fst
  if (fs.map (fun f => (f.name,f.namePos))).eraseDups.length != fs.length then throw "duplicate source function identities"
  let init ← Fragment.decodeInit ast
  -- A module whose only code is its initialization is checked through that
  -- unit alone; a module with neither runs nothing and states no claim.
  if fs.isEmpty && init.isEmpty then throw "no source code to verify: no function and no module initialization"
  -- A body reaches the file's other ordinary functions at their annotated
  -- signatures, and a function also reaches the module's constants at their
  -- annotations; each of those is established by its own unit.
  -- Imported values join them at the types their declarations state.
  let moduleFunctions : List (SourceExtraction.ModuleValue ι) :=
    (all.filterMap fun (g, tps) => if tps.isEmpty then
      some (g.name, g.namePos, (moduleArrow g).map .written) else none) ++
    (imported.map fun (name, span, ty) => (name, span, .ok (.written ty))) ++
    (if arrays then [(SourceExtraction.arrayPrototypeName, (0, 0),
      Except.ok (.written (Json.mkObj [("top", toJson false), ("atoms", toJson [Json.mkObj
        [("a", toJson "graph"), ("label", toJson (Store.arrayProto d.types))]])])))] else [])
  -- Every immutable module value retains its initializer's checked claim and
  -- its annotation. The initialization unit checks both contracts; an
  -- annotation does not erase independently inferred facts such as call effects.
  -- A generic class is read at the instances its uses name, as a generic
  -- module function is (`generics`), not at its declaring unit's rows.
  let classNames := genericClassNames ((ast.getObjVal? "init").toOption.getD (.arr #[]))
  let moduleConstants : List (SourceExtraction.ModuleValue ι) := init.flatMap fun
    | .constants _ bs => (bs.filter fun b => !classNames.contains b.name).map fun b =>
      (b.name, b.namePos, match (d.init.map (·.expressions)).getD [] |>.find? (·.pos == b.init.span) with
        | some e => .ok (.claimed e.type.ground b.annot)
        | none => .error s!"module constant '{b.name}' has no claimed initializer")
    | _ => []
  -- A class's instance members are closures created before the class value
  -- is bound, and run only once it is: they read it as its own binding
  -- (`Fragment.selfBindingOf`), which the initialization unit reads as a
  -- module value at the class's construct signature, the annotation its
  -- binding is checked at there, as a function reads a module constant. A
  -- generic class's is not one (the parser refuses its self-reads).
  let classSelves : List (SourceExtraction.ModuleValue ι) := init.flatMap fun
    | .constants _ bs =>
      let ctors := bs.filterMap fun b => match b.init with
        | .ctor .. => some b.name
        | _ => none
      bs.filterMap fun b => match b.annot with
        | some ty =>
          if !classNames.contains b.name &&
              (ctors.contains b.name || ctors.contains (b.name ++ ".[[class]]")) then
            some (Fragment.selfBindingOf b.name, b.namePos, .ok (.written ty))
          else none
        | none => none
    | _ => []
  -- The initialization unit: the top-level code, as a body with no
  -- parameters that completes with `undefined`.
  let initUnit : List (Fragment.Fn × List Fragment.TypeParam × (Function ι)) ← match init, d.init with
    | [], none => pure []
    | [], some _ => throw "module initialization claims for a source without initialization code"
    | _ :: _, none => throw "missing claims for the module initialization"
    | first :: _, some c =>
      let span := (first.pos.1, (init.getLast?.map (·.pos.2)).getD first.pos.2)
      let undefinedType := Json.mkObj [("top", toJson false),
        ("atoms", toJson [Json.mkObj [("a", toJson "undefined")]])]
      let binders ← classBinders ((ast.getObjVal? "init").toOption.getD (.arr #[]))
      pure [(⟨"", span, [], undefinedType, init⟩, binders,
        ⟨"", span, [], .labels [Labels.undef], c.entries, c.expressions, c.arrows⟩)]
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
    let module := if initClaims.isSome then moduleFunctions ++ classSelves
      else moduleFunctions ++ moduleConstants
    let mut c ← match initClaims with
      | some c => pure c
      | none => match d.functions.find? (fun c => c.name == f.name && c.namePos == f.namePos) with
        | some c => pure c
        | none => throw s!"missing claims for '{f.name}'"
    let mut module := module
    let mut d := d
    let mut f := f
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
    if c.hasScheme && tps.isEmpty && !(c.arrows.getD []).isEmpty then
      throw "per-arrow source claims are for ground closures, not quantified schemes"
    -- The unit's source tree, and the generic closures it creates, each
    -- graph code at its scheme row.
    let unitSource := if initClaims.isSome then
        some (Json.mkObj [("body", (ast.getObjVal? "init").toOption.getD (.arr #[]))])
      else functionJsons.find? fun j =>
        (j.getObjValAs? String "name").toOption == some f.name &&
          (j.getObjValAs? Span "namePos").toOption == some f.namePos
    let closures := match unitSource with
      | some j => Scheme.genericClosures ((j.getObjVal? "body").toOption.getD .null)
      | none => []
    let graphClosures := !closures.isEmpty
    if !tps.isEmpty then
      -- A generic unit is an ordinary graph request: each binder is read as
      -- its parameter row, a bounded one as its meet with its bound (an
      -- earlier binder's row, for a dependent bound), and the unit is
      -- certified at every assignment of those rows
      -- (`Parametricity.accepted_at`).
      let some source := unitSource
        | throw "a generic unit's source function is missing"
      if nestedBinders ((source.getObjVal? "body").toOption.getD .null) && !graphClosures then
        throw (sourceRefusal d.types f.namePos .genericValidation
          "a generic closure inside a generic body has binders of its own")
      let (T, rows) ← match binderRows d.types tps with
        | .ok r => pure r
        | .error reason => throw (sourceRefusal d.types f.namePos .genericValidation reason)
      let (T, atRows, scopes) ← if graphClosures then
          match Scheme.closureRows T rows closures (f.body.flatMap Fragment.Stmt.callees) c with
          | .ok r => pure r
          | .error reason => throw (sourceRefusal T f.namePos .schemeIntroduction reason)
        else
          let (T, atRows) := c.atRows T rows
          pure (T, atRows, [])
      d := { d with types := T }
      c := atRows
      let source := Scheme.annotationAtScopes scopes rows source
      if initClaims.isSome then
        let body ← Fragment.decodeInit (Json.mkObj [("init", source.getObjValD "body")])
        f := { f with body }
      else
        f := (← Fragment.decodeFn source).1
    else if graphClosures && c.hasScheme then
      -- A generic closure in a unit without binders of its own: its scheme is
      -- a scheme row, its code graph code checked at the row's signatures.
      let some source := unitSource | throw "a unit's source function is missing"
      let (T, claims, scopes) ← match Scheme.closureRows d.types [] closures
          (f.body.flatMap Fragment.Stmt.callees) c with
        | .ok r => pure r
        | .error reason => throw (sourceRefusal d.types f.namePos .schemeIntroduction reason)
      d := { d with types := T }
      c := claims
      let source := Scheme.annotationAtScopes scopes [] source
      if initClaims.isSome then
        let body ← Fragment.decodeInit (Json.mkObj [("init", source.getObjValD "body")])
        f := { f with body }
      else
        f := (← Fragment.decodeFn source).1
    let finish (d : Document σ ι) (module : List (SourceExtraction.ModuleValue ι)) (c : Function ι)
        (f : Fragment.Fn) : Except String (FunctionPlan σ ι) := do
      let mut d := d
      let mut module := module
      let mut c := c
      -- A generic module function this unit calls: its slot holds the instances
      -- the calls name, and those reads and calls are claimed at them.
      if !c.hasScheme then
        for g in generics.filter (fun g => !(initClaims.isSome && classNames.contains g.name)) do
          if (f.body.flatMap Fragment.Stmt.callees).any (·.2.2.1 == g.name) then
            match Scheme.moduleInstances d.types g f.body c with
            | .ok (T, slot, reads, calls) =>
              d := { d with types := T }
              -- The callee reads are claimed at the slot's type, which the
              -- source fixes; the producer's reading of them is not needed.
              let (A, T) ← match (Fragment.translate slot).run d.types with
                | .ok r => pure r
                | .error reason => throw (sourceRefusal d.types g.pos .schemeElimination reason)
              d := { d with types := T }
              module := module ++ [(g.name, g.pos, .ok (.written slot))]
              c := { c with expressions := c.expressions.map fun e =>
                if reads.contains e.pos then { e with type := .labels A }
                else if calls.contains e.pos then { e with instantiate := none } else e }
            | .error (.obligation failure, T) => throw (directFailure T failure)
            | .error (.refusal pos role reason, _) => throw (sourceRefusal d.types pos role reason)
      -- Every generic closure's scheme is a scheme row by now; a scheme claim
      -- left names no closure of the source.
      if c.hasScheme then
        throw (sourceRefusal d.types f.namePos .schemeIntroduction
          "a scheme claim has no quantified closure in its source")
      return .graph f.name f.namePos (← extractNormalizedFn d.types f c.normalized module)
    -- A generic unit's graph extraction reports where it stops as a
    -- located refusal at the function, as the direct checker's do.
    if tps.isEmpty then finish d module c f
    else tryCatch (finish d module c f) fun e =>
      throw (if (e.splitOn "obligation-diagnostic: ").length > 1 then e
        else sourceRefusal d.types f.namePos .genericValidation e)

def checkJsonWith [Meets σ ι] (front : Front σ ι) (ast claims : Json) (fileKey : String) (evidence : Json)
    (only : Option (String × Span) := none) : Except String Unit := do
  let plans ← extractPlansWith front ast claims fileKey only
  let certified ← certifyPlans plans
  let rs := CertifiedPlan.requests certified
  let b : Bundle ι ← decodeStrict evidence
  if checkRequests rs b then return ()
  throw "source evidence does not justify the extracted program and exact claims"

def produceJsonWith [Meets σ ι] (front : Front σ ι) (ast claims : Json) (fileKey : String) (fuel : Nat)
    (only : Option (String × Span) := none) : Except String Json := do
  let plans ← extractPlansWith front ast claims fileKey only
  let rs := FunctionPlan.requests plans
  let es ← rs.mapM fun r => ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels (Store.valid r.types) (Store.labels r.types) fuel r.obligations
  let cs ← (rs.zip es).mapM fun (r,proofs) => do
    let known := proofs ++ ExpressionClaims.renderKnown (RequestJson.graph r.toRequest)
      r.searchLabels (Store.valid r.types) r.nodePlans
    let j ← RequestJson.produceJson σ (toJson r.toRequest) fuel [] known r.sourceMap (some r.searchLabels) r.assertions r.cuts r.codeHints
    decodeResponse r.toRequest j
  let evidence := toJson (Bundle.mk cs es)
  let b : Bundle ι ← decodeStrict evidence
  if !checkRequests rs b then
    throw "source evidence does not justify the extracted graph requests"
  return evidence

end

/-! ### The finite table's entry points -/

/-- The finite table's front end: the claims in the finite layout
(`FiniteLayout`), their table filled from the source's declarations
(`DeclarationGraph.prepare`). -/
def finiteFront : Front SourceTypes.Table Nat := fun ast claims fileKey only => do
  let (claims, applications, arrayRows, meets) ←
    (FiniteLayout.finite ast claims).mapError (s!"invalid source claims: {·}")
  let d ← decode claims
  checkIdentity d ast fileKey
  -- Every declaration application in the source becomes a graph row, or, over
  -- a rigid binder, the claim type of its expanded source equation.
  -- Declaration failures precede graph construction, but still belong to the
  -- unit requiring these contracts. Locate them at that unit, not at an
  -- external library's byte offset misinterpreted as a span in this file.
  let contractSite := only.map Prod.snd |>.getD
    ((d.functions.head?.map (·.namePos)).getD (0, 0))
  let (ast, types, imported, generics) ← (DeclarationGraph.prepare ast d.types
    applications arrayRows meets).mapError fun reason =>
      sourceRefusal d.types contractSite .bindingAnnotation
        s!"the declarations required by this unit cannot be interpreted: {reason}"
  let d := { d with types }
  if !validTable d.types then throw "declaration graph has an invalid type reference"
  return ⟨ast, d, imported, generics⟩

def extractPlans (ast claims : Json) (fileKey : String) (only : Option (String × Span) := none) :
    Except String (List (FunctionPlan SourceTypes.Table Nat)) :=
  extractPlansWith finiteFront ast claims fileKey only

/-- Graph-only projection for proof fixtures that inspect extracted programs. -/
def extractGraphRequests (ast claims : Json) (fileKey : String) :
    Except String (List (SourceRequest SourceTypes.Table Nat)) := do
  return FunctionPlan.requests (← extractPlans ast claims fileKey)

def checkJson (ast claims : Json) (fileKey : String) (evidence : Json)
    (only : Option (String × Span) := none) : Except String Unit :=
  checkJsonWith finiteFront ast claims fileKey evidence only

def produceJson (ast claims : Json) (fileKey : String) (fuel : Nat)
    (only : Option (String × Span) := none) : Except String Json :=
  produceJsonWith finiteFront ast claims fileKey fuel only

/-- Every extracted plan crosses the exhaustive certification boundary, and its
graph request proves the enclosing execution safe at every assignment of the
parameter rows, so a generic unit or closure at every instantiation. -/
theorem checkJson_safe {ast claims evidence : Json} {fileKey : String}
    {only : Option (String × Span)}
    (h : checkJson ast claims fileKey evidence only = .ok ()) :
    ∃ plans certified b, extractPlans ast claims fileKey only = .ok plans ∧
      certifyPlans plans = .ok certified ∧
      decodeStrict evidence = .ok b ∧
      checkRequests (CertifiedPlan.requests certified) b = true ∧
      (∀ r c, (r,c) ∈ (CertifiedPlan.requests certified).zip b.functions →
        ∀ η n W heap ρ, EnvOk (reassign (RequestJson.graph r.toRequest) η) r.inputs ρ n W →
          WorldAdm W → HeapOk n W heap →
          SafeGraph r.program (meaning (reassign (RequestJson.graph r.toRequest) η) r.result)
            n W heap (.at r.start ρ)) := by
  unfold checkJson checkJsonWith at h
  cases he : extractPlans ast claims fileKey only with
  | error e =>
    unfold extractPlans at he
    rw [he] at h
    contradiction
  | ok plans =>
    unfold extractPlans at he
    rw [he] at h
    simp only [Bind.bind, Except.bind] at h
    cases hc : certifyPlans plans with
    | error e =>
      rw [hc] at h
      contradiction
    | ok certified =>
      rw [hc] at h
      cases hb : (decodeStrict evidence : Except String (Bundle Nat)) with
      | error e =>
        rw [hb] at h
        contradiction
      | ok b =>
        rw [hb] at h
        by_cases hx : checkRequests (CertifiedPlan.requests certified) b = true
        · refine ⟨plans,certified,b,rfl,hc,rfl,hx,?_⟩
          intro r c hm η n W heap ρ he hw hh
          exact checkRequests_safe_at hx hm η n W heap ρ he hw hh
        · simp [hx] at h

#print axioms checkJson_safe
end Verification.Model.SourceClaimJson
