import Verification.Model.Source.SourceExtraction
import Verification.Model.Source.DeclarationGraph

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
      ClaimType → CallEffects.Effect → ClaimType
  | unavailable : String → ClaimType
  deriving Repr, BEq, Inhabited
instance : Coe (List Nat) ClaimType := ⟨ClaimType.labels⟩

private partial def ClaimType.toJson : ClaimType → Json
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
/-- A generic declaration's application the producer reserved an empty row
for: the row, the declaration's position among the definitions, and the
argument types. Lean fills the row. -/
structure Application where
  row : Nat
  declaration : Nat
  args : List (List Nat)
  deriving ToJson, FromJson, Repr

/-- An array type the producer reserved an empty row for: the row, the row of
its store's tuple contract, and whether it is readonly. Lean fills the row
with the array shape (`SourceTypes.arrayClause`), so no producer spells it. -/
structure ArrayRow where
  row : Nat
  store : Nat
  readonly : Bool
  deriving ToJson, FromJson, Repr

/-- An intersection the producer reserved an empty row for: the row and its
operands' types. Lean fills the row with their meet (`DeclarationGraph.meetRow`),
so no producer spells it. -/
structure MeetRow where
  row : Nat
  parts : List (List Nat)
  deriving ToJson, FromJson, Repr

structure Document where
  file : String
  sourceSha256 : String
  types : SourceTypes.Table
  functions : List Function
  /-- Present exactly when the source has module initialization code. -/
  init : Option InitClaims := none
  /-- Generic applications the producer reserved rows for; absent when none. -/
  applications : Option (List Application) := none
  /-- Array types the producer reserved rows for; absent when none. -/
  arrays : Option (List ArrayRow) := none
  /-- Intersections the producer reserved rows for; absent when none. -/
  meets : Option (List MeetRow) := none
  deriving FromJson

/-- Absence asserts nothing: a source with no initialization code has no
initialization claims, and no producer writes an empty one. -/
instance : ToJson Document where
  toJson d := Json.mkObj ([("file", toJson d.file), ("sourceSha256", toJson d.sourceSha256),
    ("types", toJson d.types), ("functions", toJson d.functions)] ++
    (match d.init with
     | none => []
     | some i => [("init", toJson i)]) ++
    (match d.applications with
     | none | some [] => []
     | some a => [("applications", toJson a)]) ++
    (match d.arrays with
     | none | some [] => []
     | some a => [("arrays", toJson a)]) ++
    (match d.meets with
     | none | some [] => []
     | some a => [("meets", toJson a)]))


def Function.normalized (f : Function) : SourceClaims.Function :=
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

private def claimHasScheme : ClaimType → Bool
  | .scheme .. => true
  | _ => false

private def Function.hasScheme (f : Function) : Bool :=
  claimHasScheme f.result || f.params.any (claimHasScheme ·.type) ||
    f.entries.any (fun e => e.bindings.any (claimHasScheme ·.type)) ||
    f.expressions.any (claimHasScheme ·.type)

/-- A generic module value's instance checks (`moduleInstances`) are not
ordinary graph sequents, but their failures use the same mandatory located
diagnostic channel. The viewer consumes this record structurally and derives
all prose from it. A type argument outside its binder's bound belongs to the
scheme the call eliminates, and says so. -/
private def directFailure (T : SourceTypes.Table) (failure : DirectObligation.Located) : String :=
  let message :=
    s!"quantified call does not satisfy the closure's bound: cannot establish {failure.judgment.render T}"
  RequestJson.withDiagnostic s!"source direct obligation at [{failure.pos.1},{failure.pos.2}): {message}"
    [("kind",toJson "direct-obligation"),("phase",toJson "request-validation"),
     ("outcome",toJson "not-established"),("id",toJson s!"scheme:{failure.pos.1}"),
     ("sourceMap",toJson (SourceMapEntry.mk failure.pos failure.role.wire none [])),
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
      let store := PositiveNormalization.Clause.list ⟨[], [], some E, false, .readable⟩ []
      let T := SourceTypes.intern T store
      let array := SourceTypes.arrayOf T (SourceTypes.label T store) false
      let T := SourceTypes.intern T array
      pure (T, [SourceTypes.label T array])
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
          let pack := PositiveNormalization.Clause.pack ⟨[], [], some E, false, .dense⟩ []
          let T := SourceTypes.intern T pack
          pure (T, PositiveNormalization.Clause.arrs [] [⟨rc, (ps, [SourceTypes.label T pack]), r, effect⟩])
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
  | .scheme tps rc ps rest r effect =>
      let inner := σ.filter fun q => !(tps.map Prod.fst).contains q.1
      .scheme (tps.map fun q => (q.1, q.2.map (subst inner))) (subst inner rc) (ps.map (subst inner))
        (rest.map (subst inner)) (subst inner r) effect
  | c => c

/-- Explicit type arguments are a requirement on a call's instance: the call
is typed at the instance they state, binder by binder in declaration order,
even where another would fit. `σ` is the claimed instance, ground. -/
def explicitInstance (T : SourceTypes.Table) (pos : Span) (binders : List String)
    (written : List Json) (σ : List (String × List Nat)) :
    Except DirectObligation.Failure SourceTypes.Table := do
  let refuse (reason : String) := DirectObligation.Failure.refusal pos .schemeElimination reason
  if written.length > binders.length then
    throw (refuse "more explicit type arguments than the callee has binders")
  let mut T := T
  for (binder, annotation) in binders.zip written do
    let (stated, grown) ← ((Fragment.translate annotation).run T).mapError refuse
    T := grown
    let some claimed := σ.lookup binder | throw (refuse s!"no type argument for '{binder}'")
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
def moduleInstances (T : SourceTypes.Table) (g : DeclarationGraph.Instantiable)
    (unit : List Fragment.Stmt) (claims : Function) :
    Except (DirectObligation.Failure × SourceTypes.Table)
      (SourceTypes.Table × Json × List Span × List Span) := do
  let refuse (pos : Span) (reason : String) : DirectObligation.Failure × SourceTypes.Table :=
    (.refusal pos .schemeElimination reason, T)
  let calls := (unit.flatMap Fragment.Stmt.callees).filter (·.2.2.1 == g.name)
  let graph (A : List Nat) : Json := Json.mkObj [("top", toJson false),
    ("atoms", toJson (A.map fun l => Json.mkObj [("a", toJson "graph"), ("label", toJson l)]))]
  let sites ← calls.mapM fun (pos, _, _, written) => do
    let some inst := (claims.expressions.find? (·.pos == pos)).bind (·.instantiate)
      | throw (refuse pos s!"a call to the generic function '{g.name}' needs its type arguments")
    let given := inst.map (·.name)
    if given.eraseDups.length != given.length then throw (refuse pos "duplicate type argument")
    if given.length != g.binders.length || given.any (!g.binders.contains ·) then
      throw (refuse pos s!"type arguments do not instantiate exactly the binders of '{g.name}'")
    let σ ← inst.mapM fun i => do
      let A ← (groundOf s!"the type argument for '{i.name}'" i.type).mapError (refuse pos)
      pure (i.name, A)
    pure (pos, σ, written)
  let mut T := T
  let mut seen : List (List (String × List Nat)) := []
  let mut instances : List Json := []
  for (pos, σ, written) in sites do
    T ← (explicitInstance T pos g.binders written σ).mapError (·, T)
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
private def atRows (σ : List (String × ClaimType)) (t : ClaimType) :
    StateM SourceTypes.Table ClaimType := modifyGet fun T =>
  match groundIn T (subst σ t) with
  | .ok (T, A) => (.labels A, T)
  | .error reason => (.unavailable reason, T)

/-! ### Generic closures as graph code

A generic closure is graph code at a scheme row (`HasTy.funScheme`): its code
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
abbrev Registry := List (ClaimType × Nat × List (String × Nat))

private abbrev SchemeM := StateT (SourceTypes.Table × Registry) (Except String)

private def internS (c : PositiveNormalization.Clause (List Nat)) : SchemeM Nat :=
  modifyGet fun (T, reg) =>
    let T := SourceTypes.intern T c
    (SourceTypes.label T c, (T, reg))

/-- A parameter row `l` with a bound of rows `B`: the meet of the two when `B`
is of clause rows, the row itself otherwise. -/
private def boundedRow (l : Nat) (B : List Nat) : SchemeM Nat := do
  let (T, reg) ← get
  let G := SourceTypes.graph T
  if B.isEmpty || !G.plainTy B then return l
  let m := GraphRow.meet l (B.flatMap G)
  match T.idxOf? m with
  | some i => return i
  | none => set (T ++ [m], reg); return T.length

mutual
/-- A claim, its binders already rows, in ground form: a scheme with binders
of its own is a scheme row, the same row for the same scheme. -/
private partial def groundT : ClaimType → SchemeM (List Nat)
  | .labels A => pure A
  | .union ts => do
    let arms ← ts.mapM groundT
    pure (arms.flatten.eraseDups.mergeSort (· ≤ ·))
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
private partial def mentions (names : List String) : ClaimType → Bool
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
private partial def schemeRowOf (t : ClaimType) : SchemeM (Nat × List (String × Nat)) := do
  if let some (_, l, rows) := (← get).2.find? (·.1 == t) then return (l, rows)
  let .scheme tps rc ps rest r effect := t | throw "not a scheme"
  let names := tps.map Prod.fst
  let (T, reg) ← get
  let params := tps.zipIdx.map fun ((n, _), i) => (n, T.length + i)
  set (T ++ params.map (fun (n, l) => GraphRow.param l n .value), reg)
  let meetRow (m : RequestJson.Row) : SchemeM Nat := do
    let (T, reg) ← get
    match T.idxOf? m with
    | some i => return i
    | none => set (T ++ [m], reg); return T.length
  let mut rows : List (String × Nat) := []
  let mut bounds : List (Nat × List Nat) := []
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
          match SourceTypes.dependentMeet (← get).1 l r with
          | some m => rows := rows ++ [(n, ← meetRow m)]
          | none => rows := rows ++ [(n, l)]
        | none => throw "a type-parameter bound must name an earlier parameter"
    | some bound =>
      if mentions names bound then
        throw "a type-parameter bound is a ground type or an earlier type parameter"
      let B ← groundT bound
      rows := rows ++ [(n, ← boundedRow l B)]
      bounds := bounds ++ [(l, B)]
  let σ := rows.map fun (n, l) => (n, ClaimType.labels [l])
  let rc ← groundT (subst σ rc)
  let ps ← ps.mapM fun q => groundT (subst σ q)
  let r ← groundT (subst σ r)
  let (sigs, rests) ← match rest with
    | none => pure ([⟨rc, ps, r, effect⟩], [])
    | some e => do
      let E ← groundT (subst σ e)
      let pack ← internS (.pack ⟨[], [], some E, false, .dense⟩ [])
      pure ([], [⟨rc, (ps, [pack]), r, effect⟩])
  let boundRows := bounds
  let (T, reg) ← get
  let label := T.length
  set (T ++ [GraphRow.scheme (params.map Prod.snd) sigs boundRows rests],
    reg ++ [(t, label, rows)])
  return (label, rows)
end

/-- The innermost scope, among `scopes`, strictly containing the span `p`. -/
private def scopeAt (scopes : List (Span × List (String × Nat))) (outer : List (String × Nat))
    (p : Span) : List (String × Nat) :=
  let inside := scopes.filter fun (q, _) => q.1 ≤ p.1 && p.2 ≤ q.2 && q != p
  match inside.foldl (fun (best : Option (Span × List (String × Nat))) x => match best with
      | some b => if x.1.2 - x.1.1 < b.1.2 - b.1.1 then some x else some b
      | none => some x) none with
  | some (_, rows) => rows
  | none => outer

/-- A unit's claims with its generic closures' schemes as scheme rows, each
claim inside a closure reading the closure's binders as that row's binders,
and a call of a scheme-typed local claimed at the instance it names. `outer`
reads the unit's own binders, if any, as their rows. Returns the grown
table, the claims and the binder scope of each closure. -/
def closureRows (T : SourceTypes.Table) (outer : List (String × Nat))
    (closures : List GenericClosure) (calls : List (Span × Span × String × List Json))
    (c : Function) :
    Except String (SourceTypes.Table × Function × List (Span × List (String × Nat))) := do
  let asClaims (rows : List (String × Nat)) : List (String × ClaimType) :=
    rows.map fun (n, l) => (n, .labels [l])
  let run : SchemeM (Function × List (Span × List (String × Nat))) := do
    -- Each closure's scheme, outer closures first: a closure's binders are
    -- in scope for the closures inside it.
    let mut scopes : List (Span × List (String × Nat)) := []
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
    let mut instances : List (Span × ClaimType) := []
    let mut named : List Span := []
    for (p, q, _, _) in calls do
      let some e := c.expressions.find? (·.pos == p) | continue
      let some inst := e.instantiate | continue
      let some callee := c.expressions.find? (·.pos == q) | continue
      let σ := asClaims (scopeAt scopes outer q)
      let .scheme tps rc ps rest r effect := subst σ callee.type | continue
      if tps.isEmpty then continue
      let given := inst.map (·.name)
      if given.eraseDups.length != given.length || given.length != tps.length ||
          given.any (fun n => !(tps.map Prod.fst).contains n) then
        throw "type arguments do not instantiate exactly the scheme's binders"
      let σp := asClaims (scopeAt scopes outer p)
      -- A bounded binder is read as a meet row, so its instance is the meet
      -- of the type arguments of the row's parameters with the row's
      -- clauses: the clause row an instance table maps the meet row to
      -- (`meetOk`), in the order it reads them.
      let args := inst.map fun i => (i.name, subst σp i.type)
      let (sl, rows) ← schemeRowOf (.scheme tps rc ps rest r effect)
      let binders := match (← get).1[sl]? with
        | some (.scheme bs ..) => bs
        | _ => []
      let nameOf := binders.zip (tps.map Prod.fst)
      let σi ← args.mapM fun (n, U) => do
        let some l := rows.lookup n | pure (n, U)
        let some (.meet b cs also) := (← get).1[l]? | pure (n, U)
        let st ← get
        let meet : SchemeM (Option Nat) := do
          let Us ← (b :: also).mapM fun q => do
            let some m := nameOf.lookup q | throw "a meet row's parameter is no binder of its scheme"
            let some A := args.lookup m | throw s!"no type argument for '{m}'"
            groundT A
          let (T, reg) ← get
          let G := SourceTypes.graph T
          if !Us.all G.plainTy then return none
          let cs := PositiveRules.meetMany (Us.map (PositiveRules.clausesOf G) ++ [cs])
          if cs.isEmpty then return none
          let row := GraphRow.clauses cs
          match T.idxOf? row with
          | some l => return some l
          | none => set (T ++ [row], reg); return some T.length
        match meet.run st with
        | .ok (some l, st) => set st; pure (n, .labels [l])
        | _ => pure (n, U)
      instances := instances ++ [(q, .scheme [] (subst σi rc) (ps.map (subst σi))
        (rest.map (subst σi)) (subst σi r) effect)]
      named := named ++ [p]
    let go (at_ : Span) (t : ClaimType) : SchemeM ClaimType := do
      let t := ((instances.find? (·.1 == at_)).map (·.2)).getD t
      let st ← get
      match (groundT (subst (asClaims (scopeAt scopes outer at_)) t)).run st with
      | .ok (A, st) => set st; pure (.labels A)
      | .error reason => pure (.unavailable reason)
    let entry (e : Entry) : SchemeM Entry := do
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
unit's binders by `σ`, a generic closure's, inside it, by its scope. -/
partial def annotationAtScopes (scopes : List (Span × List (String × Nat)))
    (σ : List (String × Nat)) : Json → Json
  | .arr xs => .arr (xs.map (annotationAtScopes scopes σ))
  | .obj kvs =>
    let j := Json.obj kvs
    match (j.getObjValAs? String "a").toOption, (j.getObjValAs? String "name").toOption with
    | some "param", some name =>
      match σ.lookup name with
      | some l => if j == Json.mkObj [("a", toJson "param"), ("name", toJson name)] then
          Json.mkObj [("a", toJson "graph"), ("label", toJson l)] else j
      | none => j
    | _, _ =>
      let σ := if (j.getObjValAs? String "k").toOption == some "lambda" then
          match (j.getObjValAs? Span "pos").toOption.bind (fun p => scopes.lookup p) with
          | some rows => rows
          | none => σ
        else σ
      Json.mkObj (kvs.toList.map fun (k, v) =>
        (k, if k == "typeParams" then v else annotationAtScopes scopes σ v))
  | j => j

end Scheme

/-- A generic unit's claims with each binder read as its parameter row
(`rows`): the unit is then an ordinary graph request over those rows, which
the graph checker certifies at every assignment of them
(`Parametricity.accepted_at`). The instantiations its calls state are read
the same way, so a call of a generic module function at a binder names the
instance at that binder's row. -/
def Function.atRows (c : Function) (T : SourceTypes.Table) (rows : List (String × Nat)) :
    SourceTypes.Table × Function :=
  let σ := rows.map fun (n, l) => (n, ClaimType.labels [l])
  let go := Scheme.atRows σ
  let entry (e : Entry) : StateM SourceTypes.Table Entry := do
    return { e with bindings := ← e.bindings.mapM fun b => do return { b with type := ← go b.type } }
  let run : StateM SourceTypes.Table Function := do
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
private partial def validType (T : SourceTypes.Table) : ClaimType → Bool
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
    -- Every record the binding may hold names the field: a fact is about
    -- the location the field is at, whichever record the object is.
    (match PositiveRules.expand (SourceTypes.graph T) (A.ground.toOption.getD []) with
      | [] => false
      | cs => cs.all fun
        | .refs contract [] vs .. => fs.all (fun p => (contract.lookup p.1).isSome || (vs.lookup p.1).isSome)
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
inductive FunctionPlan where
  | graph (name : String) (namePos : Span) (request : SourceRequest)

/-- A plan admitted by the top-level verified outcome. Graph evidence is
consumed separately. Adding a source-plan variant cannot silently enter this
exhaustive boundary through a projection. -/
inductive CertifiedPlan where
  | graph (name : String) (namePos : Span) (request : SourceRequest)

def CertifiedPlan.requests : List CertifiedPlan → List SourceRequest
  | [] => []
  | .graph _ _ request :: rest => request :: CertifiedPlan.requests rest

/-- Graph projection for search and inspection. This is intentionally not the
acceptance boundary. -/
def FunctionPlan.requests : List FunctionPlan → List SourceRequest
  | [] => []
  | .graph _ _ request :: rest => request :: FunctionPlan.requests rest

/-- The sole conversion into the verified-plan type. Exhaustive matching makes
a new `FunctionPlan` constructor a compile error here. -/
def FunctionPlan.certify : FunctionPlan → Except String CertifiedPlan
  | .graph name pos request => pure (.graph name pos request)

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

/-- A prepared ground bound's graph labels. -/
private def boundLabels (j : Json) : Option (List Nat) := do
  if (j.getObjVal? "top").toOption != some (toJson false) then none
  let atoms ← ((j.getObjVal? "atoms").toOption).bind (·.getArr?.toOption)
  atoms.toList.mapM fun a => do
    if (a.getObjValAs? String "a").toOption != some "graph" then none
    (a.getObjValAs? Nat "label").toOption

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
private def binderRows (T : SourceTypes.Table) (tps : List Fragment.TypeParam) :
    Except String (SourceTypes.Table × List (String × Nat)) := do
  let (rows, T) ← (tps.foldlM (fun (rows : List (String × Nat)) (tp : Fragment.TypeParam) => do
    let p ← SourceTypes.binderRow tp.name
    let G := SourceTypes.graph (← get)
    let row : Nat ← match tp.bound.bind boundLabels, tp.bound.bind boundBinder with
      | some B, _ =>
        if B.isEmpty || !G.plainTy B then pure p
        else SourceTypes.internRow (GraphRow.meet p (B.flatMap G))
      | none, some m =>
        match rows.lookup m with
        | some r => match SourceTypes.dependentMeet (← get) p r with
          | some meet => SourceTypes.internRow meet
          | none => pure p
        | none => pure p
      | none, none => pure p
    return rows ++ [(tp.name, row)]) []).run T
  return (T, rows)

private def annotationAtRows := SourceTypes.annotationAtRows

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

/-- `only` selects one function of the file, named with its position: the
others remain its module, reachable at their signatures, and need no claims. -/
def extractPlans (ast claims : Json) (fileKey : String) (only : Option (String × Span) := none) :
    Except String (List FunctionPlan) := do
  let d ← decode claims
  if d.file != fileKey || (← jStr (← jField ast "file")) != fileKey then throw "source claim file identity mismatch"
  if (← jStr (← jField ast "sourceSha256")) != d.sourceSha256 then throw "source claim fingerprint mismatch"
  -- Every declaration application in the source becomes a graph row, or, over
  -- a rigid binder, the claim type of its expanded source equation.
  -- A source with arrays lists `ArrayProto`: its units see `Array.prototype`.
  let arrays := match (ast.getObjVal? "declarations").toOption.bind
      (fun doc => (doc.getObjVal? "definitions").toOption) with
    | some (.arr ds) => ds.any fun d =>
        ((d.getObjVal? "declaration").toOption.bind fun i => (i.getObjVal? "module").toOption) ==
          some (Json.str "skjs/array-prototype")
    | _ => false
  -- Declaration failures precede graph construction, but still belong to the
  -- unit requiring these contracts. Locate them at that unit, not at an
  -- external library's byte offset misinterpreted as a span in this file.
  let contractSite := only.map Prod.snd |>.getD
    ((d.functions.head?.map (·.namePos)).getD (0, 0))
  let (ast, types, imported, generics) ← (DeclarationGraph.prepare ast d.types
    ((d.applications.getD []).map fun a => (a.row, a.declaration, a.args))
    ((d.arrays.getD []).map fun a => (a.row, a.store, a.readonly))
    ((d.meets.getD []).map fun m => (m.row, m.parts))).mapError fun reason =>
      sourceRefusal d.types contractSite .bindingAnnotation
        s!"the declarations required by this unit cannot be interpreted: {reason}"
  let d := { d with types }
  if !validTable d.types then throw "declaration graph has an invalid type reference"
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
  let moduleFunctions : List SourceExtraction.ModuleValue :=
    (all.filterMap fun (g, tps) => if tps.isEmpty then
      some (g.name, g.namePos, (moduleArrow g).map .written) else none) ++
    (imported.map fun (name, span, ty) => (name, span, .ok (.written ty))) ++
    (if arrays then [(SourceExtraction.arrayPrototypeName, (0, 0),
      Except.ok (.written (Json.mkObj [("top", toJson false), ("atoms", toJson [Json.mkObj
        [("a", toJson "graph"), ("label", toJson SourceTypes.arrayProtoLabel)]])])))] else [])
  -- Every immutable module value retains its initializer's checked claim and
  -- its annotation. The initialization unit checks both contracts; an
  -- annotation does not erase independently inferred facts such as call effects.
  -- A generic class is read at the instances its uses name, as a generic
  -- module function is (`generics`), not at its declaring unit's rows.
  let classNames := genericClassNames ((ast.getObjVal? "init").toOption.getD (.arr #[]))
  let moduleConstants : List SourceExtraction.ModuleValue := init.flatMap fun
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
  let classSelves : List SourceExtraction.ModuleValue := init.flatMap fun
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
  let initUnit : List (Fragment.Fn × List Fragment.TypeParam × Function) ← match init, d.init with
    | [], none => pure []
    | [], some _ => throw "module initialization claims for a source without initialization code"
    | _ :: _, none => throw "missing claims for the module initialization"
    | first :: _, some c =>
      let span := (first.pos.1, (init.getLast?.map (·.pos.2)).getD first.pos.2)
      let undefinedType := Json.mkObj [("top", toJson false),
        ("atoms", toJson [Json.mkObj [("a", toJson "undefined")]])]
      let binders ← classBinders ((ast.getObjVal? "init").toOption.getD (.arr #[]))
      pure [(⟨"", span, [], undefinedType, init⟩, binders,
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
    let finish (d : Document) (module : List SourceExtraction.ModuleValue) (c : Function)
        (f : Fragment.Fn) : Except String FunctionPlan := do
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
    let known := proofs ++ ExpressionClaims.renderKnown (RequestJson.graph r.toRequest)
      r.searchLabels r.types.length r.nodePlans
    let j ← RequestJson.produceJson (toJson r.toRequest) fuel [] known r.sourceMap (some r.searchLabels) r.assertions r.cuts r.codeHints
    decodeResponse r.toRequest j
  let evidence := toJson (Bundle.mk cs es)
  let b : Bundle ← decodeStrict evidence
  if !checkRequests rs b then
    throw "source evidence does not justify the extracted graph requests"
  return evidence

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
        · refine ⟨plans,certified,b,rfl,hc,rfl,hx,?_⟩
          intro r c hm η n W heap ρ he hw hh
          exact checkRequests_safe_at hx hm η n W heap ρ he hw hh
        · simp [hx] at h

#print axioms checkJson_safe
end Verification.Model.SourceClaimJson
