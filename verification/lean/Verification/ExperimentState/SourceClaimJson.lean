import Verification.ExperimentState.SourceExtraction

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
  | unavailable : String → ClaimType
instance : Coe (List Nat) ClaimType := ⟨ClaimType.labels⟩
instance : ToJson ClaimType where
  toJson
    | .labels A => toJson A
    | .param name => Json.mkObj [("param",toJson name)]
    | .unavailable reason => Json.mkObj [("unavailable",toJson reason)]
instance : FromJson ClaimType where
  fromJson? j := match j with
    | .arr _ => ClaimType.labels <$> fromJson? j
    | _ => do
      if let .ok reason := j.getObjValAs? String "unavailable" then
        if j != Json.mkObj [("unavailable",toJson reason)] || reason.isEmpty then throw "invalid unavailable claim"
        return .unavailable reason
      let name ← jStr (← jField j "param")
      if j != Json.mkObj [("param",toJson name)] || name.isEmpty then throw "invalid rigid parameter claim"
      return .param name
private def ClaimType.ground : ClaimType → SourceClaims.Candidate
  | .labels A => .ok A
  | .param _ => .error "rigid parameter outside generic function"
  | .unavailable reason => .error reason

structure Binding where
  name : String
  type : ClaimType
  current : Option (List Nat) := none
  deriving ToJson, FromJson
structure Entry where
  start : Nat
  bindings : List Binding
  deriving ToJson, FromJson
structure Expression where
  pos : Span
  type : ClaimType
  current : Option (List Nat) := none
  deriving ToJson, FromJson
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
    f.expressions.filterMap (fun e => e.current.map (e.pos,·))⟩

/-- The table starts with the primitives and refers only to its own labels. -/
private def validTable (T : SourceTypes.Table) : Bool :=
  SourceTypes.initial.isPrefixOf T && (T.flatMap id |>.flatMap clauseTypes).all (validTy T.length)
private def validType (T : SourceTypes.Table) : ClaimType → Bool
  | .param name => !name.isEmpty
  | .unavailable reason => !reason.isEmpty
  | .labels A => validTy T.length A && A == A.mergeSort (· ≤ ·) && A.eraseDups == A
private def validCurrent (T : SourceTypes.Table) (A : ClaimType) (current : Option (List Nat)) : Bool :=
  match current with
  | none => true
  | some R =>
    (match PositiveRules.expand (SourceTypes.graph T) (A.ground.toOption.getD []) with | [.refs _ []] => true | _ => false) &&
      validType T (.labels R) && R.all SourceTypes.isPrimitive
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
private def exprSites : Fragment.Expr → Sites
  | .var p _ | .lit p _ => ([],[p])
  | .shapeTest p _ _ e | .not p e | .alloc p e | .read p e | .lambda p _ _ e => joinSites ([],[p]) (exprSites e)
  | .withValue p a b _ _ | .write p a b | .unitTest p _ _ _ a b | .coalesce p a b | .logical p _ a b => joinSites ([],[p]) (joinSites (exprSites a) (exprSites b))
  -- An assignment is an expression site, and the name it assigns is not one:
  -- the producer claims the value written, not the location.
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
  | .ret p e | .cst p _ _ e | .mut p _ _ _ e | .effect p e => joinSites ([p.1],[]) (exprSites e)
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
  | .labels A => do
    let rows := PositiveRules.expand (SourceTypes.graph T) A
    if rows != [.bool] && rows != [.boolLit true,.boolLit false] && rows != [.boolLit false,.boolLit true] then
      throw "generic claim requires a rigid parameter or boolean"
    return Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj [("a",toJson "boolean")]])]
private def Function.genericClaims (T : SourceTypes.Table) (c : Function) : Except String Fragment.Claims := do
  if c.entries.any (fun e => e.bindings.any (fun b => b.current.isSome)) ||
      c.expressions.any (fun e => e.current.isSome) then throw "generic claims cannot assert current contents"
  return ⟨c.name,c.namePos,← c.params.mapM (fun b => do return (b.name,← genericType T b.type)),
    ← genericType T c.result,
    ← c.entries.mapM (fun e => do return (e.start,← e.bindings.mapM (fun b => do return (b.name,← genericType T b.type)))),
    ← c.expressions.mapM (fun e => do return (e.pos,← genericType T e.type))⟩

def extract (ast claims : Json) (fileKey : String) : Except String (List SourceRequest) := do
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
  let rs ← decoded.mapM fun (f,tps) => do
    let c ← match d.functions.find? (fun c => c.name == f.name && c.namePos == f.namePos) with
      | some c => pure c
      | none => throw s!"missing claims for '{f.name}'"
    let sites := functionSites f
    if !c.entries.all (fun e => sites.1.contains e.start) ||
        !c.expressions.all (fun e => sites.2.contains e.pos) then
      throw "claim site is not an entry or expression of the named source function"
    if !tps.isEmpty then
      GenericSource.check f tps (← c.genericClaims d.types)
      return none
    return some (← extractNormalizedFn d.types f c.normalized)
  return rs.filterMap id

def checkJson (ast claims : Json) (fileKey : String) (evidence : Json) : Except String Unit := do
  let rs ← extract ast claims fileKey
  let b : Bundle ← decodeStrict evidence
  if checkRequests rs b then return ()
  throw "source evidence does not justify the extracted program and exact claims"

def produceJson (ast claims : Json) (fileKey : String) (fuel : Nat) : Except String Json := do
  let rs ← extract ast claims fileKey
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
    ∃ rs b, extract ast claims fileKey = .ok rs ∧
      decodeStrict evidence = .ok b ∧ checkRequests rs b = true := by
  unfold checkJson at h
  cases he : extract ast claims fileKey with
  | error e => simp only [he] at h; contradiction
  | ok rs =>
    cases hb : (decodeStrict evidence : Except String Bundle) with
    | error e => simp only [he, hb] at h; contradiction
    | ok b =>
      simp only [he, hb] at h
      change (if checkRequests rs b = true then Except.ok () else
        Except.error "source evidence does not justify the extracted program and exact claims") = .ok () at h
      split at h
      · exact ⟨rs,b,rfl,rfl,by assumption⟩
      · contradiction

#print axioms checkJson_checked
end Verification.ExperimentState.SourceClaimJson
