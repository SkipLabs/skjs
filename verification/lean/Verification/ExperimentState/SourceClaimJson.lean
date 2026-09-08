import Verification.ExperimentState.SourceExtraction

/-! Strict producer-independent sidecars for the fixed source graph. The external
parser supplies the source fingerprint; this module checks agreement, not hashing
or the parser's semantic correctness. Saved statuses are not part of the schema. -/
namespace Verification.ExperimentState.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction

structure Binding where
  name : String
  type : List Nat
  deriving ToJson, FromJson
structure Entry where
  start : Nat
  bindings : List Binding
  deriving ToJson, FromJson
structure Expression where
  pos : Span
  type : List Nat
  deriving ToJson, FromJson
structure Function where
  name : String
  namePos : Span
  params : List Binding
  result : List Nat
  entries : List Entry
  expressions : List Expression
  deriving ToJson, FromJson
structure Document where
  version : Nat
  profile : String
  file : String
  sourceSha256 : String
  functions : List Function
  deriving ToJson, FromJson

def Function.normalized (f : Function) : SourceClaims.Function :=
  ⟨f.name,f.namePos,f.params.map (fun b => (b.name,.ok b.type)),.ok f.result,
    f.entries.map (fun e => (e.start,e.bindings.map (fun b => (b.name,.ok b.type)))),
    f.expressions.map (fun e => (e.pos,.ok e.type))⟩

private def validType (A : List Nat) : Bool :=
  validTy SourceTypes.types.length A && A == A.mergeSort (· ≤ ·) && A.eraseDups == A
private def validBindings (bs : List Binding) : Bool :=
  (bs.map (·.name)).eraseDups.length == bs.length && bs.all (fun b => !b.name.isEmpty && validType b.type)
private def validSpan (p : Span) : Bool := p.1 < p.2
private def validFunction (f : Function) : Bool :=
  !f.name.isEmpty && validSpan f.namePos && validBindings f.params && validType f.result &&
  (f.entries.map (·.start)).eraseDups.length == f.entries.length &&
  (f.expressions.map (·.pos)).eraseDups.length == f.expressions.length &&
  f.entries.all (fun e => validBindings e.bindings) &&
  f.expressions.all (fun e => validSpan e.pos && validType e.type)

def decode (j : Json) : Except String Document := do
  let d : Document ← decodeStrict j
  if d.version != 1 || d.profile != "stateful-source-19-v1" then throw "unsupported source-claim profile or version"
  if d.sourceSha256.length != 64 || !d.sourceSha256.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
    throw "invalid source fingerprint"
  if !d.functions.all validFunction then throw "invalid source claims: duplicate identity, span, binding or type labels"
  if (d.functions.map (fun f => (f.name,f.namePos))).eraseDups.length != d.functions.length then
    throw "duplicate function claims"
  return d

private abbrev Sites := List Nat × List Span
private def joinSites (a b : Sites) : Sites := (a.1 ++ b.1,a.2 ++ b.2)
private def exprSites : SourceInput.Expr → Sites
  | .var p _ | .lit p _ => ([],[p])
  | .alloc p e | .read p e | .lam p _ _ _ e => joinSites ([],[p]) (exprSites e)
  | .write p a b | .app p a b => joinSites ([],[p]) (joinSites (exprSites a) (exprSites b))
  | .atEnv p e => joinSites ([p.1],[]) (exprSites e)
  | .done _ => ([],[])
  | .seqBody p a b | .letBody p _ _ a b => joinSites ([p.1],[]) (joinSites (exprSites a) (exprSites b))
  | .ifBody p _ a b c => joinSites ([p.1],[]) (joinSites (exprSites a) (joinSites (exprSites b) (exprSites c)))
private partial def stmtSites : SourceInput.Stmt → Sites
  | .ret p e | .cst p _ _ e | .effect p e => joinSites ([p.1],[]) (exprSites e)
  | .loop p c body => joinSites ([p.1],[]) (joinSites (exprSites c)
      (body.foldl (fun s st => joinSites s (stmtSites st)) ([],[])))
  | .ite p c a b =>
    joinSites ([p.1],[]) (joinSites (exprSites c)
      ((a ++ b.getD []).foldl (fun s st => joinSites s (stmtSites st)) ([],[])))

def functionSites (f : SourceInput.Fn) : List Nat × List Span :=
  f.body.foldl (fun s st => joinSites s (stmtSites st)) ([],[])

def extract (ast claims : Json) (fileKey : String) : Except String (List SourceRequest) := do
  let d ← decode claims
  if d.file != fileKey || (← jStr (← jField ast "file")) != fileKey then throw "source claim file identity mismatch"
  if (← jStr (← jField ast "sourceSha256")) != d.sourceSha256 then throw "source claim fingerprint mismatch"
  let fs ← SourceInput.decodeAst ast
  if fs.isEmpty then throw "no source functions to verify"
  if (fs.map (fun f => (f.name,f.namePos))).eraseDups.length != fs.length then throw "duplicate source function identities"
  if fs.length != d.functions.length then throw "function claim count mismatch"
  fs.mapM fun f => do
    let c ← match d.functions.find? (fun c => c.name == f.name && c.namePos == f.namePos) with
      | some c => pure c
      | none => throw s!"missing claims for '{f.name}'"
    let sites := functionSites f
    if !c.entries.all (fun e => sites.1.contains e.start) ||
        !c.expressions.all (fun e => sites.2.contains e.pos) then
      throw "claim site is not an entry or expression of the named source function"
    extractNormalizedFn f c.normalized

def checkJson (ast claims : Json) (fileKey : String) (evidence : Json) : Except String Unit := do
  let rs ← extract ast claims fileKey
  let b : Bundle ← decodeStrict evidence
  if checkRequests rs b then return ()
  throw "source evidence does not justify the extracted program and exact claims"

def produceJson (ast claims : Json) (fileKey : String) (fuel : Nat) : Except String Json := do
  let rs ← extract ast claims fileKey
  let es ← rs.mapM fun r => ExpressionClaims.produce (RequestJson.graph r.toRequest)
    (List.range r.types.length) r.types.length fuel r.obligations
  let cs ← (rs.zip es).mapM fun (r,proofs) => do
    let j ← RequestJson.produceJson (toJson r.toRequest) fuel [] proofs
    decodeResponse r.toRequest j
  let evidence := toJson (Bundle.mk 3 cs es)
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
