import Verification.ExperimentState.SourceExtraction

/-! Strict producer-independent sidecars for the fixed source graph. The external
parser supplies the source fingerprint; this module checks agreement, not hashing
or the parser's semantic correctness. Saved statuses are not part of the schema. -/
namespace Verification.ExperimentState.SourceClaimJson
open Lean ProgramTyping RequestJson SourceExtraction

structure Binding where
  name : String
  type : List Nat
  current : Option (List Nat) := none
  deriving ToJson, FromJson
structure Entry where
  start : Nat
  bindings : List Binding
  deriving ToJson, FromJson
structure Expression where
  pos : Span
  type : List Nat
  current : Option (List Nat) := none
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

/-- A current-content assertion cannot be turned into an ordinary value type.
Until source observations are connected to heap-aware graph evidence, they fail closed.
The export retains the assertion so a consumer can check it without re-extraction. -/
private def pointCandidate (A : List Nat) (current : Option (List Nat)) : SourceClaims.Candidate :=
  match current with
  | none => .ok A
  | some _ => .error "current-content assertion requires heap-aware source evidence"

def Function.normalized (f : Function) : SourceClaims.Function :=
  ⟨f.name,f.namePos,f.params.map (fun b => (b.name,pointCandidate b.type b.current)),.ok f.result,
    f.entries.map (fun e => (e.start,e.bindings.map (fun b => (b.name,pointCandidate b.type b.current)))),
    f.expressions.map (fun e => (e.pos,pointCandidate e.type e.current))⟩

private def validType (A : List Nat) : Bool :=
  validTy SourceTypes.types.length A && A == A.mergeSort (· ≤ ·) && A.eraseDups == A
private def validCurrent (A : List Nat) (current : Option (List Nat)) : Bool :=
  match current with
  | none => true
  | some R =>
    (match A with | [r] => 3 ≤ r && r < 11 | _ => false) &&
      validType R && R.all (· < 3)
private def validBindings (bs : List Binding) : Bool :=
  (bs.map (·.name)).eraseDups.length == bs.length && bs.all (fun b => !b.name.isEmpty && validType b.type && validCurrent b.type b.current)
private def validSpan (p : Span) : Bool := p.1 < p.2
private def validFunction (f : Function) : Bool :=
  !f.name.isEmpty && validSpan f.namePos && validBindings f.params && f.params.all (fun b => b.current.isNone) && validType f.result &&
  (f.entries.map (·.start)).eraseDups.length == f.entries.length &&
  (f.expressions.map (·.pos)).eraseDups.length == f.expressions.length &&
  f.entries.all (fun e => validBindings e.bindings) &&
  f.expressions.all (fun e => validSpan e.pos && validType e.type && validCurrent e.type e.current)

def decode (j : Json) : Except String Document := do
  -- Version 1 has no assertion fields. Decode it strictly in its own shape by
  -- adding only the known absent fields before the version-2 structural check.
  let legacy := (← (← jField j "version").getNat?) == 1
  let j ← if legacy then do
      if (← jStr (← jField j "profile")) != "stateful-source-75-v1" then
        throw "unsupported source-claim profile or version"
      let addCurrent := fun (x : Json) => do
        let o ← x.getObj?
        if (o.toList.any (fun p => p.1 == "current")) then throw "version 1 cannot carry current-content assertions"
        pure (Json.mkObj (o.toList ++ [("current",Json.null)]))
      let mut root := (← j.getObj?).toList
      let functions ← (← jArr j "functions").mapM fun f => do
        let params ← (← jArr f "params").mapM addCurrent
        let expressions ← (← jArr f "expressions").mapM addCurrent
        let entries ← (← jArr f "entries").mapM fun e => do
          let bindings ← (← jArr e "bindings").mapM addCurrent
          return Json.mkObj ((← e.getObj?).toList.map fun (k,v) =>
            (k,if k == "bindings" then toJson bindings else v))
        return Json.mkObj ((← f.getObj?).toList.map fun (k,v) =>
          (k,if k == "params" then toJson params else if k == "expressions" then toJson expressions
             else if k == "entries" then toJson entries else v))
      root := root.map fun (k,v) => (k,if k == "functions" then toJson functions else v)
      pure (Json.mkObj root)
    else pure j
  let d : Document ← decodeStrict j
  if !(d.version == 1 && d.profile == "stateful-source-75-v1") &&
      !(d.version == 2 && d.profile == "stateful-source-75-v2") then
    throw "unsupported source-claim profile or version"
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
  | .not p e | .alloc p e | .read p e | .lam p _ _ _ e => joinSites ([],[p]) (exprSites e)
  | .write p a b | .app p a b | .nullTest p _ _ a b | .coalesce p a b | .logical p _ a b => joinSites ([],[p]) (joinSites (exprSites a) (exprSites b))
  | .atEnv p e => joinSites ([p.1],[]) (exprSites e)
  | .done _ => ([],[])
  | .seqBody p a b | .letBody p _ _ a b => joinSites ([p.1],[]) (joinSites (exprSites a) (exprSites b))
  | .ifBody p result a b c => joinSites (if result.isSome then ([p.1],[]) else ([],[p])) (joinSites (exprSites a) (joinSites (exprSites b) (exprSites c)))
private partial def stmtSites : SourceInput.Stmt → Sites
  | .brk p | .cont p => ([p.1],[])
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
    r.searchLabels r.types.length fuel r.obligations
  let cs ← (rs.zip es).mapM fun (r,proofs) => do
    let j ← RequestJson.produceJson (toJson r.toRequest) fuel [] proofs r.origins (some r.searchLabels)
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
