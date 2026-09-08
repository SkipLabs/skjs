import Verification.ExperimentState.SourceClaimJson

/-! Untrusted candidate conversion, reusing the current SKJS type decoder.
Unsupported candidates and sites absent from the lowered source are reported,
never replaced by guessed types. This does not check evidence or complete gaps. -/
namespace Verification.ExperimentState.SourceClaimExport
open Lean ProgramTyping SourceClaimJson

private def issue (f : SourceInput.Fn) (site raw : Json) (reason : String) : Json :=
  Json.mkObj [("function",toJson f.name),("namePos",toJson f.namePos),
    ("site",site),("raw",raw),("reason",toJson reason)]
private def bindingSite (kind name : String) (start : Nat := 0) : Json :=
  Json.mkObj [("kind",toJson kind),("name",toJson name),("start",toJson start)]

/-- Returns a sidecar plus explicit omissions. The caller retains the raw export
and collection metadata separately; neither is admitted as proof evidence. -/
def convert (ast claims : Json) (fileKey : String) : Except String Json := do
  if (← jStr (← jField ast "file")) != fileKey then throw "AST file key mismatch"
  let selected ← (← claims.getArr?).toList.filterM fun f => do
    return (← jStr (← jField f "file")) == fileKey
  if selected.length != 1 then throw "expected exactly one matching claim file"
  let fs ← SourceInput.decodeAst ast
  let cs ← SourceInput.decodeTypeClaims claims fileKey
  if (fs.map (fun f => (f.name,f.namePos))).eraseDups.length != fs.length ||
      (cs.map (fun f => (f.name,f.namePos))).eraseDups.length != cs.length then
    throw "duplicate function identity"
  if !cs.all (fun c => fs.any (fun f => f.name == c.name && f.namePos == c.namePos)) then
    throw "claim function identity is absent from source"
  let mut functions : List Function := []
  let mut omissions : List Json := []
  for f in fs do
    let some c := cs.find? (fun c => c.name == f.name && c.namePos == f.namePos) |
      omissions := omissions ++ [issue f (toJson "function") .null "function claims unavailable"]
      continue
    if (c.envs.map Prod.fst).eraseDups.length != c.envs.length ||
        (c.exprs.map Prod.fst).eraseDups.length != c.exprs.length ||
        (c.params.map Prod.fst).eraseDups.length != c.params.length ||
        !c.envs.all (fun (_,bs) => (bs.map Prod.fst).eraseDups.length == bs.length) then
      throw "duplicate source claim sites or bindings"
    let mut params : List Binding := []
    for (name,raw) in c.params do
      match SourceInput.translate raw with
      | .ok A => params := params ++ [⟨name,A⟩]
      | .error e => omissions := omissions ++ [issue f (bindingSite "parameter" name) raw e]
    let result ← match SourceInput.translate c.ret with
      | .ok A => pure (some A)
      | .error e =>
        omissions := omissions ++ [issue f (toJson "result") c.ret e]
        pure none
    if params.length != c.params.length || result.isNone then
      omissions := omissions ++ [issue f (toJson "function") .null "function omitted: signature has unavailable types"]
      continue
    let some result := result | throw "unavailable function result"
    let sites := functionSites f
    let mut entries : List Entry := []
    for (start,bs) in c.envs do
      if !sites.1.contains start then
        omissions := omissions ++ [issue f (bindingSite "entry" "" start) (toJson bs) "entry not present in lowered source"]
        continue
      let mut bindings : List Binding := []
      for (name,raw) in bs do
        match SourceInput.translate raw with
        | .ok A => bindings := bindings ++ [⟨name,A⟩]
        | .error e => omissions := omissions ++ [issue f (bindingSite "binding" name start) raw e]
      entries := entries ++ [⟨start,bindings⟩]
    let mut expressions : List Expression := []
    for (pos,raw) in c.exprs do
      let site := Json.mkObj [("kind",toJson "expression"),("pos",toJson pos)]
      if !sites.2.contains pos then
        omissions := omissions ++ [issue f site raw "expression not present in lowered source"]
        continue
      match SourceInput.translate raw with
      | .ok A => expressions := expressions ++ [⟨pos,A⟩]
      | .error e => omissions := omissions ++ [issue f site raw e]
    functions := functions ++ [⟨f.name,f.namePos,params,result,entries,expressions⟩]
  let d : Document := ⟨1,"stateful-source-75-v1",fileKey,
    ← jStr (← jField ast "sourceSha256"),functions⟩
  -- Enforce the destination schema, without requiring the claims to be complete.
  let _ ← SourceClaimJson.decode (toJson d)
  return Json.mkObj [("claims",toJson d),("omissions",toJson omissions)]
end Verification.ExperimentState.SourceClaimExport
