import Verification.Model.Source.SourceClaimJson

/-! Untrusted candidate conversion, reusing the current SKJS type decoder.
Unsupported candidates and sites absent from the lowered source are reported,
never replaced by guessed types. This does not check evidence or complete gaps. -/
namespace Verification.Model.SourceClaimExport
open Lean ProgramTyping SourceClaimJson

private def issue (f : Fragment.Fn) (site raw : Json) (reason : String) : Json :=
  Json.mkObj [("function",toJson f.name),("namePos",toJson f.namePos),
    ("site",site),("raw",raw),("reason",toJson reason)]
private def bindingSite (kind name : String) (start : Nat := 0) : Json :=
  Json.mkObj [("kind",toJson kind),("name",toJson name),("start",toJson start)]

/-- Native encoding ends here. Unavailable candidates remain at their original
sites, so conversion cannot make a failed claim disappear. -/
private def convertFunction (f : Fragment.Fn) (c : Fragment.Claims) (generic : Bool) (modeled : Bool := true) :
    SourceTypes.Lowering SourceTypes.Table ((Function Nat) × List Json) := do
  let mut issues : List Json := []
  let candidate := fun (raw : Json) (point : Bool) => do
    let rigid : Except String (ClaimType Nat) := do
      if (← raw.getObjValAs? Bool "top") then throw "not a rigid parameter"
      let atoms ← raw.getObjValAs? (List Json) "atoms"
      match atoms with
      | [atom] =>
        let name ← atom.getObjValAs? String "name"
        if raw != Json.mkObj [("top",toJson false),("atoms",toJson [Json.mkObj [("a",toJson "param"),("name",toJson name)]])] then
          throw "not a rigid parameter"
        return .param name
      | _ => throw "not a rigid parameter"
    match rigid with
    | .ok A => return (A,none)
    | .error _ =>
      let p ← SourceTypes.attempt (if point then Fragment.translatePoint raw else do
        return ⟨← Fragment.translate raw,none⟩)
      match p with
      | .ok p => return (.labels p.type,p.current)
      | .error e => return (.unavailable e,none)
  let note := fun (site raw : Json) (A : ClaimType Nat) => match A with
    | .unavailable reason => [issue f site raw reason]
    | _ => []
  let mut params := []
  for (name,raw) in c.params do
    let (A,_) ← candidate raw false
    issues := issues ++ note (bindingSite "parameter" name) raw A
    params := params ++ [Binding.mk name A none]
  let (result,_) ← candidate c.ret false
  issues := issues ++ note (toJson "result") c.ret result
  let sites := functionSites f
  let mut entries := []
  for (start,bs) in c.envs do
    if modeled && !sites.1.contains start then
      if generic then throw "claim site is not an entry of the named generic source function"
      issues := issues ++ [issue f (bindingSite "entry" "" start) (toJson bs) "native entry has no lowered source site"]
      continue
    let mut bindings := []
    for (name,raw) in bs do
      -- The native implicit receiver is not a source binding, whatever its
      -- claim: a plain function's `this` is `void`, which the export carries.
      if name == "this" then continue
      let (A,current) ← candidate raw true
      issues := issues ++ note (bindingSite "binding" name start) raw A
      bindings := bindings ++ [Binding.mk name A current]
    entries := entries ++ [Entry.mk start bindings]
  let mut expressions := []
  for (pos,raw) in c.exprs do
    let site := Json.mkObj [("kind",toJson "expression"),("pos",toJson pos)]
    if modeled && !sites.2.contains pos then
      if generic then throw "claim site is not an expression of the named generic source function"
      issues := issues ++ [issue f site raw "native expression has no lowered source site"]
      continue
    let (A,current) ← candidate raw true
    issues := issues ++ note site raw A
    -- The export sidecar reports claims; it never proposes an elimination.
    expressions := expressions ++ [Expression.mk pos A current none]
  return (⟨f.name,f.namePos,params,result,entries,expressions,none⟩,issues)

/-- Returns a sidecar plus explicit omissions. The caller retains the raw export
and collection metadata separately; neither is admitted as proof evidence. -/
def convert (ast claims : Json) (fileKey : String) : Except String Json := do
  if (← jStr (← jField ast "file")) != fileKey then throw "AST file key mismatch"
  -- Conversion is not an acceptance path, but it must share the source gate:
  -- raw source must not smuggle an internal graph label into its output.
  let aliases ← GenericAlias.decodeAliases ast
  sourceGate (ast.getObjValD "functions")
  sourceGate (ast.getObjValD "init")
  -- Only the functions' identities and sites are read here, not their types.
  let ast := ast.setObjVal! "declarations" (Json.mkObj [("roots", Json.arr #[]),
    ("definitions", Json.arr #[]), ("values", Json.arr #[]), ("symbols", Json.arr #[])])
  let selected ← (← claims.getArr?).toList.filterM fun f => do
    return (← jStr (← jField f "file")) == fileKey
  if selected.length != 1 then throw "expected exactly one matching claim file"
  for a in aliases do GenericAlias.admit a
  let decoded ← Fragment.decodeAstWithParams ast
  let fs := decoded.map Prod.fst
  let cs ← Fragment.decodeTypeClaims claims fileKey
  let cs ← cs.mapM (GenericAlias.expandClaims aliases)
  if (fs.map (fun f => (f.name,f.namePos))).eraseDups.length != fs.length ||
      (cs.map (fun f => (f.name,f.namePos))).eraseDups.length != cs.length then
    throw "duplicate function identity"
  if !cs.all (fun c => fs.any (fun f => f.name == c.name && f.namePos == c.namePos)) then
    throw "claim function identity is absent from source"
  let mut functions : List (Function Nat) := []
  let mut omissions : List Json := []
  let mut types := SourceTypes.initial
  for f in fs do
    let some c := cs.find? (fun c => c.name == f.name && c.namePos == f.namePos) |
      omissions := omissions ++ [issue f (toJson "function") .null "function claims unavailable"]
      continue
    if (c.envs.map Prod.fst).eraseDups.length != c.envs.length ||
        (c.exprs.map Prod.fst).eraseDups.length != c.exprs.length ||
        (c.params.map Prod.fst).eraseDups.length != c.params.length ||
        !c.envs.all (fun (_,bs) => (bs.map Prod.fst).eraseDups.length == bs.length) then
      throw "duplicate source claim sites or bindings"
    let ((converted, omitted), grown) ← (convertFunction f c (decoded.any (fun (g,tps) => g.namePos == f.namePos && !tps.isEmpty))).run types
    types := grown
    omissions := omissions ++ omitted
    functions := functions ++ [converted]
  let d : Document SourceTypes.Table Nat := ⟨fileKey,← jStr (← jField ast "sourceSha256"),types,functions,none⟩
  -- Enforce the destination schema, without requiring the claims to be complete.
  let _ ← (decodeDocument d.types (toJson d) : Except String (Document SourceTypes.Table Nat))
  return Json.mkObj [("claims",toJson d),("omissions",toJson omissions)]
/-- Import for inspection when source lowering is unavailable. No source AST is
fabricated and no proof is attempted; verification still requires the real parser.
All sites are kept because there is no lowering with which to associate them. -/
def inspect (claims : Json) (fileKey digest : String) : Except String Json := do
  let cs ← Fragment.decodeTypeClaims claims fileKey
  let mut functions := []
  let mut issues := []
  let mut types := SourceTypes.initial
  for c in cs do
    let identity : Fragment.Fn := ⟨c.name,c.namePos,[],.null,[]⟩
    let ((f,notes),grown) ← (convertFunction identity c false false).run types
    functions := functions ++ [f]
    issues := issues ++ notes
    types := grown
  let d : Document SourceTypes.Table Nat := ⟨fileKey,digest,types,functions,none⟩
  let _ ← (decodeDocument d.types (toJson d) : Except String (Document SourceTypes.Table Nat))
  return Json.mkObj [("claims",toJson d),("omissions",toJson issues)]

end Verification.Model.SourceClaimExport
