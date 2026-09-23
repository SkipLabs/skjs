import Verification.Model.Source.Fragment

/-! Imported type declarations are source equations, not rows supplied by a producer.
The producer reserves one empty row per declaration and may refer to those
labels in its own candidate rows. This module fills the reserved rows from the
source equations before any source obligation is extracted. A direct type
reference is expanded only to its first constructor; references under arrays
and object fields stay cyclic graph labels. -/
namespace Verification.Model.ImportedGraph
open Lean PositiveNormalization PositiveRules

private def field (j : Json) (name : String) : Except String Json :=
  j.getObjVal? name

private def arr (j : Json) (name : String) : Except String (Array Json) :=
  do (← field j name).getArr?

private def str (j : Json) (name : String) : Except String String :=
  do (← field j name).getStr?

private def bool (j : Json) (name : String) : Except String Bool :=
  do (← field j name).getBool?

private structure Definition where
  identity : Json
  parameters : Array Json
  expression : Json
  deriving Inhabited

private def definitions (imports : Json) : Except String (Array Definition) := do
  (← arr imports "definitions").mapM fun j => do
    CellClaims.fieldsExactly j ["declaration", "sha256", "parameters", "body", "expression", "references"]
    return ⟨← field j "declaration", ← arr j "parameters", ← field j "expression"⟩

private def findDefinition (ds : Array Definition) (identity : Json) : Except String Nat := do
  let found := (List.range ds.size).filter fun i => ds[i]!.identity == identity
  match found with
  | [i] => return i
  | [] => throw "imported reference has no declaration equation"
  | _ => throw "duplicate imported declaration identity"

private def referenceIndex (ds : Array Definition) (term : Json) : Except String Nat := do
  CellClaims.fieldsExactly term ["k", "reference", "args", "span"]
  if !(← arr term "args").isEmpty then
    throw "parameterized imported references need substitution"
  let reference ← field term "reference"
  findDefinition ds (← field reference "target")

private abbrev Lowering := StateT SourceTypes.Table (Except String)

private def use (clause : Clause (List Nat)) : Lowering Nat := SourceTypes.use clause

mutual
private partial def lowerType (ds : Array Definition) (owner : Nat)
    (term : Json) : Lowering (List Nat) := do
  match ← str term "k" with
  | "atom" =>
    match ← str term "name" with
    | "null" => return [0]
    | "undefined" => return [3]
    | "boolean" => return [1, 2]
    | "number" => return [← use .num]
    | "string" => return [← use .str]
    | "unknown" | "void" => return [← use .top]
    | "never" => return []
    | _ => throw "unsupported imported primitive"
  | "union" =>
    let parts ← arr term "parts"
    let arms ← parts.mapM (lowerType ds owner)
    return arms.toList.flatten.eraseDups.mergeSort (· ≤ ·)
  | "self" =>
    CellClaims.fieldsExactly term ["k", "span"]
    -- Method syntax binds its receiver to the declaration being lowered. A
    -- direct alias expansion changes that owner before reaching this arm.
    if owner >= ds.size then throw "imported method has no containing declaration"
    return [4 + owner]
  | "reference" => return [4 + (← referenceIndex ds term)]
  | "array" =>
    let element ← lowerType ds owner (← field term "element")
    let readonly ← bool term "readonly"
    let store ← use (.list ⟨[], [], some element, readonly⟩ [])
    let row ← if readonly then use (.refs [] [] [(SourceTypes.storeField, [store])])
      else use (.refs [(SourceTypes.storeField, [store])] [] [])
    return [row]
  | "tuple" =>
    CellClaims.fieldsExactly term ["k", "readonly", "required", "optional", "rest", "span"]
    let required ← (← arr term "required").mapM (lowerType ds owner)
    let optional ← (← arr term "optional").mapM (lowerType ds owner)
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure none else some <$> lowerType ds owner restTerm
    let readonly ← bool term "readonly"
    let store ← use (.list ⟨required.toList, optional.toList, rest, readonly⟩ [])
    let row ← if readonly then use (.refs [] [] [(SourceTypes.storeField, [store])])
      else use (.refs [(SourceTypes.storeField, [store])] [] [])
    return [row]
  | "function" =>
    CellClaims.fieldsExactly term ["k", "receiver", "params", "rest", "result", "span"]
    let recv ← field term "receiver"
    let receiver ← if recv == .null then pure [← use .top] else lowerType ds owner recv
    let params ← (← arr term "params").mapM (lowerType ds owner)
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure none else some <$> lowerType ds owner restTerm
    let result ← lowerType ds owner (← field term "result")
    let row : Clause (List Nat) := match rest with
      | none => .arrs [(receiver, params.toList, result)] []
      | some element => .arrs [] [(receiver, params.toList, element, result)]
    return [← use row]
  | "object" =>
    let fs ← (← arr term "fields").mapM fun f => do
      if ← bool f "optional" then throw "optional imported fields need presence semantics"
      let name ← str f "name"
      let value ← lowerType ds owner (← field f "type")
      return (name, value, ← bool f "readonly")
    let names := fs.toList.map (·.1)
    if names.eraseDups.length != names.length then throw "duplicate imported field"
    let index ← field term "stringIndex"
    let indexes ← if index == .null then pure ([] : List (List Nat)) else do
      if !(← bool index "readonly") then throw "mutable imported index needs a fixed contract"
      let value ← lowerType ds owner (← field index "value")
      pure ([value] : List (List Nat))
    let writes := fs.toList.filterMap fun (name, value, readonly) =>
      if readonly then none else some (name, value)
    let views := fs.toList.filterMap fun (name, value, readonly) =>
      if readonly then some (name, value) else none
    let row ← if indexes.isEmpty then use (.refs writes [] views)
      else use (.dict writes [] views indexes)
    return [row]
  | _ => throw "imported source type constructor outside the graph fragment"

private partial def lowerHead (ds : Array Definition) (owner : Nat) (seen : List Nat)
    (term : Json) : Lowering (List (Clause (List Nat))) := do
  match ← str term "k" with
  | "union" =>
    let parts ← arr term "parts"
    let rows ← parts.mapM (lowerHead ds owner seen)
    return rows.toList.flatten.eraseDups
  | "reference" =>
    let i ← referenceIndex ds term
    if seen.contains i then throw "unguarded imported alias cycle"
    lowerHead ds i (i :: seen) ds[i]!.expression
  | _ =>
    let labels ← lowerType ds owner term
    let table ← get
    return labels.flatMap (SourceTypes.graph table)
end

private def fillRows (ds : Array Definition) (candidate : SourceTypes.Table) :
    Except String SourceTypes.Table := do
  if candidate.length < 4 + ds.size then throw "imported graph rows are missing"
  for i in [:ds.size] do
    if candidate[4+i]! != [] then throw "producer supplied an imported declaration equation"
    if !ds[i]!.parameters.isEmpty then
      throw "parameterized imported graph needs substitution"
  let mut table := candidate
  for i in [:ds.size] do
    let (row, expanded) ← (lowerHead ds i [i] ds[i]!.expression).run table
    table := expanded.set (4+i) row
  return table

private partial def rewrite (roots : Array (String × Nat)) (j : Json) : Except String Json := do
  match j with
  | .arr values => return .arr (← values.mapM (rewrite roots))
  | .obj fields =>
    if (j.getObjVal? "a").toOption == some (.str "graph") then
      throw "source cannot state an internal graph label"
    if (j.getObjVal? "a").toOption == some (.str "alias") then
      let name ← str j "name"
      if let some (_, index) := roots.toList.find? (fun p => p.1 == name) then
        if !(← arr j "args").isEmpty then
          throw "parameterized imported aliases need substitution"
        return Json.mkObj [("a", toJson "graph"), ("label", toJson index)]
    let pairs ← fields.toArray.mapM fun (name, value) => do
      return (name, ← rewrite roots value)
    return Json.mkObj pairs.toList
  | _ => return j

/-- Replace only the producer's empty reserved rows with equations derived
from source declarations. The AST copy contains internal graph atoms only after
the original source tree has been checked for them. -/
def prepare (ast : Json) (candidate : SourceTypes.Table) :
    Except String (Json × SourceTypes.Table) := do
  let imports ← field ast "imports"
  CellClaims.fieldsExactly imports ["roots", "definitions", "sources", "mappings"]
  let ds ← definitions imports
  let roots ← (← arr imports "roots").mapM fun root => do
    let name ← str (← field root "binding") "local"
    let i ← findDefinition ds (← field root "declaration")
    return (name, 4+i)
  if (roots.toList.map (·.1)).eraseDups.length != roots.size then
    throw "duplicate imported local type"
  let types ← fillRows ds candidate
  let aliases ← rewrite roots (← field ast "aliases")
  let functions ← rewrite roots (← field ast "functions")
  let empty := Json.mkObj [("roots", toJson ([] : List Json)),
    ("definitions", toJson ([] : List Json)), ("sources", toJson ([] : List Json)),
    ("mappings", toJson ([] : List Json))]
  let ast := ast.setObjVal! "imports" empty
  return (ast.setObjVal! "aliases" aliases |>.setObjVal! "functions" functions, types)

end Verification.Model.ImportedGraph
