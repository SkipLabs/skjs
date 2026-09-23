import Verification.Model.Source.Fragment
import Verification.Model.Programs.CertificateProducer

/-! Imported type declarations are source equations, not rows supplied by a producer.
The producer reserves one empty row per nullary declaration and may refer to
those labels in its candidate rows. This module fills them from source
equations. Finite ground applications of generic declarations are interned
from their substituted equations; recursive generic applications are refused
until they have application-indexed memo rows. -/
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

private def rowIndex (ds : Array Definition) (i : Nat) : Nat :=
  4 + ((List.range i).filter fun n => ds[n]!.parameters.isEmpty).length

private def nullaryCount (ds : Array Definition) : Nat :=
  (ds.toList.filter fun d => d.parameters.isEmpty).length

private def referenceIndex (ds : Array Definition) (term : Json) : Except String Nat := do
  CellClaims.fieldsExactly term ["k", "reference", "args", "span"]
  let reference ← field term "reference"
  findDefinition ds (← field reference "target")

private abbrev Lowering := StateT SourceTypes.Table (Except String)

private def use (clause : Clause (List Nat)) : Lowering Nat := SourceTypes.use clause

mutual
private partial def lowerType (ds : Array Definition) (owner : Nat)
    (params : Array (List Nat)) (seen : List Nat) (term : Json) : Lowering (List Nat) := do
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
    let arms ← parts.mapM (lowerType ds owner params seen)
    return arms.toList.flatten.eraseDups.mergeSort (· ≤ ·)
  | "parameter" =>
    CellClaims.fieldsExactly term ["k", "index", "span"]
    let i ← (← field term "index").getNat?
    match params[i]? with
    | some value => return value
    | none => throw "imported parameter index outside application"
  | "self" =>
    CellClaims.fieldsExactly term ["k", "span"]
    -- Method syntax binds its receiver to the declaration being lowered. A
    -- direct alias expansion changes that owner before reaching this arm.
    if owner >= ds.size then throw "imported method has no containing declaration"
    if !ds[owner]!.parameters.isEmpty then
      throw "generic imported method receiver needs an application row"
    return [rowIndex ds owner]
  | "reference" =>
    let i ← referenceIndex ds term
    let args ← arr term "args"
    if ds[i]!.parameters.isEmpty then
      if !args.isEmpty then throw "imported reference has too many arguments"
      else return [rowIndex ds i]
    if seen.contains i then throw "recursive generic imported application needs memoized rows"
    let values ← args.mapM (lowerType ds owner params seen)
    let values ← lowerApplication ds i values seen
    lowerType ds i values (i :: seen) ds[i]!.expression
  | "array" =>
    let element ← lowerType ds owner params seen (← field term "element")
    let readonly ← bool term "readonly"
    let store ← use (.list ⟨[], [], some element, readonly⟩ [])
    let row ← if readonly then use (.refs [] [] [(SourceTypes.storeField, [store])])
      else use (.refs [(SourceTypes.storeField, [store])] [] [])
    return [row]
  | "tuple" =>
    CellClaims.fieldsExactly term ["k", "readonly", "required", "optional", "rest", "span"]
    let required ← (← arr term "required").mapM (lowerType ds owner params seen)
    let optional ← (← arr term "optional").mapM (lowerType ds owner params seen)
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure none else
      some <$> lowerType ds owner params seen restTerm
    let readonly ← bool term "readonly"
    let store ← use (.list ⟨required.toList, optional.toList, rest, readonly⟩ [])
    let row ← if readonly then use (.refs [] [] [(SourceTypes.storeField, [store])])
      else use (.refs [(SourceTypes.storeField, [store])] [] [])
    return [row]
  | "function" =>
    CellClaims.fieldsExactly term ["k", "receiver", "params", "rest", "result", "span"]
    let recv ← field term "receiver"
    let receiver ← if recv == .null then pure [← use .top] else
      lowerType ds owner params seen recv
    let domains ← (← arr term "params").mapM (lowerType ds owner params seen)
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure none else
      some <$> lowerType ds owner params seen restTerm
    let result ← lowerType ds owner params seen (← field term "result")
    let row : Clause (List Nat) := match rest with
      | none => .arrs [(receiver, domains.toList, result)] []
      | some element => .arrs [] [(receiver, domains.toList, element, result)]
    return [← use row]
  | "object" =>
    CellClaims.fieldsExactly term ["k", "fields", "stringIndex", "calls", "span"]
    let fs ← (← arr term "fields").mapM fun f => do
      if ← bool f "optional" then throw "optional imported fields need presence semantics"
      let name ← str f "name"
      let value ← lowerType ds owner params seen (← field f "type")
      return (name, value, ← bool f "readonly")
    let names := fs.toList.map (·.1)
    if names.eraseDups.length != names.length then throw "duplicate imported field"
    let index ← field term "stringIndex"
    let indexes ← if index == .null then pure ([] : List (List Nat)) else do
      if !(← bool index "readonly") then throw "mutable imported index needs a fixed contract"
      let value ← lowerType ds owner params seen (← field index "value")
      pure ([value] : List (List Nat))
    let writes := fs.toList.filterMap fun (name, value, readonly) =>
      if readonly then none else some (name, value)
    let views := fs.toList.filterMap fun (name, value, readonly) =>
      if readonly then some (name, value) else none
    let mut fixed : List (List Nat × List (List Nat) × List Nat) := []
    let mut variadic : List (List Nat × List (List Nat) × List Nat × List Nat) := []
    for call in ← arr term "calls" do
      CellClaims.fieldsExactly call ["k", "receiver", "params", "rest", "result", "span"]
      if (← str call "k") != "function" then throw "imported call signature is not a function"
      let recv ← field call "receiver"
      let receiver ← if recv == .null then pure [← use .top] else
        lowerType ds owner params seen recv
      let domains ← (← arr call "params").mapM (lowerType ds owner params seen)
      let rest ← field call "rest"
      let result ← lowerType ds owner params seen (← field call "result")
      if rest == .null then fixed := fixed ++ [(receiver, domains.toList, result)]
      else variadic := variadic ++ [(receiver, domains.toList,
        ← lowerType ds owner params seen rest, result)]
    let row ← if fixed.isEmpty && variadic.isEmpty then
        if indexes.isEmpty then use (.refs writes [] views)
        else use (.dict writes [] views indexes)
      else if !indexes.isEmpty || !views.isEmpty then
        throw "imported callable object with index or readonly field needs a combined clause"
      else if writes.isEmpty then use (.arrs fixed variadic)
      else use (.callable writes [] fixed variadic)
    return [row]
  | _ => throw "imported source type constructor outside the graph fragment"

private partial def lowerApplication (ds : Array Definition) (i : Nat)
    (supplied : Array (List Nat)) (seen : List Nat) : Lowering (Array (List Nat)) := do
  let d := ds[i]!
  if supplied.size > d.parameters.size then throw "imported reference has too many arguments"
  let mut values := supplied
  for p in d.parameters.toList.drop supplied.size do
    CellClaims.fieldsExactly p ["name", "span", "bound", "default"]
    let default ← field p "default"
    if default == .null then throw "imported type application has missing required argument"
    values := values.push (← lowerType ds i values (i :: seen) default)
  for index in [:d.parameters.size] do
    let p := d.parameters[index]!
    CellClaims.fieldsExactly p ["name", "span", "bound", "default"]
    let bound ← field p "bound"
    if bound != .null then
      let actual := values[index]!
      let upper ← lowerType ds i (values.toList.take index).toArray (i :: seen) bound
      let table ← get
      let graph := SourceTypes.graph table
      let pool := (actual :: upper :: (List.range table.length).map (fun n => [n])).eraseDups
      let name ← str p "name"
      let span ← field p "span"
      let refusal := s!"imported type argument does not establish its declared bound for {name} at {span.compress}: {SourceTypes.render table actual} ≤ {SourceTypes.render table upper}"
      match CertificateProducer.subtype graph pool actual upper with
      | some proof =>
        if !PositiveCertificates.check graph actual upper proof then
          throw refusal
      | none => throw refusal
  return values

private partial def lowerHead (ds : Array Definition) (owner : Nat)
    (params : Array (List Nat)) (seen : List Nat)
    (term : Json) : Lowering (List (Clause (List Nat))) := do
  match ← str term "k" with
  | "union" =>
    let parts ← arr term "parts"
    let rows ← parts.mapM (lowerHead ds owner params seen)
    return rows.toList.flatten.eraseDups
  | "reference" =>
    let i ← referenceIndex ds term
    if seen.contains i then throw "unguarded imported alias cycle"
    let args ← arr term "args"
    let values ← args.mapM (lowerType ds owner params seen)
    let values ← lowerApplication ds i values seen
    lowerHead ds i values (i :: seen) ds[i]!.expression
  | _ =>
    let labels ← lowerType ds owner params seen term
    let table ← get
    return labels.flatMap (SourceTypes.graph table)
end

private def fillRows (ds : Array Definition) (candidate : SourceTypes.Table) :
    Except String SourceTypes.Table := do
  if candidate.length < 4 + nullaryCount ds then throw "imported graph rows are missing"
  for i in [:ds.size] do
    if ds[i]!.parameters.isEmpty && candidate[rowIndex ds i]! != [] then
      throw "producer supplied an imported declaration equation"
  let mut table := candidate
  for i in [:ds.size] do
    if ds[i]!.parameters.isEmpty then
      let (row, expanded) ← (lowerHead ds i #[] [i] ds[i]!.expression).run table
      table := expanded.set (rowIndex ds i) row
  return table

private partial def rewrite (ds : Array Definition) (roots : Array (String × Nat))
    (j : Json) : Lowering Json := do
  match j with
  | .arr values => return .arr (← values.mapM (rewrite ds roots))
  | .obj fields =>
    if (j.getObjVal? "a").toOption == some (.str "graph") then
      throw "source cannot state an internal graph label"
    if (j.getObjVal? "a").toOption == some (.str "alias") then
      let name ← str j "name"
      if let some (_, index) := roots.toList.find? (fun p => p.1 == name) then
        let args ← (← arr j "args").mapM (rewrite ds roots)
        if ds[index]!.parameters.isEmpty then
          if !args.isEmpty then throw "imported type application has wrong arity"
          return Json.mkObj [("a", toJson "graph"), ("label", toJson (rowIndex ds index))]
        let values ← args.mapM Fragment.translate
        let values ← lowerApplication ds index values []
        let labels ← lowerType ds index values [index] ds[index]!.expression
        match labels with
        | [label] => return Json.mkObj [("a", toJson "graph"), ("label", toJson label)]
        | _ => throw "generic imported application needs one graph clause"
    let pairs ← fields.toArray.mapM fun (name, value) => do
      return (name, ← rewrite ds roots value)
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
    return (name, i)
  if (roots.toList.map (·.1)).eraseDups.length != roots.size then
    throw "duplicate imported local type"
  let types ← fillRows ds candidate
  let (aliases, types) ← (rewrite ds roots (← field ast "aliases")).run types
  let (functions, types) ← (rewrite ds roots (← field ast "functions")).run types
  let empty := Json.mkObj [("roots", toJson ([] : List Json)),
    ("definitions", toJson ([] : List Json)), ("sources", toJson ([] : List Json)),
    ("mappings", toJson ([] : List Json))]
  let ast := ast.setObjVal! "imports" empty
  return (ast.setObjVal! "aliases" aliases |>.setObjVal! "functions" functions, types)

end Verification.Model.ImportedGraph
