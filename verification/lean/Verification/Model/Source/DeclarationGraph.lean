import Verification.Model.Source.Fragment
import Verification.Model.Programs.CertificateProducer

/-! Type declarations, local or imported, are source equations, not rows supplied
by a producer.
The producer reserves one empty row per nullary declaration and may refer to
those labels in its candidate rows. This module fills them from source
equations. Finite ground applications of generic declarations are interned
from their substituted equations; recursive generic applications are refused
until they have application-indexed memo rows. Function annotations are written
in the same source terms, and `prepare` converts each to the claim form the
source readers take. -/
namespace Verification.Model.DeclarationGraph
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
  bases : Array Json
  expression : Json
  deriving Inhabited

private def definitions (document : Json) : Except String (Array Definition) := do
  (← arr document "definitions").mapM fun j => do
    CellClaims.fieldsExactly j ["declaration", "parameters", "bases", "expression"]
    return ⟨← field j "declaration", ← arr j "parameters",
      ← arr j "bases", ← field j "expression"⟩

private def findDefinition (ds : Array Definition) (identity : Json) : Except String Nat := do
  let found := (List.range ds.size).filter fun i => ds[i]!.identity == identity
  match found with
  | [i] => return i
  | [] => throw "reference has no declaration equation"
  | _ => throw "duplicate declaration identity"

private def rowIndex (ds : Array Definition) (i : Nat) : Nat :=
  4 + ((List.range i).filter fun n => ds[n]!.parameters.isEmpty).length

private def nullaryCount (ds : Array Definition) : Nat :=
  (ds.toList.filter fun d => d.parameters.isEmpty).length

private def referenceIndex (ds : Array Definition) (term : Json) : Except String Nat := do
  CellClaims.fieldsExactly term ["k", "reference", "args", "span"]
  let reference ← field term "reference"
  findDefinition ds (← field reference "target")

private abbrev Lowering := StateT SourceTypes.Table (Except String)

/-- A literal type as the claim atom of its value. -/
private def literalAtom (term : Json) : Except String Json := do
  CellClaims.fieldsExactly term ["k", "name", "text", "span"]
  match ← str term "name" with
  | "true" => return Json.mkObj [("a", toJson "booleanlit"), ("v", toJson "true")]
  | "false" => return Json.mkObj [("a", toJson "booleanlit"), ("v", toJson "false")]
  | "number" => return Json.mkObj [("a", toJson "numberlit"), ("v", ← field term "text")]
  | "string" => return Json.mkObj [("a", toJson "stringlit"), ("v", ← field term "text")]
  | _ => throw "unsupported source literal"

private def use (clause : Clause (List Nat)) : Lowering Nat := SourceTypes.use clause

private partial def hasRigidParameter : Json → Bool
  | .obj fields =>
    (fields.toList.lookup "a" == some (.str "param")) ||
      fields.toList.any (fun p => hasRigidParameter p.2)
  | .arr values => values.any hasRigidParameter
  | _ => false

/-- For disjoint plain record fields, a source heritage intersection has the
same contract as one record operand with those fields. Canonicalizing that
case also gives the proposal and the source one graph row. Other combinations
keep the general intersection representation. -/
private def inheritRows (own base : List (Clause (List Nat))) : Except String (List (Clause (List Nat))) := do
  match own, base with
  | [.refs writes [] views], [.refs inherited [] inheritedViews] =>
    let names := (writes ++ views ++ inherited ++ inheritedViews).map Prod.fst
    if names.eraseDups.length != names.length then
      throw "overlapping inherited fields need compatibility checking"
    return [.refs (inherited ++ writes) [] (inheritedViews ++ views)]
  | _, _ =>
    let rows := PositiveNormalization.meetLists own base
    if rows.isEmpty then throw "inherited interface contracts have no representable intersection"
    return rows

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
    | _ => throw "unsupported declaration primitive"
  | "literal" =>
    Fragment.translate (Json.mkObj [("top", toJson false), ("atoms", toJson [← literalAtom term])])
  | "union" =>
    let parts ← arr term "parts"
    let arms ← parts.mapM (lowerType ds owner params seen)
    return arms.toList.flatten.eraseDups.mergeSort (· ≤ ·)
  | "intersection" =>
    -- The positive meet of the operands' clauses: record operands on one
    -- object, function operands as one overloaded callable.
    let parts ← arr term "parts"
    let rows ← parts.mapM fun part => do
      let labels ← lowerType ds owner params seen part
      let table ← get
      return labels.flatMap (SourceTypes.graph table)
    let some first := rows[0]? | throw "empty declaration intersection"
    let meet := rows.toList.drop 1 |>.foldl PositiveNormalization.meetLists first
    if meet.isEmpty then throw "declaration intersection has no representable clause"
    return [← SourceTypes.useRow meet]
  | "parameter" =>
    CellClaims.fieldsExactly term ["k", "index", "span"]
    let i ← (← field term "index").getNat?
    match params[i]? with
    | some value => return value
    | none => throw "declaration parameter index outside application"
  | "self" =>
    CellClaims.fieldsExactly term ["k", "span"]
    -- Method syntax binds its receiver to the declaration being lowered. A
    -- direct alias expansion changes that owner before reaching this arm.
    if owner >= ds.size then throw "method has no containing declaration"
    if !ds[owner]!.parameters.isEmpty then
      throw "generic method receiver needs an application row"
    return [rowIndex ds owner]
  | "reference" =>
    let i ← referenceIndex ds term
    let args ← arr term "args"
    if ds[i]!.parameters.isEmpty then
      if !args.isEmpty then throw "reference has too many type arguments"
      else return [rowIndex ds i]
    if seen.contains i then throw "recursive generic application needs memoized rows"
    let values ← args.mapM (lowerType ds owner params seen)
    let values ← lowerApplication ds i values seen
    if ds[i]!.bases.isEmpty then
      lowerType ds i values (i :: seen) ds[i]!.expression
    else
      (← lowerDefinitionRows ds i values (i :: seen)).mapM use
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
      if ← bool f "optional" then throw "optional declaration fields need presence semantics"
      let name ← str f "name"
      let value ← lowerType ds owner params seen (← field f "type")
      return (name, value, ← bool f "readonly")
    let names := fs.toList.map (·.1)
    if names.eraseDups.length != names.length then throw "duplicate declaration field"
    let index ← field term "stringIndex"
    let indexes ← if index == .null then pure ([] : List (List Nat)) else do
      if !(← bool index "readonly") then throw "mutable declaration index needs a fixed contract"
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
      if (← str call "k") != "function" then throw "call signature is not a function"
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
        throw "callable object with index or readonly field needs a combined clause"
      else if writes.isEmpty then use (.arrs fixed variadic)
      else use (.callable writes [] fixed variadic)
    return [row]
  | _ => throw "source type constructor outside the graph fragment"

private partial def lowerApplication (ds : Array Definition) (i : Nat)
    (supplied : Array (List Nat)) (seen : List Nat) : Lowering (Array (List Nat)) := do
  let d := ds[i]!
  if supplied.size > d.parameters.size then throw "reference has too many type arguments"
  let mut values := supplied
  for p in d.parameters.toList.drop supplied.size do
    CellClaims.fieldsExactly p ["name", "span", "bound", "default"]
    let default ← field p "default"
    if default == .null then throw "type application has missing required argument"
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
      let refusal := s!"type argument does not establish its declared bound for {name} at {span.compress}: {SourceTypes.render table actual} ≤ {SourceTypes.render table upper}"
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
    if seen.contains i then throw "unguarded alias cycle"
    let args ← arr term "args"
    let values ← args.mapM (lowerType ds owner params seen)
    let values ← lowerApplication ds i values seen
    lowerDefinitionRows ds i values (i :: seen)
  | _ =>
    let labels ← lowerType ds owner params seen term
    let table ← get
    return labels.flatMap (SourceTypes.graph table)

private partial def lowerDefinitionRows (ds : Array Definition) (i : Nat)
    (params : Array (List Nat)) (seen : List Nat) :
    Lowering (List (Clause (List Nat))) := do
  let mut rows ← lowerHead ds i params seen ds[i]!.expression
  for base in ds[i]!.bases do
    let inherited ← lowerHead ds i params seen base
    rows ← inheritRows rows inherited
  return rows
end

private def fillRows (ds : Array Definition) (candidate : SourceTypes.Table) :
    Except String SourceTypes.Table := do
  if candidate.length < 4 + nullaryCount ds then throw "declaration graph rows are missing"
  for i in [:ds.size] do
    if ds[i]!.parameters.isEmpty && candidate[rowIndex ds i]! != [] then
      throw "producer supplied a declaration equation"
  let mut table := candidate
  for i in [:ds.size] do
    if ds[i]!.parameters.isEmpty then
      let (row, expanded) ← (lowerDefinitionRows ds i #[] [i]).run table
      table := expanded.set (rowIndex ds i) row
  return table

private def claimType (atoms : List Json) : Json :=
  Json.mkObj [("top", toJson false), ("atoms", toJson atoms)]

private def topClaim : Json :=
  Json.mkObj [("top", toJson true), ("atoms", toJson ([] : List Json))]

private def isTopClaim (claim : Json) : Bool :=
  (claim.getObjVal? "top").toOption == some (.bool true)

private def claimAtoms (claim : Json) : List Json :=
  match (claim.getObjVal? "atoms").toOption with
  | some (.arr atoms) => atoms.toList
  | _ => []

private def graphClaim (labels : List Nat) : Json :=
  claimType (labels.map fun label => Json.mkObj [("a", toJson "graph"), ("label", toJson label)])

private partial def mentionsParameter : Json → Bool
  | .obj fields =>
    (fields.toList.lookup "k" == some (.str "parameter")) ||
      fields.toList.any (fun p => mentionsParameter p.2)
  | .arr values => values.any mentionsParameter
  | _ => false

mutual
/-- A declaration's source equation under its parameters, each bound to a
claim that may mention the enclosing function's rigid binders. Parts without a
parameter are ground and lower to graph rows like any other application; the
parts over parameters are rebuilt as the claim forms the rigid checker reads.
This is the one path for every declaration applied to a rigid argument. -/
private partial def rigidClaim (ds : Array Definition) (owner : Nat) (env : Array Json)
    (seen : List Nat) (term : Json) : Lowering Json := do
  if !mentionsParameter term then
    return graphClaim (← lowerType ds owner #[] seen term)
  match ← str term "k" with
  | "parameter" =>
    CellClaims.fieldsExactly term ["k", "index", "span"]
    let i ← (← field term "index").getNat?
    match env[i]? with
    | some claim => return claim
    | none => throw "declaration parameter index outside application"
  | "union" =>
    let parts ← (← arr term "parts").mapM (rigidClaim ds owner env seen)
    if parts.any isTopClaim then return topClaim
    return claimType (parts.toList.flatMap claimAtoms)
  | "function" =>
    CellClaims.fieldsExactly term ["k", "receiver", "params", "rest", "result", "span"]
    let recv ← field term "receiver"
    let receiver ← if recv == .null then pure topClaim else rigidClaim ds owner env seen recv
    let params ← (← arr term "params").mapM (rigidClaim ds owner env seen)
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure [] else
      pure [("rest", ← rigidClaim ds owner env seen restTerm)]
    let result ← rigidClaim ds owner env seen (← field term "result")
    return claimType [Json.mkObj ([("a", toJson "function"), ("this", receiver),
      ("params", toJson params)] ++ rest ++ [("result", result),
      ("construct", toJson "unknown"), ("array", toJson "unknown")])]
  | "array" =>
    let element ← rigidClaim ds owner env seen (← field term "element")
    return claimType [Json.mkObj [("a", toJson "array"), ("required", toJson ([] : List Json)),
      ("optional", toJson ([] : List Json)), ("rest", element),
      ("readonly", toJson (← bool term "readonly"))]]
  | "tuple" =>
    CellClaims.fieldsExactly term ["k", "readonly", "required", "optional", "rest", "span"]
    let required ← (← arr term "required").mapM (rigidClaim ds owner env seen)
    let optional ← (← arr term "optional").mapM (rigidClaim ds owner env seen)
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure Json.null else
      rigidClaim ds owner env seen restTerm
    return claimType [Json.mkObj [("a", toJson "array"), ("required", toJson required),
      ("optional", toJson optional), ("rest", rest),
      ("readonly", toJson (← bool term "readonly"))]]
  | "object" =>
    CellClaims.fieldsExactly term ["k", "fields", "stringIndex", "calls", "span"]
    if (← field term "stringIndex") != .null || !(← arr term "calls").isEmpty then
      throw "a declaration with call or index signatures applied to a type parameter is outside the fragment"
    let fields ← (← arr term "fields").mapM fun f => do
      if ← bool f "optional" then throw "optional declaration fields need presence semantics"
      let value ← rigidClaim ds owner env seen (← field f "type")
      let write := if ← bool f "readonly" then claimType [] else value
      return Json.mkObj [("name", ← field f "name"), ("optional", toJson false),
        ("read", value), ("write", write)]
    return claimType [Json.mkObj [("a", toJson "record"), ("fields", toJson fields),
      ("indexes", Json.mkObj [("string", toJson "absent"), ("number", toJson "absent"),
        ("symbol", toJson "absent")]),
      ("call", toJson "unknown"), ("construct", toJson "unknown"), ("array", toJson "unknown")]]
  | "reference" =>
    let i ← referenceIndex ds term
    let args ← (← arr term "args").mapM (rigidClaim ds owner env seen)
    expandApplication ds i args seen
  | "self" => throw "a method receiver of a declaration applied to a type parameter is outside the fragment"
  | _ => throw "declaration source constructor applied to a type parameter is outside the fragment"

/-- Apply declaration `i` to claims over the enclosing rigid binders. -/
private partial def expandApplication (ds : Array Definition) (i : Nat)
    (supplied : Array Json) (seen : List Nat) : Lowering Json := do
  let d := ds[i]!
  if seen.contains i then
    throw "recursive generic application over a type parameter needs memoized rows"
  if !d.bases.isEmpty then
    throw "an interface with bases applied to a type parameter is outside the fragment"
  if supplied.size > d.parameters.size then throw "declaration applied to too many type arguments"
  let mut values := supplied
  for p in d.parameters.toList.drop supplied.size do
    CellClaims.fieldsExactly p ["name", "span", "bound", "default"]
    let default ← field p "default"
    if default == .null then throw "declaration application has a missing required type argument"
    values := values.push (← rigidClaim ds i values (i :: seen) default)
  for p in d.parameters do
    if (← field p "bound") != .null then
      throw "a bounded declaration applied to a type parameter needs a rigid bound check"
  rigidClaim ds i values (i :: seen) d.expression
end

private def arrayClaim (required optional : List Json) (rest : Json) (readonly : Bool) : Json :=
  claimType [Json.mkObj [("a", toJson "array"), ("required", toJson required),
    ("optional", toJson optional), ("rest", rest), ("readonly", toJson readonly)]]

/-- The source states no claim: neither a claim-shaped type nor an internal
graph label. -/
private def sourceObject (j : Json) : Except String Unit := do
  if (j.getObjVal? "a").toOption == some (.str "graph") then
    throw "source cannot state an internal graph label"
  if (j.getObjVal? "atoms").isOk then
    throw "a source annotation is a type term, not a claim"

/-- A source annotation as the claim form the source readers take. The terms
are the ones declaration bodies use; a reference resolves to the declaration
TypeScript named, by identity. A ground application is its graph labels, and
one over an enclosing function's binder is its expanded equation. -/
private partial def annotationClaim (ds : Array Definition) (term : Json) : Lowering Json := do
  let recur := annotationClaim ds
  sourceObject term
  match ← str term "k" with
  | "atom" =>
    CellClaims.fieldsExactly term ["k", "name", "span"]
    match ← str term "name" with
    | "unknown" => return topClaim
    | "never" => return claimType []
    | name =>
      if ["null", "undefined", "boolean", "number", "string", "void"].contains name then
        return claimType [Json.mkObj [("a", toJson name)]]
      throw s!"unsupported source atom {name}"
  | "literal" => return claimType [← literalAtom term]
  | "union" =>
    CellClaims.fieldsExactly term ["k", "parts", "span"]
    let parts ← (← arr term "parts").mapM recur
    if parts.any isTopClaim then return topClaim
    return claimType (parts.toList.flatMap claimAtoms).eraseDups
  | "intersection" =>
    -- Conjunction exists only inside a record or function atom.
    CellClaims.fieldsExactly term ["k", "parts", "span"]
    let parts ← (← arr term "parts").mapM recur
    let atoms ← parts.toList.mapM fun part => do
      match isTopClaim part, claimAtoms part with
      | false, [atom] => pure atom
      | _, _ => throw "an intersection operand must be a single type"
    let some head := atoms.head? | throw "empty intersection"
    let shape := (head.getObjVal? "a").toOption
    if atoms.any (fun atom => (atom.getObjVal? "a").toOption != shape) then
      throw "intersection operands must have the same shape"
    if shape != some (.str "record") && shape != some (.str "function") then
      throw "an intersection of anything but records or functions is outside the fragment"
    return claimType [head.setObjVal! "and" (toJson atoms.tail)]
  | "array" =>
    CellClaims.fieldsExactly term ["k", "readonly", "element", "span"]
    return arrayClaim [] [] (← recur (← field term "element")) (← bool term "readonly")
  | "tuple" =>
    CellClaims.fieldsExactly term ["k", "readonly", "required", "optional", "rest", "span"]
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure Json.null else recur restTerm
    return arrayClaim (← (← arr term "required").mapM recur).toList
      (← (← arr term "optional").mapM recur).toList rest (← bool term "readonly")
  | "function" =>
    CellClaims.fieldsExactly term ["k", "receiver", "params", "rest", "result", "span"]
    let recv ← field term "receiver"
    let receiver ← if recv == .null then pure topClaim else recur recv
    let params ← (← arr term "params").mapM recur
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure [] else pure [("rest", ← recur restTerm)]
    return claimType [Json.mkObj ([("a", toJson "function"), ("this", receiver),
      ("params", toJson params)] ++ rest ++ [("result", ← recur (← field term "result")),
      ("construct", toJson "unknown"), ("array", toJson "unknown")])]
  | "object" =>
    CellClaims.fieldsExactly term ["k", "fields", "stringIndex", "calls", "span"]
    if !(← arr term "calls").isEmpty then
      throw "a call signature in a source annotation is outside the fragment"
    let fields ← (← arr term "fields").mapM fun f => do
      CellClaims.fieldsExactly f ["name", "optional", "readonly", "type", "span"]
      if ← bool f "optional" then throw "an optional field needs presence semantics"
      let value ← recur (← field f "type")
      let write := if ← bool f "readonly" then claimType [] else value
      return Json.mkObj [("name", ← field f "name"), ("optional", toJson false),
        ("read", value), ("write", write)]
    let index ← field term "stringIndex"
    if fields.isEmpty && index == .null then throw "a record with no field has no location"
    let signature ← if index == .null then pure [] else do
      CellClaims.fieldsExactly index ["readonly", "value", "span"]
      if !(← bool index "readonly") then throw "expected a readonly string index signature"
      pure [("indexSignature", Json.mkObj [("read", ← recur (← field index "value")),
        ("write", claimType [])])]
    return claimType [Json.mkObj ([("a", toJson "record"), ("fields", toJson fields),
      ("indexes", Json.mkObj [("string", toJson "absent"), ("number", toJson "absent"),
        ("symbol", toJson "absent")])] ++ signature ++
      [("call", toJson "unknown"), ("construct", toJson "unknown"), ("array", toJson "unknown")])]
  | "binder" =>
    CellClaims.fieldsExactly term ["k", "name", "span"]
    return claimType [Json.mkObj [("a", toJson "param"), ("name", ← field term "name")]]
  | "reference" =>
    let index ← referenceIndex ds term
    let args ← (← arr term "args").mapM recur
    -- An application over a rigid binder is its expanded equation; a ground
    -- one is its graph labels, so `Id<boolean>` is exactly `[1, 2]`, the
    -- type a producer claims, not a new row with the same meaning.
    if args.any hasRigidParameter then return ← expandApplication ds index args []
    if ds[index]!.parameters.isEmpty then
      if !args.isEmpty then throw "type application has wrong arity"
      return graphClaim [rowIndex ds index]
    let values ← args.mapM Fragment.translate
    let values ← lowerApplication ds index values []
    let labels ← if ds[index]!.bases.isEmpty then
        lowerType ds index values [index] ds[index]!.expression
      else (← lowerDefinitionRows ds index values [index]).mapM use
    if labels.isEmpty then throw "generic application has no inhabited graph clause"
    return graphClaim labels
  | k => throw s!"declaration syntax '{k}' in a source annotation"

/-- The fields of the Fragment AST that hold a source annotation. -/
private def annotationFields : List String :=
  ["annot", "functionType", "bagType", "type", "result", "bound", "retType"]

/-- Every annotation of the function tree in claim form. -/
private partial def rewrite (ds : Array Definition) (j : Json) : Lowering Json := do
  match j with
  | .arr values => return .arr (← values.mapM (rewrite ds))
  | .obj fields =>
    sourceObject j
    let pairs ← fields.toArray.mapM fun (name, value) => do
      if annotationFields.contains name && value != .null then
        return (name, ← annotationClaim ds value)
      return (name, ← rewrite ds value)
    return Json.mkObj pairs.toList
  | _ => return j

/-- Replace only the producer's empty reserved rows with equations derived
from source declarations. The AST copy contains internal graph atoms only after
the original source tree has been checked for them. -/
def prepare (ast : Json) (candidate : SourceTypes.Table) :
    Except String (Json × SourceTypes.Table) := do
  let document ← field ast "declarations"
  CellClaims.fieldsExactly document ["roots", "definitions"]
  let ds ← definitions document
  let roots ← (← arr document "roots").mapM fun root => do
    let name ← str (← field root "binding") "local"
    let i ← findDefinition ds (← field root "declaration")
    return (name, i)
  if (roots.toList.map (·.1)).eraseDups.length != roots.size then
    throw "duplicate declaration root name"
  let types ← fillRows ds candidate
  let (functions, types) ← (rewrite ds (← field ast "functions")).run types
  let (init, types) ← (rewrite ds (← field ast "init")).run types
  let empty := Json.mkObj [("roots", toJson ([] : List Json)),
    ("definitions", toJson ([] : List Json))]
  let ast := ast.setObjVal! "declarations" empty
  return ((ast.setObjVal! "functions" functions).setObjVal! "init" init, types)

end Verification.Model.DeclarationGraph
