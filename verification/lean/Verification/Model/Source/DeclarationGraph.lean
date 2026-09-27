import Verification.Model.Source.Fragment
import Verification.Model.Programs.CertificateProducer

/-! Type declarations, local or imported, are source equations, not rows supplied
by a producer.
The producer reserves one empty row per nullary declaration and may refer to
those labels in its candidate rows. This module fills them from source
equations. Ground applications of generic declarations are lowered from their
substituted equations; one with methods, which is how a declaration recurs, is
one row per declaration and arguments for the module (`Memo`), so a recursive
family of applications is a finite graph. Function annotations are written
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

/-- An object term's index signatures, by the keys each constrains: its
`stringIndex`, and the `numberIndex` and `symbolIndex` a term states only when
it has them. -/
private def indexSignatures (term : Json) : List (String × IndexKeys × Json) :=
  [("stringIndex", IndexKeys.strings, term.getObjVal? "stringIndex"),
   ("numberIndex", .numeric, term.getObjVal? "numberIndex"),
   ("symbolIndex", .symbols, term.getObjVal? "symbolIndex")].filterMap
    fun (name, keys, index) => match index with
      | .ok .null | .error _ => none
      | .ok index => some (name, keys, index)

/-- The members an object term has: the number and symbol indexes only when
present. -/
private def objectMembers (term : Json) : List String :=
  ["k", "fields", "stringIndex", "calls", "span"] ++
    ((indexSignatures term).map (·.1)).filter (· != "stringIndex") ++
    if (term.getObjVal? "prototype").toOption.isSome then ["prototype"] else []

/-- Whether an object term has a number or symbol index. -/
private def keyedIndexes (term : Json) : Bool :=
  (indexSignatures term).any (·.1 != "stringIndex")

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

/-- The nullary declaration whose row is `l`, if any. -/
private def nullaryAt (ds : Array Definition) (l : Nat) : Option Nat :=
  ((List.range ds.size).filter fun i => ds[i]!.parameters.isEmpty)[l - 4]?.filter fun _ => 4 ≤ l

/-- `ArrayProto`'s identity: the synthetic declaration array types' prototype
view names. -/
private def arrayProtoIdentity : Json :=
  Json.mkObj [("module", "skjs/array-prototype"), ("name", "ArrayProto"), ("span", toJson [0, 0])]

/-- The excluded array keys: `constructor` and the keys `ArrayProto`'s declaration names, spelled as its row's are
(`SourceTypes.arrayExcludedKeys`): an array owns none of them. Read from the
declaration, since arrays are lowered before, and while, its row is;
`prepare` checks the row names the same keys. -/
private def arrayExcludedKeys (ds : Array Definition) : Except String (List PropKey) := do
  let some d := ds[0]? | return SourceTypes.arrayExcludedKeys.ofKeys []
  if d.identity != arrayProtoIdentity then return SourceTypes.arrayExcludedKeys.ofKeys []
  let names ← (← arr d.expression "fields").mapM fun f => do PropKey.decode (← field f "name")
  return SourceTypes.arrayExcludedKeys.ofKeys names.toList

private def referenceIndex (ds : Array Definition) (term : Json) : Except String Nat := do
  CellClaims.fieldsExactly term ["k", "reference", "args", "span"]
  let reference ← field term "reference"
  findDefinition ds (← field reference "target")

/-- A generic application given a row: its declaration, its arguments, and
their key (`Memo.key`). -/
private structure Given where
  declaration : Nat
  args : Array (List Nat)
  key : Array (List (Nat ⊕ RequestJson.Row))
  row : Nat

/-- What lowering keeps beside the table, for every lowering of the module. -/
private structure Memo where
  /-- The generic applications given rows. An application with methods gets
  its row when first lowered; a producer's reserved row is its application's
  from the start. -/
  applications : List Given := []
  /-- The value binder rows of generic methods with a ground declared bound,
  and that bound: a fact of the binder row, as its name fixes the method and
  position, and ground terms lower alike wherever they are lowered. -/
  binders : List (Nat × List Nat) := []
  /-- The producer's reserved intersections: operand types and row. A ground
  intersection of the same operands is that row, filled when first met, so the
  producer's name for it and every lowering's are one row. -/
  meets : List (List (List Nat) × Nat) := []
  /-- The rows below it are the primitives' and the nullary declarations'. -/
  floor : Nat := 4
  /-- The nullary declarations whose equations are being lowered: an
  intersection naming one of them waits for its row (`pending`). -/
  lowering : List Nat := []
  /-- Ground intersections met before an operand's row was filled, each with
  the row given it and its operands: a declaration being lowered, or a
  recursive application being lowered, met inside its own equation
  (`TreeNode<T> & TreeLeaf<T>` in `TreeLeaf<T>`'s). Each row is the meet of
  its operands' clauses, filled once they are (`settle`). -/
  pending : List (Nat × List (List Nat)) := []

private abbrev Lowering := StateT Memo SourceTypes.Lowering

/-- A type up to rows with identical clauses, which denote the same type
(`SourceTypes.canonical`): each label is its row, a producer's row for
`number` and a declaration's `type int = number` alike. An application's row
is only its label, as is an empty row, reserved and not yet filled. -/
private def Memo.key (m : Memo) (T : SourceTypes.Table) (A : List Nat) : List (Nat ⊕ RequestJson.Row) :=
  (A.map fun l => match T[l]? with
    | some (RequestJson.Row.clauses []) | none => .inl l
    | some r => if m.applications.any (·.row == l) then .inl l else .inr r).eraseDups

private def sameKey (a b : List (Nat ⊕ RequestJson.Row)) : Bool :=
  a.all (b.contains ·) && b.all (a.contains ·)

/-- The row given to declaration `i` at arguments `values`, if any. -/
private def Memo.row (m : Memo) (T : SourceTypes.Table) (i : Nat) (values : Array (List Nat)) :
    Option Nat :=
  let k := values.map (m.key T)
  (m.applications.find? fun g => g.declaration == i && g.key.size == k.size &&
    (g.key.zip k).all fun (a, b) => sameKey a b).map (·.row)

/-- Give declaration `i` at arguments `values` the row `row`. -/
private def Memo.give (m : Memo) (T : SourceTypes.Table) (i : Nat) (values : Array (List Nat))
    (row : Nat) : Memo :=
  { m with applications := ⟨i, values, values.map (m.key T), row⟩ :: m.applications }

/-- The keys again, once rows they name have been filled. -/
private def Memo.rekey (m : Memo) (T : SourceTypes.Table) : Memo :=
  { m with applications := m.applications.map fun g => { g with key := g.args.map (m.key T) } }

/-- A literal type as the claim atom of its value. -/
private def literalAtom (term : Json) : Except String Json := do
  CellClaims.fieldsExactly term ["k", "name", "text", "span"]
  match ← str term "name" with
  | "true" => return Json.mkObj [("a", toJson "booleanlit"), ("v", toJson "true")]
  | "false" => return Json.mkObj [("a", toJson "booleanlit"), ("v", toJson "false")]
  | "number" => return Json.mkObj [("a", toJson "numberlit"), ("v", ← field term "text")]
  | "string" => return Json.mkObj [("a", toJson "stringlit"), ("v", ← field term "text")]
  | "bigint" => return Json.mkObj [("a", toJson "bigintlit"), ("v", ← field term "text")]
  | _ => throw "unsupported source literal"

/-- The row of a union of clauses: the first row with exactly those clauses
that is not a declaration's, or a new one. A declaration's row is its name
(`type int = number`): a type lowered from source is the same row wherever
it is lowered, whether that declaration's row was filled yet or not, and
the row a producer interned for it. -/
private def useRow (row : List (Clause (List Nat))) : Lowering Nat := do
  let floor := (← get).floor
  modifyGetThe SourceTypes.Table fun T =>
    match (List.range T.length).find? fun k => (k < 4 || floor ≤ k) && T[k]? == some (.clauses row) with
    | some k => (k, T)
    | none => (T.length, T ++ [.clauses row])

private def use (clause : Clause (List Nat)) : Lowering Nat := useRow [clause]

private partial def hasRigidParameter : Json → Bool
  | .obj fields =>
    (fields.toList.lookup "a" == some (.str "param")) ||
      fields.toList.any (fun p => hasRigidParameter p.2)
  | .arr values => values.any hasRigidParameter
  | _ => false

/-- Whether a source term has a subterm of kind `k`. -/
private partial def mentionsKind (k : String) : Json → Bool
  | .obj fields => fields.toList.lookup "k" == some (.str k) ||
      fields.toList.any (fun p => mentionsKind k p.2)
  | .arr values => values.any (mentionsKind k)
  | _ => false

/-- The type parameters a source term names. -/
private partial def sourceBinderNames : Json → List String
  | .obj fields =>
    let here := if fields.toList.lookup "k" == some (.str "binder") then
      match fields.toList.lookup "name" with
      | some (.str n) => [n]
      | _ => []
    else []
    (here ++ fields.toList.flatMap fun (_, v) => sourceBinderNames v).eraseDups
  | .arr values => (values.toList.flatMap sourceBinderNames).eraseDups
  | _ => []

/-- Whether a declaration's equation has methods, whose receiver is the
declaration itself. -/
private def mentionsSelf : Json → Bool := mentionsKind "self"

/-- The declarations a term references. -/
private partial def references (ds : Array Definition) : Json → List Nat
  | .obj kvs =>
    let here := if (kvs.toList.lookup "k") == some (.str "reference") then
      (referenceIndex ds (.obj kvs)).toOption.toList else []
    (here ++ kvs.toList.flatMap fun (_, v) => references ds v).eraseDups
  | .arr xs => (xs.toList.flatMap (references ds)).eraseDups
  | _ => []

/-- A generic declaration whose equation reaches itself through references,
`type List<T> = null | { head: T; tail: List<T> }`: its application is a row
of its own, as an application with methods is, so the equation is lowered
once, not unrolled without end. -/
private def recursiveDeclaration (ds : Array Definition) (i : Nat) : Bool := Id.run do
  let mut known := references ds ds[i]!.expression
  for _ in List.range (ds.size + 1) do
    let next := (known ++ known.flatMap fun j =>
      match ds[j]? with
      | some d => references ds d.expression ++ d.bases.toList.flatMap (references ds)
      | none => []).eraseDups
    if next.length == known.length then break
    known := next
  return known.contains i

/-- A term that names no type parameter, method binder or receiver: it lowers
to the same labels wherever it is lowered. -/
private def groundTerm (t : Json) : Bool :=
  !mentionsKind "parameter" t && !mentionsKind "binder" t && !mentionsKind "self" t

/-- An intersection whose operands share no clause: no value has both shapes
(`string & { a: number }`, a function and an array), or a key one owns is one
another's bound excludes (`number[] & { map: number }`). TypeScript keeps some
such types (a branded primitive), which the model's values do not inhabit. -/
private def emptyMeet : String :=
  "the intersection is empty: its operands have no value in common (no value has two shapes, and an array owns no key its prototype provides), and an empty intersection is refused rather than verified vacuously"

/-- Two operands' clauses as TypeScript meets them: the model's meet
(`PositiveNormalization.meetLists`), except that a record of invariant fields
met with a function type is the function carrying those fields, a `callable`.
A record type's clause is a plain object, which no function is, so the model's
meet of the two is empty; TypeScript's record type also holds functions with
those properties, and its intersection with a function type is exactly those
functions (`(() => void) & { a: number }`). A record with readonly or optional
fields or methods has no such clause: that pair is dropped, and a meet left
with nothing is refused for it; an array owns its store, so a function is
never one. -/
private def sourceMeetLists (A B : List (Clause (List Nat))) : Except String (List (Clause (List Nat))) := do
  let plainRecord (c : Clause (List Nat)) : Bool := match c with
    | .refs .. => !c.presentKeys.contains CallArguments.arrayStoreField
    | .dict .. => true
    | _ => false
  let calls (c : Clause (List Nat)) : Bool := match c with
    | .arrs .. | .callable .. => true
    | _ => false
  let pair (a b : Clause (List Nat)) : List (Clause (List Nat)) :=
    match a, b with
    | .refs f fs [] [] [] [], .arrs L S | .arrs L S, .refs f fs [] [] [] [] => [.callable f fs L S]
    | .refs f fs [] [] [] [], .callable c cs L S | .callable c cs L S, .refs f fs [] [] [] [] =>
      [.callable (f ++ c) (fs ++ cs) L S]
    | a, b => (PositiveNormalization.meet a b).filter Clause.consistent
  let pairs := A.flatMap fun a => B.map fun b => (a, b)
  let met := pairs.flatMap fun (a, b) => pair a b
  -- A pair no clause states, a callable with readonly or optional fields,
  -- methods or an index, is dropped as the model's meet drops it; where
  -- nothing else is left, that pair is the reason, not emptiness.
  if met.isEmpty && pairs.any (fun (a, b) => (plainRecord a && calls b) || (calls a && plainRecord b)) then
    throw "the intersection of a function type and a record with readonly or optional fields, methods or an index is a callable with them, which no clause states"
  return met

/-- An interface's contract is the meet of its own members with each base's:
record operands on one object, whose named fields and index views are one
record (`meet`, `ReferenceConjunctions.flatten`), so a dictionary's index
applies to every present field, the named ones included (`interface C extends
NamedEagerCollections`), and the read rules see the named members. The
interface's own members come first, so where one overrides a base's member of
the same key, the read rules find the interface's. -/
private def inheritRows (own base : List (Clause (List Nat))) : Except String (List (Clause (List Nat))) := do
  let rows ← sourceMeetLists own base
  if rows.isEmpty then throw emptyMeet
  return rows

/-- Uses of one free method binder. A nested scheme with the same binder
shadows it; a pack occurrence is the direct operand of a pack rest. -/
structure BinderUse where
  value : Bool := false
  pack : Bool := false
  deriving BEq, Repr, Inhabited

private def BinderUse.merge (a b : BinderUse) : BinderUse :=
  ⟨a.value || b.value, a.pack || b.pack⟩

partial def binderUse (name : String) : Json → BinderUse
  | .obj fields =>
    let fields := fields.toList
    if fields.lookup "k" == some (.str "binder") then
      ⟨fields.lookup "name" == some (.str name), false⟩
    else if fields.lookup "k" == some (.str "pack") then
      match fields.lookup "of" with
      | some (.obj operand) =>
        if operand.toList.lookup "k" == some (.str "binder") then
          ⟨false, operand.toList.lookup "name" == some (.str name)⟩
        else binderUse name (.obj operand)
      | some other => binderUse name other
      | none => {}
    else if fields.lookup "k" == some (.str "scheme") &&
        (match fields.lookup "binders" with
          | some (.arr bs) => bs.any fun b => (b.getObjValAs? String "name").toOption == some name
          | _ => false) then {}
    else fields.foldl (fun acc field => acc.merge (binderUse name field.2)) {}
  | .arr terms => terms.foldl (fun acc term => acc.merge (binderUse name term)) {}
  | .null | .bool _ | .num _ | .str _ => {}

/-- The source role stays with a binder until its rows are emitted. A value
occurrence cannot accidentally retrieve the row of an argument-list binder. -/
private inductive BinderBinding where
  | value (row : Nat)
  | pack (row : Nat)

private def BinderBinding.row : BinderBinding → Nat
  | .value row | .pack row => row

/-- The declarations being expanded inline since the innermost application
row, innermost first. -/
private structure Visit where
  declarations : List Nat := []
  /-- The binders of the generic methods being lowered, innermost first. -/
  binders : List (String × BinderBinding) := []
  /-- The key of the member whose scheme is lowered next, when it is a
  generic method's: its binder rows are the member's
  (`quantified members`, below). -/
  member : Option String := none

/-- Entering a declaration's equation: its terms see none of the enclosing
methods' binders, as type parameters are lexically scoped. -/
private def Visit.enter (v : Visit) (i : Nat) : Visit :=
  { v with declarations := i :: v.declarations, binders := [], member := none }
private def Visit.contains (v : Visit) (i : Nat) : Bool := v.declarations.contains i

/-! ### Generic methods

A generic method's type is a scheme row whose binders are parameter rows. A
generic declaration's methods mention its applications at their own binders
(`Promise<T>`'s `then<R1>` returns `Promise<R1>`, whose `then` binds another
`R1`, ...). Binder rows are shared, by name, so that unfolding closes up: a
method's binders take the least **colour** not free in the arguments of the
application it belongs to, and a binder row is keyed by the method, the
binder's position and its colour. `Promise<R1ᵃ>`'s `then` then binds `R1ᵇ`,
`Promise<R1ᵇ>`'s binds `R1ᵃ`, and the application memo finds `Promise<R1ᵃ>`
again. The colours never capture: a binder never takes a colour free in what
its signatures mention from outside.

An application with methods is one row per declaration and arguments, for the
whole module (`Memo.applications`), and its equation is lowered from that row
alone: what it becomes depends on the application, never on the path that
reached it first. So a recursive family of applications closes into a finite
graph in which every application has its whole equation. Past the colour
budget, and at arguments that keep growing (`Pair<[T, U]>`, refused by the
argument budget), lowering refuses the declaration. Limits never weaken a contract. -/

/-- How many colours generic methods' binders may take. -/
private def colourBudget : Nat := 4

/-- How many times a declaration without methods may be expanded inline within
one application row's equation at different arguments. -/
private def applicationDepth : Nat := 3

/-- How many rows the arguments of an application with methods may reach, an
application among them counting its own arguments. Arguments that keep growing
(`Pair<[T, U]>`'s `m<V>(): Pair<[[T, U], V]>`) pass it; a finite family of
applications stays below it. -/
private def argumentBudget : Nat := 32

/-- The rows the types `A` reach, until more than `limit` are found: an
application row reaches its arguments, not its equation, which may still be
being lowered; a declaration's row (below `floor`), a primitive's and a
binder's reach nothing further. A function of the types, not of the path
lowering them. -/
private def reach (m : Memo) (T : SourceTypes.Table) (floor limit : Nat) (A : List Nat) : List Nat :=
  let next (l : Nat) : List Nat :=
    match m.applications.find? (·.row == l) with
    | some g => g.args.toList.flatten
    | none =>
      if l < floor then [] else match T[l]? with
        | some (.clauses cs) => cs.flatMap fun c => c.operands.flatten
        | some (.scheme _ sigs bounds rests) =>
          sigs.flatMap (fun (r, ps, res) => r ++ ps.flatten ++ res) ++ bounds.flatMap (·.2) ++
            rests.flatMap (fun (r, ps, p, res) => r ++ ps.flatten ++ p ++ res)
        | some (.meet p cs ps) => p :: ps ++ cs.flatMap fun c => c.operands.flatten
        | _ => []
  let rec go : Nat → List Nat → List Nat → List Nat
    | 0, seen, _ => seen
    | _, seen, [] => seen
    | fuel + 1, seen, l :: todo =>
      if seen.length > limit then seen
      else if seen.contains l then go fuel seen todo
      else go fuel (seen ++ [l]) (todo ++ next l)
  go ProgramTyping.closureFuel [] A

/-- The colours of the method's binder rows `labels` reach: the rows whose
name, before its colour, `mine` accepts. A binder a nested scheme binds counts
too: the colours taken are over-approximated, never missed. Another method's
binders are other rows whatever their colour, so they capture nothing and take
no colour: a family of applications then closes, and is truncated, alike at
every instance of another method's binders. -/
private def freeColours (m : Memo) (T : SourceTypes.Table) (floor : Nat) (mine : String → Bool)
    (labels : List Nat) : List Nat :=
  (reach m T floor ProgramTyping.closureFuel labels).filterMap fun p => match T[p]? with
    | some (RequestJson.Row.param _ n _) =>
      match n.splitOn "^" with
      | [head, c] => if mine head then c.toNat? else none
      | _ => none
    | _ => none

/-- The one row of the binder named `name`, shared by every lowering. -/
private def paramRow (name : String) (kind : PositiveGraphs.ParameterKind) : Lowering Nat :=
  modifyGetThe SourceTypes.Table fun T =>
  match T.findIdx? (fun r => match r with | RequestJson.Row.param _ n k => n == name && k == kind | _ => false) with
  | some i => (i, T)
  | none => (T.length, T ++ [.param T.length name kind])

/-- A scheme row, interned. -/
private def schemeRow (bs : List Nat) (sigs : List (List Nat × List (List Nat) × List Nat))
    (bounds : List (Nat × List Nat))
    (rests : List (List Nat × List (List Nat) × List Nat × List Nat) := []) :
    Lowering Nat := modifyGetThe SourceTypes.Table fun T =>
  let r := RequestJson.Row.scheme bs sigs bounds rests
  match T.idxOf? r with
  | some i => (i, T)
  | none => (T.length, T ++ [r])

/-- The positive meet of ground operands' clauses, folded from the right:
record operands on one object, function operands as one overloaded callable.
An operand with a row that is not a clause row has no clauses to meet, so it
is refused rather than dropped. -/
private def groundMeet (parts : List (List Nat)) : Lowering (List (Clause (List Nat))) := do
  let table ← getThe SourceTypes.Table
  let graph := SourceTypes.graph table
  if !parts.all (graph.plainTy ·) then
    throw "an intersection operand holding a type parameter is outside the graph fragment"
  let rows := parts.map (·.flatMap graph)
  let some last := rows.getLast? | throw "empty declaration intersection"
  let meet ← (rows.dropLast.foldrM sourceMeetLists last : Except String _)
  if meet.isEmpty then throw emptyMeet
  return meet

/-- A row not yet filled: a nullary declaration's, a reserved application's
or a waiting intersection's, empty until its equation is lowered. -/
private def unfilled (T : SourceTypes.Table) (l : Nat) : Bool :=
  4 ≤ l && T[l]? == some (RequestJson.Row.clauses [])

/-- A ground intersection with an operand not yet filled: its own row, the
same for the same operands, filled by `settle` once they are. -/
private def waitingMeet (parts : List (List Nat)) : Lowering Nat := do
  if let some (row, _) := (← get).pending.find? (·.2 == parts) then return row
  let row ← modifyGetThe SourceTypes.Table fun T => (T.length, T ++ [.clauses []])
  modify fun m => { m with pending := m.pending ++ [(row, parts)] }
  return row

/-- Fill every waiting intersection whose operands are filled, until none is
left that can be: one filled may be another's operand. -/
private def settle : Lowering Unit := do
  for _ in [:(← get).pending.length] do
    let T ← getThe SourceTypes.Table
    let (ready, waiting) := (← get).pending.partition fun (_, parts) =>
      !parts.any (·.any (unfilled T))
    if ready.isEmpty then return
    modify fun m => { m with pending := waiting }
    for (row, parts) in ready do
      let cs ← groundMeet parts
      modifyThe SourceTypes.Table (·.set row (.clauses cs))

/-- Every waiting intersection filled: a row left empty would read as no
value at all. -/
private def complete : Lowering Unit := do
  settle
  if !(← get).pending.isEmpty then
    throw "an intersection's operands were never lowered"

/-- An intersection's row. A value binder among the operands, an operand
alone, with ground others, is a meet row: the binder within the meet of the
others (`V & DepSafe`), whose instance at `V := T` is the meet of `T` with them
(`meetOk`), which is what lowering `T & DepSafe` itself gives when the binder
is the first operand. Several binders, or a binder with another binder's meet
row (a binder bounded by another, `U extends T`, whose row is `U ⊓ T`), are
the meet of their parameters within the ground operands' clauses, or within
every value when there are none (`SourceTypes.dependentMeet`). Any other
intersection is the meet of its operands' clauses. -/
private def meetRow (parts : List (List Nat)) : Lowering (List Nat) := do
  let table ← getThe SourceTypes.Table
  let graph := SourceTypes.graph table
  let binders : List Nat := parts.filterMap fun A => match A with
    | [x] => if graph.parameterKinds x == some .value then some x else none
    | _ => none
  -- An operand that is a binder's meet row stands for its parameters and
  -- its clauses.
  let meetOperands : List (Nat × List (Clause (List Nat)) × List Nat) := parts.filterMap fun A =>
    match A with
    | [x] => match (table[x]? : Option RequestJson.Row) with
      | some (.meet p cs qs) => some (p, cs, qs)
      | _ => none
    | _ => none
  match binders.eraseDups, meetOperands with
  | [], [] =>
    let m ← get
    let reserved := m.meets.find? fun (ps, _) => ps.length == parts.length &&
      (ps.zip parts).all fun (a, b) => sameKey (m.key table a) (m.key table b)
    -- An operand whose equation is still being lowered: the meet waits for
    -- it, in the producer's reserved row if it has one.
    let waiting := parts.any (·.any (unfilled table))
    match reserved with
    | some (_, row) =>
      if table[row]? == some (.clauses []) then
        if waiting then
          if !m.pending.any (·.1 == row) then
            modify fun m => { m with pending := m.pending ++ [(row, parts)] }
        else
          let cs ← groundMeet parts
          modifyThe SourceTypes.Table (·.set row (.clauses cs))
      return [row]
    | none =>
      if waiting then return [← waitingMeet parts]
      return [← useRow (← groundMeet parts)]
  | [x], [] =>
    let others := parts.filter (· != [x])
    if others.isEmpty then return [x]
    let cs ← groundMeet others
    -- A producer's reserved row for this intersection, a generic unit's
    -- bounded binder among them, is that meet row.
    let m ← get
    let reserved := m.meets.find? fun (ps, _) => ps == parts
    if let some (_, row) := reserved then
      if table[row]? == some (.clauses []) then
        modifyThe SourceTypes.Table (·.set row (.meet x cs))
        return [row]
    modifyGetThe SourceTypes.Table fun T =>
      let r := RequestJson.Row.meet x cs
      match T.idxOf? r with
      | some i => ([i], T)
      | none => ([T.length], T ++ [r])
  | bs, ms =>
    let params := (bs ++ ms.flatMap fun (p, _, qs) => p :: qs).eraseDups
    let some x := params.head? | throw "empty declaration intersection"
    let isMeet (y : Nat) : Bool := match (table[y]? : Option RequestJson.Row) with
      | some (.meet ..) => true
      | _ => false
    let others := parts.filter fun A => match A with
      | [y] => !bs.contains y && !isMeet y
      | _ => true
    let clauseSets ← do
      let ground ← if others.isEmpty then pure [] else pure [← groundMeet others]
      pure (ground ++ (ms.map (·.2.1)).filter (· != [.top]))
    let cs := match clauseSets.getLast? with
      | none => [.top]
      | some last => clauseSets.dropLast.foldr PositiveNormalization.meetLists last
    if cs.isEmpty then throw emptyMeet
    let r := RequestJson.Row.meet x cs params.tail
    let m ← get
    let reserved := m.meets.find? fun (ps, _) => ps == parts
    if let some (_, row) := reserved then
      if table[row]? == some (.clauses []) then
        modifyThe SourceTypes.Table (·.set row r)
        return [row]
    return [← (SourceTypes.internRow r : SourceTypes.Lowering Nat)]

mutual
/-- A rest's type: a pack parameter's row, or the pack of any number of
actuals at an element. -/
private partial def lowerRest (ds : Array Definition) (owner : Nat)
    (params : Array (List Nat)) (seen : Visit) (term : Json) : Lowering (List Nat) := do
  if (term.getObjValAs? String "k").toOption == some "pack" then
    CellClaims.fieldsExactly term ["k", "of", "span"]
    let operand ← field term "of"
    CellClaims.fieldsExactly operand ["k", "name", "span"]
    if (← str operand "k") != "binder" then throw "a pack rest must name a type parameter"
    match seen.binders.lookup (← str operand "name") with
    | some (.pack row) => return [row]
    | some (.value _) => throw "a value parameter used as an argument pack"
    | none => throw "a pack parameter outside its generic method"
  let element ← lowerType ds owner params seen term
  return [← use (.pack ⟨[], [], some element, false, true⟩ [])]

private partial def lowerType (ds : Array Definition) (owner : Nat)
    (params : Array (List Nat)) (seen : Visit) (term : Json) : Lowering (List Nat) := do
  match ← str term "k" with
  | "atom" =>
    match ← str term "name" with
    | "null" => return [0]
    | "undefined" => return [3]
    | "boolean" => return [1, 2]
    | "number" => return [← use .num]
    | "string" => return [← use .str]
    | "bigint" => return [← use .bigint]
    | "symbol" => return [← use .symbol]
    | "unknown" | "void" => return [← use .top]
    | "never" => return []
    -- `object`: every object. One with no call code is an ordinary record
    -- constraining no key (`recT []`, arrays and instances included), and one
    -- with call or construct code meets no signature, as `callable`'s.
    | "object" =>
      let plain ← use (.refs [] [] [])
      let calls ← use (.arrs [] [])
      let ctors ← use (.ctors [])
      return [plain, calls, ctors].eraseDups.mergeSort (· ≤ ·)
    | _ => throw "unsupported declaration primitive"
  -- A generic method's scheme comes from its source terms. Unsupported
  -- binder roles or bounds refuse the declaration; no contract is erased.
  | "scheme" =>
    CellClaims.fieldsExactly term ["k", "binders", "signatures", "span"]
    let bs ← arr term "binders"
    let sigTerms ← arr term "signatures"
    let refuse (reason : String) : Lowering (List Nat) := do
      throw s!"generic contract at {(← field term "span").compress}: {reason}; the contract cannot be erased"
    -- A bound naming the method's own binders is not what a
    -- scheme's bounds mean: they are read outside the binders.
    let names ← bs.toList.mapM fun b => do
      CellClaims.fieldsExactly b ["name", "bound", "default", "span"]
      str b "name"
    let own (j : Json) : Bool := names.any fun n =>
      let use := binderUse n j
      use.value || use.pack
    if ← bs.anyM (fun b => do return own (← field b "bound")) then return ← refuse "dependent method bounds are not represented"
    -- Until a pack's collected-array view is implemented, a binder used in
    -- both roles cannot be represented. Classification respects nested scopes.
    let uses := names.map fun n => (n, binderUse n (.arr sigTerms))
    if uses.any (fun (_, use) => use.pack && use.value) then return ← refuse "a binder used as both a value and an argument pack is not represented"
    let packs := (uses.filter fun (_, use) => use.pack).map Prod.fst
    let spanKey := (← field term "span").compress
    -- A generic method's binder rows are its member's: the key, the binder's
    -- position and declared bound, and the colour. Members of one key
    -- declared alike quantify over the same rows, whichever declaration
    -- states them, so the covering rule for quantified signatures, which
    -- relates schemes binding the same rows, relates them
    -- (`SchemeCoversWith`). Any other scheme's rows are its own.
    let rowName (k : Nat) (n : String) (bound : Json) (c : Nat) : String :=
      match seen.member with
      | some key => s!"{key}#{k}:{bound.compress}^{c}"
      | none => s!"{n}#{k}@{spanKey}^{c}"
    let mine (head : String) : Bool := match seen.member with
      | some key => head.startsWith s!"{key}#"
      | none => head.endsWith s!"@{spanKey}"
    let taken := freeColours (← get) (← getThe SourceTypes.Table) (4 + nullaryCount ds) mine
      (params.toList.flatten ++ seen.binders.map (fun p => p.2.row))
    match (List.range colourBudget).find? (fun c => !taken.contains c) with
    | none => refuse "the binder colour budget is exhausted"
    | some c =>
      let rows ← ((List.range names.length).zip (names.zip bs.toList)).mapM fun (k, n, b) => do
        paramRow (rowName k n (← field b "bound") c) (if packs.contains n then .arguments else .value)
      -- Bounds are read where the method is declared, outside its binders. A
      -- pack parameter's bound is an array or a tuple of required positions,
      -- read as the argument lists it admits.
      let packBound (b : Json) : Lowering (Option (List Nat)) := do
        match (b.getObjValAs? String "k").toOption with
        | some "array" =>
          let element ← lowerType ds owner params seen (← field b "element")
          return some [← use (.pack ⟨[], [], some element, false, true⟩ [])]
        | some "tuple" =>
          if !(← arr b "optional").isEmpty || (← field b "rest") != .null then return none
          let required ← (← arr b "required").mapM (lowerType ds owner params seen)
          return some [← use (.pack ⟨required.toList, [], none, false, true⟩ [])]
        | _ => return none
      let bounds? ← (bs.toList.zip (rows.zip names)).filterMapM fun (b, row, n) => do
        let bound ← field b "bound"
        if packs.contains n then
          if bound == .null then return none
          return some ((← packBound bound).map (row, ·))
        if bound == .null then return none
        let declared ← lowerType ds owner params seen bound
        if groundTerm bound then
          modify fun m => { m with binders := (row, declared) :: m.binders.filter (·.1 != row) }
        return some (some (row, declared))
      let some bounds := bounds?.mapM id | return ← refuse "the argument-pack bound is not represented"
      let bindings := (names.zip rows).map fun (name, row) =>
        (name, if packs.contains name then BinderBinding.pack row else .value row)
      let inner := { seen with binders := bindings ++ seen.binders, member := none }
      -- A method whose signatures cannot be lowered, as one whose unfolding
      -- keeps growing (`Promise<T>`'s `catch<R>` returns `Promise<T | R>`),
      -- refuses the declaration: failure is never recovered as a weaker type.
      let sigs ← sigTerms.toList.mapM fun f => do
        CellClaims.fieldsExactly f ["k", "receiver", "params", "rest", "result", "span"]
        let recv ← lowerType ds owner params inner (← field f "receiver")
        let ps ← (← arr f "params").toList.mapM (lowerType ds owner params inner)
        let restTerm ← field f "rest"
        let rest ← if restTerm == .null then pure none else
          some <$> lowerRest ds owner params inner restTerm
        let res ← lowerType ds owner params inner (← field f "result")
        return (recv, ps, rest, res)
      let fixed := sigs.filterMap fun (r, ps, rest, res) => if rest.isNone then some (r, ps, res) else none
      let rests := sigs.filterMap fun (r, ps, rest, res) => rest.map fun P => (r, ps, P, res)
      return [← schemeRow rows fixed bounds rests]
  | "binder" =>
    CellClaims.fieldsExactly term ["k", "name", "span"]
    match seen.binders.lookup (← str term "name") with
    | some (.value row) => return [row]
    | some (.pack _) => throw "an argument pack used as a value type"
    | none => throw "a type parameter outside its generic method"
  | "literal" =>
    Fragment.translate (Json.mkObj [("top", toJson false), ("atoms", toJson [← literalAtom term])])
  | "union" =>
    let parts ← arr term "parts"
    let arms ← parts.mapM (lowerType ds owner params seen)
    return arms.toList.flatten.eraseDups.mergeSort (· ≤ ·)
  | "intersection" =>
    let parts := (← (← arr term "parts").mapM (lowerType ds owner params seen)).toList
    -- A nullary declaration's row is filled before it is met, unless its own
    -- equation is being lowered: then the meet waits for it.
    for l in parts.flatten do
      if l < (← get).floor && unfilled (← getThe SourceTypes.Table) l then
        if let some i := nullaryAt ds l then
          if !(← get).lowering.contains i then fillNullary ds i
    meetRow parts
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
    if ds[owner]!.parameters.isEmpty then return [rowIndex ds owner]
    -- A generic declaration's application reserves its own row, passed after
    -- its arguments.
    match params[ds[owner]!.parameters.size]? with
    | some row => return row
    | none => throw "generic method receiver needs an application row"
  | "reference" =>
    let i ← referenceIndex ds term
    let args ← arr term "args"
    if ds[i]!.parameters.isEmpty then
      if !args.isEmpty then throw "reference has too many type arguments"
      else return [rowIndex ds i]
    let values ← args.mapM (lowerType ds owner params seen)
    let values ← lowerApplication ds i values seen
    -- An application with methods is its row (`groundApplication`). Any
    -- other is expanded inline, which a recursive declaration would do
    -- without end: the depth bound refuses it.
    if !mentionsSelf ds[i]!.expression && !recursiveDeclaration ds i &&
        (seen.declarations.filter (· == i)).length ≥ applicationDepth then
      throw "recursive generic application needs memoized rows"
    groundApplication ds i values seen
  | "array" =>
    let element ← lowerType ds owner params seen (← field term "element")
    let readonly ← bool term "readonly"
    let store ← use (.list ⟨[], [], some element, readonly, ← bool term "dense"⟩ [])
    return [← use (SourceTypes.arrayClause (← arrayExcludedKeys ds) store readonly)]
  | "tuple" =>
    CellClaims.fieldsExactly term ["k", "readonly", "dense", "required", "optional", "rest", "span"]
    let required ← (← arr term "required").mapM (lowerType ds owner params seen)
    let optional ← (← arr term "optional").mapM (lowerType ds owner params seen)
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure none else
      some <$> lowerType ds owner params seen restTerm
    let readonly ← bool term "readonly"
    let store ← use (.list ⟨required.toList, optional.toList, rest, readonly, ← bool term "dense"⟩ [])
    return [← use (SourceTypes.arrayClause (← arrayExcludedKeys ds) store readonly)]
  | "function" =>
    CellClaims.fieldsExactly term ["k", "receiver", "params", "rest", "result", "span"]
    let recv ← field term "receiver"
    let receiver ← if recv == .null then pure [← use .top] else
      lowerType ds owner params seen recv
    let domains ← (← arr term "params").mapM (lowerType ds owner params seen)
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure none else
      some <$> lowerRest ds owner params seen restTerm
    let result ← lowerType ds owner params seen (← field term "result")
    let row : Clause (List Nat) := match rest with
      | none => .arrs [(receiver, domains.toList, result)] []
      | some P => .arrs [] [(receiver, domains.toList, P, result)]
    return [← use row]
  | "constructor" =>
    CellClaims.fieldsExactly term ["k", "params", "rest", "result", "span"]
    let ps ← (← arr term "params").mapM (lowerType ds owner params seen)
    let restTerm ← field term "rest"
    let result ← lowerType ds owner params seen (← field term "result")
    if restTerm == .null then return [← use (.ctors [(ps.toList, result)])]
    let P ← lowerRest ds owner params seen restTerm
    return [← use (.ctors [] [(ps.toList, P, result)])]
  -- The standard library's `Function`: a value with call code or with
  -- construct code, meeting no signature, so nothing calls or constructs
  -- through it (`callsT []`, `ctorsT []`).
  | "callable" =>
    CellClaims.fieldsExactly term ["k", "span"]
    let calls ← use (.arrs [] [])
    let ctors ← use (.ctors [])
    return [calls, ctors].eraseDups.mergeSort (· ≤ ·)
  | "pack" => throw "a pack parameter outside a signature's rest"
  | "object" =>
    CellClaims.fieldsExactly term (objectMembers term)
    -- Members held as own properties that are not enumerable (the library
    -- overlay's `Error`): on a prototype the object holds, whose keys the
    -- object does not own, so a read and `in` find them there and a spread
    -- does not copy them.
    let hidden ← match term.getObjVal? "prototype" with
      | .ok t => do
        let P ← lowerType ds owner params seen t
        let keys ← (← arr t "fields").mapM fun f => do PropKey.decode (← field f "name")
        pure (some (P, keys.toList))
      | .error _ => pure none
    -- A method, one signature or several with the declaration as receiver, is
    -- a host-relative member: its contract holds when it is invoked on the
    -- object it is read from, so it is neither a field nor a view. An
    -- optional method stays an optional field; a generic one, whose type is a
    -- scheme, stays a readonly member.
    let methodForms (t : Json) : Option (Array Json) :=
      let forms := if (t.getObjValAs? String "k").toOption == some "intersection"
        then (t.getObjValAs? (Array Json) "parts").toOption.getD #[] else #[t]
      if !forms.isEmpty && forms.all (fun f => (f.getObjValAs? String "k").toOption == some "function" &&
          ((f.getObjVal? "receiver").toOption.bind fun r => (r.getObjValAs? String "k").toOption) ==
            some "self")
      then some forms else none
    -- A generic method, a scheme whose signatures take the declaration as
    -- receiver, is a host-relative member with quantified signatures: the
    -- scheme the member bound to its host meets (`MethodMembers.boundOn`).
    -- The forwarding function ignores the receiver it is given, so the
    -- scheme's own receivers admit any value.
    let schemeMethod (t : Json) : Option Json := do
      guard ((t.getObjValAs? String "k").toOption == some "scheme")
      let sigs ← (t.getObjValAs? (Array Json) "signatures").toOption
      guard (!sigs.isEmpty && sigs.all fun f =>
        ((f.getObjVal? "receiver").toOption.bind fun r => (r.getObjValAs? String "k").toOption) ==
          some "self")
      let anyReceiver (f : Json) : Json := f.setObjVal! "receiver"
        (Json.mkObj [("k", "atom"), ("name", "unknown"), ("span", f.getObjValD "span")])
      return t.setObjVal! "signatures" (toJson (sigs.map anyReceiver))
    let mut methods : List (MethodMembers.Sig (List Nat)) := []
    let mut all : Array (PropKey × List Nat × Bool × Bool) := #[]
    -- An optional field constrains its key only where the object has it; a
    -- readonly one is a view there.
    for f in ← arr term "fields" do
      let name ← PropKey.decode (← field f "name")
      if SourceTypes.reservedKey name then
        throw s!"a declared member cannot use the model's internal key {repr name}"
      let ty ← field f "type"
      let optional ← bool f "optional"
      match (if optional then none else methodForms ty) with
      | some forms =>
        let mut calls : List (List (List Nat) × List Nat) := []
        let mut rests : List (List (List Nat) × List Nat × List Nat) := []
        for form in forms do
          CellClaims.fieldsExactly form ["k", "receiver", "params", "rest", "result", "span"]
          let domains ← (← arr form "params").mapM (lowerType ds owner params seen)
          let rest ← field form "rest"
          let result ← lowerType ds owner params seen (← field form "result")
          if rest == .null then calls := calls ++ [(domains.toList, result)]
          else rests := rests ++ [(domains.toList, ← lowerRest ds owner params seen rest, result)]
        methods := methods ++ [⟨name, calls, rests, []⟩]
      | none =>
        match (if optional then none else schemeMethod ty) with
        | some t =>
          let scheme ← lowerType ds owner params { seen with member := some (toJson name).compress } t
          methods := methods ++ [⟨name, [], [], [scheme]⟩]
        | none =>
          let value ← lowerType ds owner params seen ty
          all := all.push (name, value, ← bool f "readonly", optional)
    let fs := all.filterMap fun (n, v, r, o) => if o then none else some (n, v, r)
    let optional := all.toList.filterMap fun (n, v, r, o) =>
      if o then some (⟨n, r, v⟩ : OptionalField (List Nat)) else none
    let names := fs.toList.map (·.1) ++ optional.map (·.key) ++ methods.map (·.key)

    if names.eraseDups.length != names.length then throw "duplicate declaration field"
    -- An index is a view over the keys it constrains; a mutable one is also
    -- a writable index at the same contract, as a mutable field is an
    -- invariant one.
    let mut indexes : List (IndexKeys × List Nat) := []
    let mut cells : List (IndexKeys × List Nat) := []
    for (_, keys, index) in indexSignatures term do
      CellClaims.fieldsExactly index ["readonly", "value", "span"]
      let value ← lowerType ds owner params seen (← field index "value")
      indexes := indexes ++ [(keys, value)]
      if !(← bool index "readonly") then cells := cells ++ [(keys, value)]
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
      else
        variadic := variadic ++ [(receiver, domains.toList,
          ← lowerRest ds owner params seen rest, result)]
    if hidden.isSome && (!fixed.isEmpty || !variadic.isEmpty || !indexes.isEmpty) then
      throw "a prototype of hidden members is stated of a plain record only"
    let row ← if fixed.isEmpty && variadic.isEmpty then
        if indexes.isEmpty then
          match hidden with
          | some (P, keys) =>
            use (.refs writes [] (views ++ [(CallArguments.protoField, P)]) optional methods [⟨false, keys⟩])
          | none => use (.refs writes [] views optional methods)
        else use (.dict writes [] views indexes optional methods [] cells)
      else if !methods.isEmpty then
        throw "a callable object with methods needs a combined clause"
      else if !optional.isEmpty then
        throw "a callable object with an optional field needs a combined clause"
      else if !indexes.isEmpty || !views.isEmpty then
        throw "callable object with index or readonly field needs a combined clause"
      else if writes.isEmpty then use (.arrs fixed variadic)
      else use (.callable writes [] fixed variadic)
    return [row]
  | _ => throw "source type constructor outside the graph fragment"

private partial def lowerApplication (ds : Array Definition) (i : Nat)
    (supplied : Array (List Nat)) (seen : Visit) : Lowering (Array (List Nat)) := do
  let d := ds[i]!
  if supplied.size > d.parameters.size then throw "reference has too many type arguments"
  let mut values := supplied
  for p in d.parameters.toList.drop supplied.size do
    CellClaims.fieldsExactly p ["name", "span", "bound", "default"]
    let default ← field p "default"
    if default == .null then throw "type application has missing required argument"
    values := values.push (← lowerType ds i values (seen.enter i) default)
  for index in [:d.parameters.size] do
    let p := d.parameters[index]!
    CellClaims.fieldsExactly p ["name", "span", "bound", "default"]
    let bound ← field p "bound"
    if bound != .null then
      -- A binder of a generic method stands for an instance within its own
      -- ground declared bound, so it establishes a parameter's bound through
      -- that one (`K2 extends Json` in `Mapper<K, V, K2, V2>`), and so does its
      -- meet with ground types, which is below it.
      let binders := (← get).binders
      let T ← getThe SourceTypes.Table
      let actual := values[index]!.flatMap fun l =>
        let p := match T[l]? with
          | some (RequestJson.Row.meet p _ _) => p
          | _ => l
        match binders.lookup p with
        | some declared => declared
        | none => [l]
      let upper ← lowerType ds i (values.toList.take index).toArray (seen.enter i) bound
      let table ← getThe SourceTypes.Table
      let graph := SourceTypes.graph table
      let pool := CertificateProducer.reachablePool graph actual upper
      let name ← str p "name"
      let span ← field p "span"
      -- A parameter row stands for any type: a unit's binder whose bound
      -- names another binder is one (`binderRows`), without that bound.
      let paramName := fun (l : Nat) => match table[l]? with
        | some (RequestJson.Row.param _ n _) => some n
        | _ => none
      let refusal := match actual.mapM paramName with
        | some (n :: ns) => s!"the type parameter {String.intercalate " | " (n :: ns)} does not establish the declared bound for {name} at {span.compress}: a type parameter whose bound names another is read as its own parameter row, which does not carry that bound"
        | _ => s!"type argument does not establish its declared bound for {name} at {span.compress}: {SourceTypes.render table actual} ≤ {SourceTypes.render table upper}"
      match CertificateProducer.subtype graph pool actual upper with
      | some proof =>
        if !PositiveCertificates.check graph actual upper proof then
          throw refusal
      | none => throw refusal
  return values

/-- A ground application of a generic declaration. One given a row, as every
application with methods is, is that row (`Memo.applications`). An application
with methods not yet given one gets it before its equation is lowered, since
the methods' receiver is that application, and the equation is lowered from
that row afresh, whatever path reached it. Its arguments must stay within the
argument budget. Any other application is its equation's labels, so
`Id<boolean>` is exactly `[1, 2]`. -/
private partial def groundApplication (ds : Array Definition) (i : Nat)
    (values : Array (List Nat)) (seen : Visit) : Lowering (List Nat) := do
  let T ← getThe SourceTypes.Table
  if let some row := (← get).row T i values then return [row]
  if mentionsSelf ds[i]!.expression || (!ds[i]!.parameters.isEmpty && recursiveDeclaration ds i) then
    if (reach (← get) T (4 + nullaryCount ds) argumentBudget values.toList.flatten).length > argumentBudget then
      throw "a recursive generic application whose arguments keep growing"
    let row ← modifyGetThe SourceTypes.Table fun T => (T.length, T ++ RequestJson.rows [[]])
    modify fun m => m.give T i values row
    let rows ← lowerDefinitionRows ds i (values.push [row]) (Visit.enter {} i)
    modifyThe SourceTypes.Table fun T => T.set row rows
    settle
    return [row]
  if ds[i]!.bases.isEmpty then
    lowerType ds i values (seen.enter i) ds[i]!.expression
  else
    (← lowerDefinitionRows ds i values (seen.enter i)).mapM use

private partial def lowerHead (ds : Array Definition) (owner : Nat)
    (params : Array (List Nat)) (seen : Visit)
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
    if mentionsSelf ds[i]!.expression then
      let labels ← groundApplication ds i values seen
      let table ← getThe SourceTypes.Table
      -- A generic base's application row reserved but not yet lowered (a
      -- derived class's instance type met with its base's, lowered first):
      -- its rows now, as the reservation would give it.
      if let [row] := labels then
        if !ds[i]!.parameters.isEmpty && (SourceTypes.graph table row).isEmpty then
          let rows ← lowerDefinitionRows ds i (values.push [row]) (Visit.enter {} i)
          modifyThe SourceTypes.Table fun T => T.set row rows
          settle
          return rows
      return labels.flatMap (SourceTypes.graph table)
    lowerDefinitionRows ds i values (seen.enter i)
  | _ =>
    let labels ← lowerType ds owner params seen term
    let table ← getThe SourceTypes.Table
    let pending := (← get).pending
    if labels.any fun l => pending.any (·.1 == l) then
      throw "an intersection with an operand still being lowered is the whole of a declaration's equation"
    return labels.flatMap (SourceTypes.graph table)

private partial def lowerDefinitionRows (ds : Array Definition) (i : Nat)
    (params : Array (List Nat)) (seen : Visit) :
    Lowering (List (Clause (List Nat))) := do
  -- An interface stating no member of its own is its bases' meet: its body
  -- constrains nothing, so a callable base stays callable
  -- (`interface Callback extends Function {}`).
  let own := ds[i]!.expression
  let empty := (own.getObjValAs? String "k").toOption == some "object" &&
    ((own.getObjValAs? (Array Json) "fields").toOption.getD #[1]).isEmpty &&
    ((own.getObjValAs? (Array Json) "calls").toOption.getD #[1]).isEmpty &&
    (indexSignatures own).isEmpty && (own.getObjVal? "prototype").toOption.isNone
  let mut rows ← if empty && !ds[i]!.bases.isEmpty then pure [.top]
    else lowerHead ds i params seen own
  for base in ds[i]!.bases do
    let inherited ← lowerHead ds i params seen base
    rows ← inheritRows rows inherited
  return rows

/-- Fill nullary declaration `i`'s row from its equation, then the waiting
intersections it completes. -/
private partial def fillNullary (ds : Array Definition) (i : Nat) : Lowering Unit := do
  modify fun m => { m with lowering := i :: m.lowering }
  let rows ← lowerDefinitionRows ds i #[] { declarations := [i] }
  modifyThe SourceTypes.Table (·.set (rowIndex ds i) rows)
  modify fun m => { m with lowering := m.lowering.erase i }
  settle
end

/-- Fill the producer's empty reserved rows: each nullary declaration's, and
each generic application's `(row, declaration position, argument types)`, with
Lean's own lowering, so there is one lowering of every declaration. A reserved
row is its application's from the start (`Memo.applications`): every lowering
naming the application at the same arguments, a declaration's, a source
annotation's or an instance's, is that row, not another copy of its
equation. An intersection's reserved row `(row, operand types)` is likewise
the intersection's from the start (`Memo.meets`): the meet of its operands, as
the source's own `A & B` lowers (`meetRow`), filled where an equation first
meets it, or else in row order with the applications, so the rows it names
are filled first. An application whose equation is a union of reserved rows
(an alias) is their clauses: it waits for a later pass where one of them is
not yet filled. -/
private def fillRows (ds : Array Definition) (candidate : SourceTypes.Table)
    (applications : List (Nat × Nat × List (List Nat)) := [])
    (arrays : List (Nat × Nat × Bool) := [])
    (meets : List (Nat × List (List Nat)) := []) :
    Except String (SourceTypes.Table × Memo) := do
  if candidate.length < 4 + nullaryCount ds then throw "declaration graph rows are missing"
  for i in [:ds.size] do
    if ds[i]!.parameters.isEmpty && candidate[rowIndex ds i]! != RequestJson.Row.clauses [] then
      throw "producer supplied a declaration equation"
  let reserved (row : Nat) : Bool :=
    row ≥ 4 + nullaryCount ds && row < candidate.length && candidate[row]! == RequestJson.Row.clauses []
  let applications := applications.mergeSort (fun x y => x.1 ≤ y.1)
  for (row, declaration, args) in applications do
    if !reserved row then throw "an application's reserved row is not an empty producer row"
    if declaration ≥ ds.size || ds[declaration]!.parameters.isEmpty then
      throw "an application names no generic declaration"
    if args.any (fun A => A.any (· ≥ row)) then
      throw "an application's arguments name a later row"
  for (row, parts) in meets do
    if !reserved row || applications.any (·.1 == row) || arrays.any (·.1 == row) then
      throw "an intersection's reserved row is not an empty producer row"
    if parts.isEmpty || parts.any (fun A => A.any (· ≥ row)) then
      throw "an intersection's operands name a later row"
  if (applications.map (·.1) ++ meets.map (·.1)).eraseDups.length != applications.length + meets.length then
    throw "a row is reserved for two applications"
  let mut table := candidate
  -- An array row is the array shape over the store row the producer stated.
  for (row, store, readonly) in arrays do
    if !reserved row || applications.any (·.1 == row) || table[row]! != RequestJson.Row.clauses [] then
      throw "an array's reserved row is not an empty producer row"
    if store ≥ table.length then throw "an array's store names no row"
    table := table.set row (.clauses [SourceTypes.arrayClause (← arrayExcludedKeys ds) store readonly])
  -- A reserved application at all its arguments is that row from the start,
  -- for the declarations' equations too, and so is a reserved intersection.
  let mut memo : Memo := { floor := 4 + nullaryCount ds, meets := meets.map fun (r, ps) => (ps, r) }
  for (row, i, args) in applications do
    if args.length == ds[i]!.parameters.size && (memo.row table i args.toArray).isNone then
      memo := memo.give table i args.toArray row
  for i in [:ds.size] do
    -- A declaration an intersection met earlier is filled already.
    if ds[i]!.parameters.isEmpty && unfilled table (rowIndex ds i) then
      let (((), grown), expanded) ← ((fillNullary ds i).run memo).run table
      memo := grown
      table := expanded
  -- Arguments are compared by the rows they name once those are filled.
  memo := memo.rekey table
  -- Applications and intersections in row order: an argument or an operand
  -- names only earlier rows.
  let order := (applications.map (·.1) ++ meets.map (·.1)).mergeSort (· ≤ ·)
  -- An application whose equation is other types' union (an alias,
  -- `IteratorResult<T>`) is their rows' clauses: where one of them is a row
  -- reserved later and not yet filled, it waits for a later pass, after it.
  let mut pending := order
  let mut done : List Nat := []
  for _ in [:order.length + 1] do
    if pending.isEmpty then break
    let mut waiting : List Nat := []
    for row in pending do
      if let some (_, parts) := meets.find? (·.1 == row) then
        -- Filled here unless an equation met it first.
        let ((filled, grown), expanded) ← ((meetRow parts).run memo).run table
        if filled != [row] then throw "an intersection's reserved row names a type parameter"
        memo := grown
        table := expanded
        done := row :: done
        continue
      let some (_, i, args) := applications.find? (·.1 == row) | throw "reserved row without a task"
      let finished := done
      let fill : Lowering (Option (List (Clause (List Nat)))) := do
        let values ← lowerApplication ds i args.toArray {}
        let T ← getThe SourceTypes.Table
        -- An application given another row, one whose omitted arguments are
        -- defaults, is that row's clauses, if it has them.
        let earlier := ((← get).row T i values).filter (· != row)
        if let some (RequestJson.Row.clauses cs@(_ :: _)) := earlier.bind (T[·]?) then return some cs
        if mentionsSelf ds[i]!.expression then
          if earlier.isNone && !(← get).applications.any (·.row == row) then
            modify fun m => m.give T i values row
          some <$> lowerDefinitionRows ds i (values.push [row]) (Visit.enter {} i)
        else
          let labels ← if ds[i]!.bases.isEmpty then
              lowerType ds i values (Visit.enter {} i) ds[i]!.expression
            else (← lowerDefinitionRows ds i values (Visit.enter {} i)).mapM use
          let T ← getThe SourceTypes.Table
          if labels.any fun l => l != row && order.contains l && !finished.contains l &&
              T[l]? == some (RequestJson.Row.clauses []) then
            return none
          some <$> labels.flatMapM fun l => match T[l]? with
            | some (RequestJson.Row.clauses cs) => pure cs
            | _ => throw "an application lowers to a row without clauses"
      match ← (fill.run memo).run table with
      | ((some filled, grown), expanded) =>
        let (((), grown), expanded) ← (settle.run grown).run (expanded.set row filled)
        memo := grown
        table := expanded
        done := row :: done
      | ((none, _), _) => waiting := waiting ++ [row]
    if waiting.length == pending.length then
      throw "reserved applications wait on each other's rows"
    pending := waiting
  if !pending.isEmpty then throw "reserved applications wait on each other's rows"
  let (((), completed), final) ← (complete.run memo).run table
  -- Keys again, now every reserved row, a meet row among them, is filled.
  return (final, completed.rekey final)

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
parts over parameters are rebuilt as claim forms, which read each binder as its
parameter row. This is the one path for every declaration applied to a binder. -/
private partial def rigidClaim (ds : Array Definition) (owner : Nat) (env : Array Json)
    (seen : List Nat) (term : Json) : Lowering Json := do
  if !mentionsParameter term then
    return graphClaim (← lowerType ds owner #[] { declarations := seen } term)
  match ← str term "k" with
  | "scheme" =>
    CellClaims.fieldsExactly term ["k", "binders", "signatures", "span"]
    return topClaim
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
    if (restTerm.getObjValAs? String "k").toOption == some "pack" then
      throw "a pack parameter has no claim form"
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
      ("readonly", toJson (← bool term "readonly")), ("dense", toJson (← bool term "dense"))]]
  | "tuple" =>
    CellClaims.fieldsExactly term ["k", "readonly", "dense", "required", "optional", "rest", "span"]
    let required ← (← arr term "required").mapM (rigidClaim ds owner env seen)
    let optional ← (← arr term "optional").mapM (rigidClaim ds owner env seen)
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure Json.null else
      rigidClaim ds owner env seen restTerm
    return claimType [Json.mkObj [("a", toJson "array"), ("required", toJson required),
      ("optional", toJson optional), ("rest", rest),
      ("readonly", toJson (← bool term "readonly")), ("dense", toJson (← bool term "dense"))]]
  | "constructor" =>
    CellClaims.fieldsExactly term ["k", "params", "rest", "result", "span"]
    if (← field term "rest") != .null then throw "a construct signature with a rest has no claim form"
    let params ← (← arr term "params").mapM (rigidClaim ds owner env seen)
    return claimType [Json.mkObj [("a", toJson "constructor"), ("params", toJson params),
      ("result", ← rigidClaim ds owner env seen (← field term "result"))]]
  | "object" =>
    CellClaims.fieldsExactly term (objectMembers term)
    if (← field term "stringIndex") != .null || keyedIndexes term || !(← arr term "calls").isEmpty then
      throw "a declaration with call or index signatures applied to a type parameter is outside the fragment"
    let fields ← (← arr term "fields").mapM fun f => do
      let optional ← bool f "optional"
      let value ← rigidClaim ds owner env seen (← field f "type")
      let write := if ← bool f "readonly" then claimType [] else value
      return Json.mkObj [("name", ← field f "name"), ("optional", toJson optional),
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

private def arrayClaim (required optional : List Json) (rest : Json) (readonly dense : Bool) : Json :=
  claimType [Json.mkObj [("a", toJson "array"), ("required", toJson required),
    ("optional", toJson optional), ("rest", rest), ("readonly", toJson readonly), ("dense", toJson dense)]]

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
private partial def annotationClaim (ds : Array Definition) (term : Json)
    (bound : List (String × Json) := []) (scope : List (String × Json) := []) : Lowering Json := do
  let recur := fun t => annotationClaim ds t bound scope
  -- The rows the named binders are read as, as the unit reads them: a
  -- binder with a ground bound of clause rows is its row met with the bound,
  -- so a bounded declaration's own bound check sees the binder within it;
  -- one bounded by another binder in scope is its row met with that binder's
  -- (`dependentMeet`).
  let binderRows (names : List String) : Lowering (List (String × Nat)) := do
    let rec rowOf : Nat → String → Lowering Nat
      | 0, n => (SourceTypes.binderRow n : SourceTypes.Lowering Nat)
      | fuel + 1, n => do
        let p ← (SourceTypes.binderRow n : SourceTypes.Lowering Nat)
        match scope.lookup n with
        | some b =>
          if b == .null then return p
          if groundTerm b then
            let B ← (Fragment.translate (← annotationClaim ds b) : SourceTypes.Lowering _)
            let G := SourceTypes.graph (← getThe SourceTypes.Table)
            if B.isEmpty || !G.plainTy B then return p
            return ← (SourceTypes.internRow (RequestJson.Row.meet p (B.flatMap G)) :
              SourceTypes.Lowering Nat)
          match (b.getObjValAs? String "k").toOption, (b.getObjValAs? String "name").toOption with
          | some "binder", some m =>
            if m == n || (scope.lookup m).isNone then return p
            let r ← rowOf fuel m
            match SourceTypes.dependentMeet (← getThe SourceTypes.Table) p r with
            | some meet => (SourceTypes.internRow meet : SourceTypes.Lowering Nat)
            | none => return p
          | _, _ => return p
        | none => return p
    names.mapM fun n => do return (n, ← rowOf scope.length n)
  sourceObject term
  match ← str term "k" with
  | "scheme" =>
    CellClaims.fieldsExactly term ["k", "binders", "signatures", "span"]
    return topClaim
  | "atom" =>
    CellClaims.fieldsExactly term ["k", "name", "span"]
    match ← str term "name" with
    | "unknown" => return topClaim
    | "never" => return claimType []
    -- Several clauses no claim atom spells: its graph rows.
    | "object" => return graphClaim (← lowerType ds ds.size #[] {} term)
    | name =>
      if ["null", "undefined", "boolean", "number", "string", "void", "bigint", "symbol"].contains name then
        return claimType [Json.mkObj [("a", toJson name)]]
      throw s!"unsupported source atom {name}"
  | "literal" => return claimType [← literalAtom term]
  | "union" =>
    CellClaims.fieldsExactly term ["k", "parts", "span"]
    let parts ← (← arr term "parts").mapM recur
    if parts.any isTopClaim then return topClaim
    return claimType (parts.toList.flatMap claimAtoms).eraseDups
  | "intersection" =>
    CellClaims.fieldsExactly term ["k", "parts", "span"]
    -- An array with further members: an array may carry own keys its
    -- prototype does not provide, so an array operand meets record operands
    -- as one object (`meetRow`), which only a graph row spells.
    let terms ← arr term "parts"
    if terms.any fun t => ["array", "tuple"].contains ((t.getObjValAs? String "k").toOption.getD "") then
      if !groundTerm term then
        throw "an array's intersection over a type parameter is outside the fragment"
      return graphClaim (← lowerType ds ds.size #[] {} term)
    -- Otherwise conjunction exists only inside a record or function atom.
    let parts ← terms.mapM recur
    let single : Json → Option Json := fun part =>
      match isTopClaim part, claimAtoms part with
      | false, [atom] => some atom
      | _, _ => none
    -- Construct signatures conjoin as call signatures do: an overloaded
    -- constructor, `new Date()` and `new Date(v)`, meets each.
    let atoms := parts.toList.filterMap single
    let shape := atoms.head?.bind fun atom => (atom.getObjVal? "a").toOption
    -- A record with an index signature is not a conjunct's cell record: it
    -- meets the others as graph rows, below.
    if atoms.length == parts.size && !atoms.isEmpty &&
        atoms.all (fun atom => (atom.getObjVal? "a").toOption == shape &&
          (atom.getObjVal? "indexSignature").toOption.isNone) &&
        (shape == some (.str "record") || shape == some (.str "function") ||
          shape == some (.str "constructor")) then
      return claimType [atoms.head!.setObjVal! "and" (toJson atoms.tail)]
    -- Any other intersection meets as graph rows: the one meaning every
    -- intersection has (`meetRow`). An operand that is ground once the
    -- binders an instantiation fixes are read, `T & DepSafe` at `T := Todo`,
    -- is a clause row; a binder is the row the unit reads it as, and its meet
    -- with others a meet row, `T & "fixed"`, `T & U`.
    if parts.isEmpty then throw "empty intersection"
    let rows ← binderRows (parts.toList.flatMap SourceTypes.binderNames).eraseDups
    return graphClaim (← meetRow (← parts.toList.mapM fun part =>
      (Fragment.translate (SourceTypes.annotationAtRows rows part) : SourceTypes.Lowering _)))
  | "array" =>
    CellClaims.fieldsExactly term ["k", "readonly", "dense", "element", "span"]
    return arrayClaim [] [] (← recur (← field term "element")) (← bool term "readonly") (← bool term "dense")
  | "tuple" =>
    CellClaims.fieldsExactly term ["k", "readonly", "dense", "required", "optional", "rest", "span"]
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure Json.null else recur restTerm
    return arrayClaim (← (← arr term "required").mapM recur).toList
      (← (← arr term "optional").mapM recur).toList rest (← bool term "readonly") (← bool term "dense")
  | "function" =>
    CellClaims.fieldsExactly term ["k", "receiver", "params", "rest", "result", "span"]
    let recv ← field term "receiver"
    let receiver ← if recv == .null then pure topClaim else recur recv
    let params ← (← arr term "params").mapM recur
    let restTerm ← field term "rest"
    if (restTerm.getObjValAs? String "k").toOption == some "pack" then
      throw "a pack parameter has no claim form"
    let rest ← if restTerm == .null then pure [] else pure [("rest", ← recur restTerm)]
    return claimType [Json.mkObj ([("a", toJson "function"), ("this", receiver),
      ("params", toJson params)] ++ rest ++ [("result", ← recur (← field term "result")),
      ("construct", toJson "unknown"), ("array", toJson "unknown")])]
  | "constructor" =>
    CellClaims.fieldsExactly term ["k", "params", "rest", "result", "span"]
    if (← field term "rest") != .null then throw "a construct signature with a rest has no claim form"
    let params ← (← arr term "params").mapM recur
    return claimType [Json.mkObj [("a", toJson "constructor"), ("params", toJson params),
      ("result", ← recur (← field term "result"))]]
  | "object" =>
    -- Members held on a prototype (the library overlay's): no claim atom
    -- spells a record's prototype, so the record is its graph rows.
    if (term.getObjVal? "prototype").toOption.isSome then
      return graphClaim (← lowerType ds ds.size #[] {} term)
    CellClaims.fieldsExactly term (objectMembers term)
    -- A type literal with call signatures is a callable: its graph rows, as
    -- a declaration's body is lowered.
    -- Lowered so, a binder an instantiation fixes is the row of its ground
    -- argument; a binder no instantiation fixes has no such row.
    let asGraph (refusal : String) : Lowering Json := do
      let rows ← (sourceBinderNames term).mapM fun n => do
        let some claim := bound.lookup n | throw refusal
        let labels ← (Fragment.translate claim : SourceTypes.Lowering _)
        let G := SourceTypes.graph (← getThe SourceTypes.Table)
        match labels with
        | [l] => pure (n, BinderBinding.value l)
        | _ =>
          if labels.isEmpty || !G.plainTy labels then throw refusal
          pure (n, BinderBinding.value (← useRow (labels.flatMap G)))
      return graphClaim (← lowerType ds ds.size #[] { binders := rows } term)
    if !(← arr term "calls").isEmpty then
      return ← asGraph "a call signature of an annotation's type literal over a type parameter is outside the fragment"
    -- A method is a host-relative member, and a number or symbol index an
    -- index over a class of keys, which no claim atom spells: the record is
    -- its graph rows, lowered as a declaration's body is.
    if keyedIndexes term then
      return ← asGraph "a number or symbol index of an annotation's type literal over a type parameter is outside the fragment"
    if (← arr term "fields").any (fun f => mentionsSelf ((f.getObjVal? "type").toOption.getD .null)) then
      return ← asGraph "a method of an annotation's type literal over a type parameter is outside the fragment"
    let fields ← (← arr term "fields").mapM fun f => do
      CellClaims.fieldsExactly f ["name", "optional", "readonly", "type", "span"]
      let optional ← bool f "optional"
      let value ← recur (← field f "type")

      let write := if ← bool f "readonly" then claimType [] else value
      return Json.mkObj [("name", ← field f "name"), ("optional", toJson optional),
        ("read", value), ("write", write)]
    let index ← field term "stringIndex"
    if fields.isEmpty && index == .null then throw "a record with no field has no location"
    let signature ← if index == .null then pure [] else do
      CellClaims.fieldsExactly index ["readonly", "value", "span"]
      -- A mutable index writes at its read contract.
      let value ← recur (← field index "value")
      pure [("indexSignature", Json.mkObj [("read", value),
        ("write", if ← bool index "readonly" then claimType [] else value)])]
    return claimType [Json.mkObj ([("a", toJson "record"), ("fields", toJson fields),
      ("indexes", Json.mkObj [("string", toJson "absent"), ("number", toJson "absent"),
        ("symbol", toJson "absent")])] ++ signature ++
      [("call", toJson "unknown"), ("construct", toJson "unknown"), ("array", toJson "unknown")])]
  | "binder" =>
    CellClaims.fieldsExactly term ["k", "name", "span"]
    -- A binder an instantiation fixes is its ground argument.
    match bound.lookup (← str term "name") with
    | some ground => return ground
    | none => return claimType [Json.mkObj [("a", toJson "param"), ("name", ← field term "name")]]
  | "reference" =>
    let index ← referenceIndex ds term
    let terms ← arr term "args"
    let args ← terms.mapM recur
    -- An application over a rigid binder is its expanded equation; a ground
    -- one is its graph labels, so `Id<boolean>` is exactly `[1, 2]`, the
    -- type a producer claims, not a new row with the same meaning.
    if args.any hasRigidParameter then
      -- A class's instance type, whose methods' receiver is the application
      -- itself, and a recursive declaration have no finite claim-form
      -- expansion over a binder, and a record with call or index signatures
      -- none at all; each is its application row at the binder's parameter
      -- row, which the graph checker reads (`SourceTypes.binderRow`).
      let atRows : Lowering Json := do
        let rows ← binderRows (args.toList.flatMap SourceTypes.binderNames).eraseDups
        let values ← args.mapM fun a =>
          (Fragment.translate (SourceTypes.annotationAtRows rows a) : SourceTypes.Lowering _)
        let values ← lowerApplication ds index values {}
        let labels ← groundApplication ds index values {}
        if labels.isEmpty then throw "generic application has no inhabited graph clause"
        return graphClaim labels
      -- An application with methods, or with bases whose contracts it meets,
      -- is its application row, as the unit reads it.
      if mentionsSelf ds[index]!.expression || !ds[index]!.bases.isEmpty then return ← atRows
      return ← tryCatch (expandApplication ds index args []) fun e => do
        unless e.startsWith "recursive generic application" ||
          e.startsWith "a declaration with call or index signatures applied to a type parameter" ||
          e.startsWith "a bounded declaration applied to a type parameter" do throw e
        atRows
    if ds[index]!.parameters.isEmpty then
      if !args.isEmpty then throw "type application has wrong arity"
      return graphClaim [rowIndex ds index]
    -- A ground argument is lowered as a declaration's own terms are, so the
    -- application is the one they name; an argument an instantiation fixes
    -- is read from its claim.
    let values ← (terms.zip args).mapM fun (t, a) =>
      if mentionsKind "binder" t then (Fragment.translate a : SourceTypes.Lowering _)
      else lowerType ds ds.size #[] {} t
    let values ← lowerApplication ds index values {}
    -- An application given a row, a producer's reserved one among them, is
    -- that row, which Lean filled from the same equation at the same arguments.
    let labels ← groundApplication ds index values {}
    if labels.isEmpty then throw "generic application has no inhabited graph clause"
    return graphClaim labels
  | k => throw s!"declaration syntax '{k}' in a source annotation"

/-- The fields of the Fragment AST that hold a source annotation. -/
private def annotationFields : List String :=
  ["annot", "functionType", "bagType", "type", "result", "bound", "retType"]

/-- Every annotation of the function tree in claim form. -/
private partial def rewrite (ds : Array Definition) (j : Json)
    (scope : List (String × Json) := []) : Lowering Json := do
  match j with
  | .arr values => return .arr (← values.mapM (rewrite ds · scope))
  | .obj fields =>
    sourceObject j
    -- The binders a function, closure or class declares are in scope below
    -- it, each with its raw bound, innermost first.
    let scope := match fields.toList.lookup "typeParams" with
      | some (.arr ps) => (ps.toList.filterMap fun p => do
          let n ← (p.getObjValAs? String "name").toOption
          return (n, (p.getObjVal? "bound").toOption.getD .null)) ++ scope
      | _ => scope
    let pairs ← fields.toArray.mapM fun (name, value) => do
      -- A ground type-parameter bound is its graph rows, whatever its form:
      -- the bound is only ever read as a type.
      if name == "bound" && value != .null && groundTerm value then
        return (name, graphClaim (← Fragment.translate (← annotationClaim ds value)))
      if annotationFields.contains name && value != .null then
        return (name, ← annotationClaim ds value [] scope)
      -- A method call's explicit type arguments: a list of annotations.
      if name == "typeArgs" then
        let .arr values := value | throw "type arguments are a list"
        return (name, .arr (← values.mapM (annotationClaim ds · [] scope)))
      return (name, ← rewrite ds value scope)
    return Json.mkObj pairs.toList
  | _ => return j

/-- A generic module value: a generic module function, or a generic imported
value. `instantiate` gives, for ground arguments in claim form, the callable
at those arguments and each binder's bound at them, converted from the source
terms with the binders fixed, so a declaration applied to a binder is an
ordinary ground application. -/
structure Instantiable where
  name : String
  pos : Span
  binders : List String
  instantiate : List (String × Json) → SourceTypes.Lowering (Json × List (String × Option Json))

/-- Replace only the producer's empty reserved rows with equations derived
from source declarations. The AST copy contains internal graph atoms only after
the original source tree has been checked for them. -/
def prepare (ast : Json) (candidate : SourceTypes.Table)
    (applications : List (Nat × Nat × List (List Nat)) := [])
    (arrays : List (Nat × Nat × Bool) := [])
    (meets : List (Nat × List (List Nat)) := []) :
    Except String (Json × SourceTypes.Table × List (String × Span × Json) × List Instantiable) := do
  let document ← field ast "declarations"
  CellClaims.fieldsExactly document ["roots", "definitions", "values", "symbols"]
  -- A symbol key `{"symbol": i}` is the i-th listed `unique symbol` constant.
  -- Distinct declarations are distinct symbols, so none is listed twice.
  let symbols ← arr document "symbols"
  if symbols.toList.eraseDups.length != symbols.size then
    throw "a unique symbol declaration is listed twice"
  let ds ← definitions document
  -- `ArrayProto`, when the source has arrays, is the first definition, so its
  -- row is `SourceTypes.arrayProtoLabel`, the one array types name.
  if let some i := (List.range ds.size).find? (fun i => ds[i]!.identity == arrayProtoIdentity) then
    if i != 0 || !ds[i]!.parameters.isEmpty then throw "ArrayProto must be the first declaration"
  let roots ← (← arr document "roots").mapM fun root => do
    let name ← str (← field root "binding") "local"
    let i ← findDefinition ds (← field root "declaration")
    return (name, i)
  if (roots.toList.map (·.1)).eraseDups.length != roots.size then
    throw "duplicate declaration root name"
  let (types, memo) ← fillRows ds candidate applications arrays meets
  -- Every array lowered from here on reads the keys it excludes from
  -- `ArrayProto`'s row, so the row must name the ones its declaration does.
  if ds[0]?.any (·.identity == arrayProtoIdentity) &&
      SourceTypes.arrayExcludedKeys (SourceTypes.graph types) != (← arrayExcludedKeys ds) then
    throw "ArrayProto's row names other keys than its declaration"
  -- Generic module functions, read from their source terms before the tree is
  -- converted.
  let callable (params : List Json) (rest : Option Json) (result : Json) (bound : List (String × Json)) :
      Lowering Json := do
    let top := Json.mkObj [("top", toJson true), ("atoms", toJson ([] : List Json))]
    return claimType [Json.mkObj ([("a", toJson "function"), ("this", top),
      ("params", toJson (← params.mapM (annotationClaim ds · bound)))] ++
      (← match rest with
        | some e => do pure [("rest", ← annotationClaim ds e bound)]
        | none => pure []) ++
      [("result", ← annotationClaim ds result bound),
       ("construct", toJson "unknown"), ("array", toJson "unknown")])]
  let genericFunctions ← (← arr ast "functions").toList.filterMapM fun f => do
    let tps ← arr f "typeParams"
    if tps.isEmpty then return none
    let params ← arr f "params"
    let (fixed, rest) ← match params.toList.getLast? with
      | some p =>
        if (p.getObjVal? "rest").isOk then
          let ty ← field p "type"
          if (← str ty "k") != "array" || (← bool ty "readonly") then
            throw "a generic module function's rest parameter needs a mutable array contract"
          pure (params.toList.dropLast.map (fun q => (q.getObjVal? "type").toOption.getD .null), some (← field ty "element"))
        else pure (params.toList.map (fun q => (q.getObjVal? "type").toOption.getD .null), none)
      | none => pure ([], none)
    let result ← field f "retType"
    let binders ← tps.toList.mapM fun p => do return (← str p "name", ← field p "bound")
    let name ← str f "name"
    let pos ← fromJson? (α := Span) (← field f "namePos")
    let instantiate (σ : List (String × Json)) : Lowering (Json × List (String × Option Json)) := do
      let c ← callable fixed rest result σ
      let bounds ← binders.mapM fun (n, b) => do
        return (n, ← if b == .null then pure none else some <$> annotationClaim ds b σ)
      return (c, bounds)
    return some (name, pos, binders.map Prod.fst, instantiate)
  -- A generic class, a value of the top-level code: its constructor at each
  -- instance its uses name, read from the class's constructor type with the
  -- binders fixed. The initialization unit certifies the class at every
  -- assignment of its binders' rows.
  let genericClasses ← (← arr ast "init").toList.flatMapM fun st => do
    if (st.getObjValAs? String "k").toOption != some "const" then return []
    (← arr st "bindings").toList.filterMapM fun b => do
      let init ← field b "init"
      if (init.getObjValAs? String "k").toOption != some "ctor" then return none
      let some (.arr tps) := (init.getObjVal? "typeParams").toOption | return none
      if tps.isEmpty then return none
      let annot ← field b "annot"
      let binders ← tps.toList.mapM fun p => do return (← str p "name", ← field p "bound")
      let name ← str b "name"
      let pos ← fromJson? (α := Span) (← field b "namePos")
      let instantiate (σ : List (String × Json)) : Lowering (Json × List (String × Option Json)) := do
        let c ← annotationClaim ds annot σ
        let bounds ← binders.mapM fun (n, bd) => do
          return (n, ← if bd == .null then pure none else some <$> annotationClaim ds bd σ)
        return (c, bounds)
      return some (name, pos, binders.map Prod.fst, instantiate)
  let genericFunctions := genericFunctions ++ genericClasses
  let functionTree ← field ast "functions"
  let ((functions, memo), types) ← ((do let r ← rewrite ds functionTree; complete; pure r).run memo).run types
  -- A generic class's binders are in scope in every member, and the members
  -- are bindings of their own beside the class value: the top-level code's
  -- scope holds every generic class's binders, one per spelling.
  let classScope : List (String × Json) :=
    ((← arr ast "init").toList.flatMap fun st =>
      match (st.getObjVal? "bindings").toOption with
      | some (.arr bs) => bs.toList.flatMap fun b =>
        match ((b.getObjVal? "init").toOption.bind fun i => (i.getObjVal? "typeParams").toOption) with
        | some (.arr ps) => ps.toList.filterMap fun p => do
            return (← (p.getObjValAs? String "name").toOption, (p.getObjVal? "bound").toOption.getD .null)
        | _ => []
      | _ => [])
  let initTree ← field ast "init"
  let ((init, memo), types) ← ((do let r ← rewrite ds initTree classScope; complete; pure r).run memo).run types
  -- An imported value, at the type its declaration states: an assumption,
  -- read in claim form like an annotation. A generic one is instantiated at
  -- each call instead.
  let mut values : List (String × Span × Json) := []
  let mut generics := genericFunctions
  let mut types := types
  let mut memo := memo
  for v in ← arr document "values" do
    CellClaims.fieldsExactly v ["binding", "declaration", "construct", "typeParams", "type"]
    let binding ← field v "binding"
    CellClaims.fieldsExactly binding ["local", "imported", "specifier", "span"]
    let name ← str binding "local"
    let span ← fromJson? (α := Span) (← field binding "span")
    let _ ← bool v "construct"
    let ty ← field v "type"
    let binders ← (← arr v "typeParams").toList.mapM fun p => do
      CellClaims.fieldsExactly p ["name", "bound"]
      return (← str p "name", ← field p "bound")
    if binders.isEmpty then
      let ((claim, remembered), grown) ← ((do let c ← annotationClaim ds ty; complete; pure c).run memo).run types
      memo := remembered
      types := grown
      values := values ++ [(name, span, claim)]
    else
      let instantiate (σ : List (String × Json)) : Lowering (Json × List (String × Option Json)) := do
        let c ← annotationClaim ds ty σ
        let bounds ← binders.mapM fun (n, b) => do
          return (n, ← if b == .null then pure none else some <$> annotationClaim ds b σ)
        return (c, bounds)
      generics := generics ++ [(name, span, binders.map Prod.fst, instantiate)]
  let empty := Json.mkObj [("roots", toJson ([] : List Json)),
    ("definitions", toJson ([] : List Json)), ("values", toJson ([] : List Json)),
    ("symbols", toJson ([] : List Json))]
  let ast := ast.setObjVal! "declarations" empty
  -- An instance is lowered later, against the memo as the module left it.
  let instances := generics.map fun (name, pos, binders, instantiate) =>
    Instantiable.mk name pos binders fun σ => (do let r ← instantiate σ; complete; pure r).run' memo
  return ((ast.setObjVal! "functions" functions).setObjVal! "init" init, types, values, instances)

end Verification.Model.DeclarationGraph
