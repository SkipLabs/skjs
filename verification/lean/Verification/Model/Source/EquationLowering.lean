import Std.Data.HashMap
import Verification.Model.Types.EquationFamilies
import Verification.Model.Types.EquationValidator
import Verification.Model.Types.EquationJson
import Verification.Model.Programs.CertificateProducer
import Verification.Model.Source.RequestJson

/-! Lowering source declarations to recursive equations (RECURSIVE-EQUATIONS
§8). The parser's declaration document, the function tree's annotations and
the source-claims labels become one table of equations, validated by
`Equations.ofRaw`, and unions of closed labels over it. Heads are made per
source declaration, per unit and per type-literal occurrence, never per
instance, so a growing family (`Pair<[T, U]>`, `Promise`'s `catch`) is
finitely many heads. There is no budget, colour, depth limit or truncation:
an alias cycle not guarded by a constructor is refused, and everything else
terminates because heads are keyed by source occurrence.

Lowering is untrusted in what it proposes (the hash-consing of literal
heads) and trusted in what it states: the equations
are the meaning of the source. The source path reads it through
`EquationLowering.source` (`SourceClaimJson.equationFront`), and the store
extraction grows is its state (`EquationStore`). -/
namespace Verification.Model.EquationLowering
open Lean EquationGraphs PositiveGraphs PositiveNormalization PositiveRules PositiveCertificates
  CallEffects

/-- A union of trees: in a template, operands may hold placeholders; outside
one, every tree is closed. -/
abbrev Union := List Tree

def mkApp (h : Nat) (args : List Union) : Tree := .app h (Args.ofList (args.map Types.ofList))

def mkBound (h : Nat) (args : List Union) (j : Nat) : Tree :=
  .bound h (Args.ofList (args.map Types.ofList)) j

/-- A union in canonical order, each tree once. -/
def normUnion (u : Union) : Union :=
  (u.mergeSort fun a b => compare a b != .gt).eraseDups

/-- `normUnion`, under a name the tree traversals below read. -/
abbrev normUnionOf (u : Union) : Union := normUnion u

/-! ### Trees -/

/- Whether a tree holds a template placeholder. -/
mutual
partial def treeOpen : Tree → Bool
  | .app _ args | .bound _ args _ => argsOpen args
  | .argument _ | .local _ => true
  | .var .. => false
  | .meet ps => ps.toList.any treeOpen
partial def argsOpen (args : Args) : Bool :=
  args.toList.any fun ts => ts.toList.any treeOpen
end

/- Simultaneous substitution of placeholders. A meet is distributed over its
parts' images, each distributed meet in canonical form (§3.3). -/
mutual
partial def treeSubst (argF : Nat → Union) (locF : Nat → Union) : Tree → Union
  | .app h args => [.app h (argsSubst argF locF args)]
  | .bound h args j => [.bound h (argsSubst argF locF args) j]
  | .argument i => argF i
  | .local j => locF j
  | .var o s k => [.var o s k]
  | .meet ps => (choices (ps.toList.map (treeSubst argF locF))).map canonMeet
partial def argsSubst (argF : Nat → Union) (locF : Nat → Union) (args : Args) : Args :=
  Args.ofList (args.toList.map fun ts => Types.ofList (ts.toList.flatMap (treeSubst argF locF)))
end

/- Replacing closed subtrees: `f` gives the union a tree stands for, or
`none` to keep it and look inside. A meet is distributed over its parts'
images, each distributed meet in canonical form; each argument union is
kept canonical. -/
mutual
partial def treeReplace (f : Tree → Option Union) (t : Tree) : Union :=
  match f t with
  | some U => U
  | none => match t with
    | .app h args => [.app h (argsReplace f args)]
    | .bound h args j => [.bound h (argsReplace f args) j]
    | .meet ps => (choices (ps.toList.map (treeReplace f))).map canonMeet
    | t => [t]
partial def argsReplace (f : Tree → Option Union) (args : Args) : Args :=
  Args.ofList (args.toList.map fun ts => Types.ofList (normUnionOf (ts.toList.flatMap (treeReplace f))))
end

/- Renaming heads, meets and argument unions re-canonicalized: their order
depends on head indices, and one type has one spelling. -/
mutual
partial def treeRename (f : Nat → Nat) : Tree → Tree
  | .app h args => .app (f h) (argsRename f args)
  | .bound h args j => .bound (f h) (argsRename f args) j
  | .meet ps => canonMeet (ps.toList.map (treeRename f))
  | t => t
partial def argsRename (f : Nat → Nat) (args : Args) : Args :=
  Args.ofList (args.toList.map fun ts => Types.ofList (normUnion (ts.toList.map (treeRename f))))
end

/-- Whether a tree holds an owned parameter or a variable. -/
partial def hasRigid : Tree → Bool
  | .bound .. | .var .. => true
  | .app _ args => args.toList.any fun ts => ts.toList.any hasRigid
  | .meet ps => ps.toList.any hasRigid
  | _ => false

/-- Every closed meet in a tree, itself included. -/
partial def treeMeets : Tree → List Tree
  | .app _ args | .bound _ args _ => args.toList.flatMap fun ts => ts.toList.flatMap treeMeets
  | t@(.meet ps) => (if treeOpen t then [] else [t]) ++ ps.toList.flatMap treeMeets
  | _ => []

mutual
/-- A tree for a diagnostic, heads by name. -/
partial def showTree (names : Nat → String) : Tree → String
  | .app h args => names h ++ showArgs names args
  | .bound h args j => s!"{names h}{showArgs names args}#{j}"
  | .argument i => s!"arg {i}"
  | .local j => s!"local {j}"
  | .var o s _ => s!"?{o}.{s}"
  | .meet ps => "(" ++ " & ".intercalate (ps.toList.map (showTree names)) ++ ")"
partial def showArgs (names : Nat → String) (args : Args) : String :=
  if args.toList.isEmpty then "" else
    "<" ++ ", ".intercalate (args.toList.map fun ts => showUnion names ts.toList) ++ ">"
/-- A union for a diagnostic. -/
partial def showUnion (names : Nat → String) (U : Union) : String :=
  if U.isEmpty then "never" else " | ".intercalate (U.map (showTree names))
end

/-- The distributed meet of unions (§3.3): one canonical meet per choice. A
single part is itself. -/
def meetUnions : List Union → Union
  | [A] => A
  | parts => normUnion ((choices parts).map canonMeet)

/-- Rows over trees, mapped operand by operand. -/
def mapRow (f : Union → Union) (row : GraphRow Tree (List Tree)) : GraphRow Tree (List Tree) :=
  row.map id f

/-! ### The declaration document -/

structure Definition where
  identity : Json
  name : String
  parameters : Array Json
  bases : Array Json
  expression : Json
  deriving Inhabited

private def field (j : Json) (name : String) : Except String Json := j.getObjVal? name
private def arr (j : Json) (name : String) : Except String (Array Json) := do (← field j name).getArr?
private def str (j : Json) (name : String) : Except String String := do (← field j name).getStr?
private def bool (j : Json) (name : String) : Except String Bool := do (← field j name).getBool?

private def definitions (document : Json) : Except String (Array Definition) := do
  (← arr document "definitions").mapM fun j => do
    fieldsExactly j ["declaration", "parameters", "bases", "expression"]
    let identity ← field j "declaration"
    return ⟨identity, ← str identity "name", ← arr j "parameters", ← arr j "bases", ← field j "expression"⟩

/-- `ArrayProto`'s identity, the synthetic declaration array types name. -/
def arrayProtoIdentity : Json :=
  Json.mkObj [("module", "skjs/array-prototype"), ("name", "ArrayProto"), ("span", toJson [0, 0])]

/-- An object term's index signatures, by the keys each constrains. -/
private def indexSignatures (term : Json) : List (String × IndexKeys × Json) :=
  [("stringIndex", IndexKeys.strings, term.getObjVal? "stringIndex"),
   ("numberIndex", .numeric, term.getObjVal? "numberIndex"),
   ("symbolIndex", .symbols, term.getObjVal? "symbolIndex")].filterMap
    fun (name, keys, index) => match index with
      | .ok .null | .error _ => none
      | .ok index => some (name, keys, index)

private def objectMembers (term : Json) : List String :=
  ["k", "fields", "stringIndex", "calls", "span"] ++
    ((indexSignatures term).map (·.1)).filter (· != "stringIndex") ++
    if (term.getObjVal? "prototype").toOption.isSome then ["prototype"] else []

private def kindOf (term : Json) : Option String := (term.getObjValAs? String "k").toOption

/-- A declaration is a head when its equation is an object type, an
interface's or class's, or it has bases. Any other is an alias, inlined at
each use (§8.3). -/
def Definition.isHead (d : Definition) : Bool :=
  kindOf d.expression == some "object" || !d.bases.isEmpty

/-- Uses of one method binder: as a value, as an argument pack. A nested
scheme binding the same name shadows it. -/
structure BinderUse where
  value : Bool := false
  pack : Bool := false
  deriving Inhabited, BEq

private def BinderUse.merge (a b : BinderUse) : BinderUse := ⟨a.value || b.value, a.pack || b.pack⟩

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
  | _ => {}

/-- The types a method form's host must meet: none for the declaration as
receiver (`self`), the other parts for its intersection with the type a
`this` parameter states. -/
private def statedReceivers (f : Json) : Option (Array Json) :=
  let r := (f.getObjVal? "receiver").toOption
  match r.bind kindOf with
  | some "self" => some #[]
  | some "intersection" =>
    let parts := (r.bind fun r => (r.getObjValAs? (Array Json) "parts").toOption).getD #[]
    let stated := parts.filter (kindOf · != some "self")
    if parts.size - stated.size == 1 && !stated.isEmpty then some stated else none
  | _ => none

/-- A field's method forms: one signature or an intersection of several, each
with the declaration as receiver, or its intersection with stated types. -/
private def methodForms (t : Json) : Option (Array Json) :=
  let forms := if kindOf t == some "intersection"
    then (t.getObjValAs? (Array Json) "parts").toOption.getD #[] else #[t]
  if !forms.isEmpty && forms.all (fun f => kindOf f == some "function" &&
      (statedReceivers f).isSome)
  then some forms else none

/-- A generic method: a scheme whose signatures take the declaration as
receiver. The forwarding function ignores the receiver it is given, so the
scheme's own receivers admit any value. -/
private def schemeMethod (t : Json) : Option Json := do
  guard (kindOf t == some "scheme")
  let sigs ← (t.getObjValAs? (Array Json) "signatures").toOption
  guard (!sigs.isEmpty && sigs.all fun f => ((f.getObjVal? "receiver").toOption.bind kindOf) == some "self")
  let anyReceiver (f : Json) : Json := f.setObjVal! "receiver"
    (Json.mkObj [("k", "atom"), ("name", "unknown"), ("span", f.getObjValD "span")])
  return t.setObjVal! "signatures" (toJson (sigs.map anyReceiver))

/-! ### Scopes -/

/-- What a term may name from its surroundings: a parameter of the
declaration it is written in, a binder, or the declaration's receiver. -/
inductive Item where
  | param (index : Nat)
  | binder (name : String)
  | self
  deriving BEq, Repr

private def Item.push (acc : Array Item) (i : Item) : Array Item :=
  if acc.contains i then acc else acc.push i

/-- The items a term mentions, in first-occurrence order. A nested scheme's
binders shadow; a method form's `self` receiver is dropped by lowering, so it
is no mention. -/
partial def mentionsAux (shadow : List String) (acc : Array Item) : Json → Array Item
  | .arr xs => xs.foldl (mentionsAux shadow) acc
  | j@(.obj kvs) =>
    match kindOf j with
    | some "parameter" => match (j.getObjValAs? Nat "index").toOption with
      | some i => Item.push acc (.param i)
      | none => acc
    | some "binder" => match (j.getObjValAs? String "name").toOption with
      | some n => if shadow.contains n then acc else Item.push acc (.binder n)
      | none => acc
    | some "self" => Item.push acc .self
    | some "scheme" =>
      let bs := (j.getObjValAs? (Array Json) "binders").toOption.getD #[]
      let names := bs.toList.filterMap fun b => (b.getObjValAs? String "name").toOption
      let acc := bs.foldl (fun acc b => mentionsAux shadow acc (b.getObjValD "bound")) acc
      mentionsAux (names ++ shadow) acc (j.getObjValD "signatures")
    | some "object" =>
      kvs.toList.foldl (fun acc (k, v) =>
        if k != "fields" then mentionsAux shadow acc v else
        ((v.getArr?).toOption.getD #[]).foldl (fun acc f =>
          let ty := f.getObjValD "type"
          let optional := (f.getObjValAs? Bool "optional").toOption.getD false
          match (if optional then none else methodForms ty), (if optional then none else schemeMethod ty) with
          | some forms, _ => forms.foldl (fun acc form =>
              let acc := ((statedReceivers form).getD #[]).foldl (mentionsAux shadow) acc
              ["params", "rest", "result"].foldl (fun acc k => mentionsAux shadow acc (form.getObjValD k)) acc) acc
          | none, some t => mentionsAux shadow acc t
          | none, none => mentionsAux shadow acc ty) acc) acc
    | _ => kvs.toList.foldl (fun acc (_, v) => mentionsAux shadow acc v) acc
  | _ => acc

def mentions (shadow : List String) (term : Json) : List Item :=
  (mentionsAux shadow #[] term).toList

/-- A binder in scope: its kind and what it stands for here. -/
structure Binding where
  pack : Bool
  value : Union
  deriving Repr, Inhabited

/-- Where a term is lowered: the declaration its `parameter` and `self`
terms belong to, and their values; the binders in scope; the aliases being
inlined since the last constructor (guardedness, §8.3); the head whose row is
being built; and the site diagnostics name. Values are in the placeholder
space of the row being built, or closed outside one. -/
structure Ctx where
  decl : Option Nat := none
  params : Array Union := #[]
  self : Option Union := none
  binders : List (String × Binding) := []
  aliases : List Nat := []
  owner : Option Nat := none
  site : String := ""
  /-- The declared bounds of the placeholders in scope (`arg i`, `local j`),
  read when a bound obligation inside the template is checked (§8.2). -/
  bounds : List (Tree × Union) := []
  /-- Whether an application's declared bounds are checked here: where the
  source writes it. A claim's are not: a claim is a proposal the program is
  checked against, and bounds carry no meaning (§8.2). -/
  checkBounds : Bool := true
  deriving Inhabited

/-! ### Heads under construction -/

inductive HeadKind where
  | primitive
  | declaration (index : Nat)
  | method (owner : Nat) (key : String)
  | literal
  | scheme
  | unit (key : String)
  | array (readonly : Bool)
  | proto
  deriving BEq, Repr, Inhabited

/-- A head as lowering builds it: `body` is filled once its row is lowered. -/
structure Draft where
  name : String
  kind : HeadKind
  kinds : List ParameterKind
  binders : List Binder := []
  body : Option (GraphRow Tree (List Tree)) := none
  deriving Inhabited

/-- The producer's rows, each with its own binders (a scheme row's) and the
binder names it mentions freely, in first-occurrence order. -/
structure ProducerRows where
  rows : Array (GraphRow Json (List Json))
  own : Array (List String)
  free : Array (List String)
  deriving Inhabited

/-- The binder names and the rows a label mentions. A declaration's position
is no row. -/
partial def labelRefs (j : Json) : List String × List Nat :=
  let many (xs : List Json) : List String × List Nat :=
    xs.foldl (fun (ns, rs) x => let (n, r) := labelRefs x; (ns ++ n, rs ++ r)) ([], [])
  match j with
  | .num _ => ([], (j.getNat?).toOption.toList)
  | .arr xs => many xs.toList
  | .obj _ =>
    match (j.getObjValAs? String "binder").toOption with
    | some n => ([n], [])
    | none =>
      let unions (k : String) : List Json := ((j.getObjValAs? (Array Json) k).toOption.getD #[]).toList
      many (unions "args" ++ unions "meet" ++ ((j.getObjVal? "array").toOption.toList))
  | _ => ([], [])

/-- The producer's rows, decoded, with what each binds and names freely. -/
def producerRows (types : Array Json) : Except String ProducerRows := do
  let rows ← types.mapM fun j => (fromJson? j : Except String (GraphRow Json (List Json)))
  let own ← rows.mapM fun r => match r with
    | .scheme bs .. => bs.mapM fun b => do
      fieldsExactly b ["binder"]
      str b "binder"
    | .clauses _ => pure []
    | _ => throw "a producer's row is a clause row or a scheme row; binders and intersections are labels"
  let direct := rows.map fun r => r.operands.foldl (fun (ns, rs) A =>
    let (n, r) := labelRefs (.arr A.toArray); (ns ++ n, rs ++ r)) (([] : List String), ([] : List Nat))
  if direct.any (fun (_, rs) => rs.any (· ≥ rows.size)) then throw "a label names no row of the table"
  -- The free names: a least fixpoint over the finitely many rows and names.
  let step (free : Array (List String)) : Array (List String) :=
    (Array.range rows.size).map fun n =>
      let (ns, rs) := direct[n]!
      ((ns ++ rs.flatMap fun m => free[m]!).filter (!own[n]!.contains ·)).eraseDups
  let mut free : Array (List String) := rows.map fun _ => []
  let total := (direct.toList.flatMap (·.1)).eraseDups.length * rows.size + 1
  for _ in [0:total] do
    let next := step free
    if next == free then break
    free := next
  return { rows, own, free }

/-- A row still to lower. -/
inductive Job where
  | declaration (head index : Nat)
  | term (head : Nat) (ctx : Ctx) (term : Json)
  | store (head : Nat) (ctx : Ctx) (term : Json)
  | pack (head : Nat) (ctx : Ctx) (required : List Json) (rest : Option Json)
  | scheme (head : Nat) (ctx : Ctx) (term : Json)
  | unit (head : Nat) (ctx : Ctx) (node : Json)
  /-- A producer's row (§9.1): its index in the document's `types`. -/
  | row (head : Nat) (index : Nat)
  deriving Inhabited

def Job.head : Job → Nat
  | .declaration h _ | .term h .. | .store h .. | .pack h .. | .scheme h .. | .unit h .. | .row h _ => h

/-- A declared bound to check where an application is written (§8.2): the
actual union within the declared one. Inside a template, `owner` is the head
whose placeholders they hold. -/
structure Obligation where
  actual : Union
  upper : Union
  /-- The bounds of the placeholders `actual` and `upper` may hold. -/
  bounds : List (Tree × Union)
  site : String

/-- An array or tuple annotation by its parts: what a reader of the
annotation's shape, a rest parameter's, needs (`Fragment.arrayElement`). -/
structure ArrayParts where
  required : List Union
  optional : List Union
  rest : Option Union
  readonly : Bool
  presence : Json
  deriving Inhabited

def ArrayParts.map (f : Union → Union) (a : ArrayParts) : ArrayParts :=
  { a with required := a.required.map f, optional := a.optional.map f, rest := a.rest.map f }

structure State where
  /-- Execution policy; the equation document records only the types. -/
  subtypeBudget : PositiveCertificates.SearchBudget := {}
  doc : Array Definition
  heads : Array Draft := #[]
  keys : Std.HashMap String Nat := {}
  jobs : List Job := []
  processing : List Nat := []
  excluded : List PropKey := []
  arrays : Bool := false
  obligations : List Obligation := []
  /-- Each written intersection's union of meets, with where it is written:
  an intersection none of whose meets has a value is refused there. -/
  meetChecks : List (Union × String) := []
  /-- Each generic unit's binders, by the unit's path. -/
  scopes : List (String × List (String × Binding)) := []
  /-- Each generic unit's binders, by the unit's path: each an owned
  parameter of the unit's head, with its declared bound, if any, over those
  parameters. -/
  unitBinders : List (String × List (String × Tree × Option Union)) := []
  /-- The binder names the source spells, each with its kind: the slots of
  the name placeholders (`placeholder`). -/
  names : Array (String × ParameterKind) := #[]
  /-- The names of the fresh placeholders `EquationStore.binders` has made, by slot. -/
  fresh : Array String := #[]
  /-- The realm's array prototype head, once lowered. -/
  proto : Option Nat := none
  /-- Each array or tuple annotation's parts, by its path. -/
  arrayAnnotations : List (String × ArrayParts) := []
  /-- The producer's rows the claims name (§9.1). -/
  rows : ProducerRows := default

abbrev M := StateT State (Except String)

/-- The owner of name placeholders: a binder the source spells by its name,
`T`, is lowered as the placeholder of that name until a unit or closure
decides what the name stands for (`EquationStore.rebind`). Placeholders are
family-variable trees of a reserved owner, parameter rows of their kind; no
checked request holds one (`EquationStore.freeze` refuses it). -/
def nameOwner : Nat := 4000000000

/-- The owner of fresh placeholders: a scheme's binders before its head
binds them (`EquationStore.binders`, `EquationStore.scheme`). -/
def freshOwner : Nat := 4000000001

/-- Whether a tree is a placeholder. -/
def isPlaceholder : Tree → Bool
  | .var o _ _ => o == nameOwner || o == freshOwner
  | _ => false

/-- The name placeholder of a binder name and kind. -/
def placeholder (name : String) (kind : ParameterKind) : M Tree := do
  let s ← get
  match s.names.toList.idxOf? (name, kind) with
  | some i => return .var nameOwner i kind
  | none =>
    set { s with names := s.names.push (name, kind) }
    return .var nameOwner s.names.size kind

/-- The head with key `key`, allocated with `draft` and its row's job when
new. -/
def alloc (key : String) (draft : Draft) (job : Nat → Option Job) : M Nat := do
  if let some h := (← get).keys.get? key then return h
  let h := (← get).heads.size
  modify fun s =>
    { s with heads := s.heads.push draft, keys := s.keys.insert key h, jobs := s.jobs ++ (job h).toList }
  return h

def setBody (h : Nat) (row : GraphRow Tree (List Tree)) : M Unit :=
  modify fun s => { s with heads := s.heads.modify h fun d => { d with body := some row } }

def draft (h : Nat) : M Draft := do
  match (← get).heads[h]? with
  | some d => return d
  | none => throw s!"no head {h}"

/-- A nullary head whose row is the given clauses, hash-consed by them. -/
def ground (name : String) (cs : List (Clause (List Tree))) : M Tree := do
  let key := s!"ground|{reprStr cs}"
  let h ← alloc key { name, kind := .primitive, kinds := [], body := some (.clauses cs) } fun _ => none
  return mkApp h []

def prim (name : String) (c : Clause (List Tree)) : M Tree := ground name [c]

/-- The four primitive values' heads come first, as `LabelStore.Labels`
requires: `null`, `true`, `false`, `undefined`. -/
def primitives : M Unit := do
  let _ ← prim "null" .nul
  let _ ← prim "true" (.boolLit true)
  let _ ← prim "false" (.boolLit false)
  let _ ← prim "undefined" .undef

def top : M Tree := prim "unknown" .top

/-- The empty intersection's refusal. -/
def emptyMeet : String :=
  "the intersection is empty: its operands have no value in common (no value has two shapes, and an array owns no key its prototype provides), and an empty intersection is refused rather than verified vacuously"

/-- Two operands' clauses as TypeScript meets them: the model's meet, except
that a record of invariant fields met with a function type is the function
carrying those fields, a `callable`. -/
def sourceMeetLists [BEq α] (A B : List (Clause α)) : Except String (List (Clause α)) := do
  let plainRecord (c : Clause α) : Bool := match c with
    | .refs .. => !c.presentKeys.contains CallArguments.arrayStoreField
    | .dict .. => true
    | _ => false
  let calls (c : Clause α) : Bool := match c with
    | .arrs .. | .callable .. => true
    | _ => false
  let pair (a b : Clause α) : List (Clause α) :=
    match a, b with
    | .refs f fs [] [] [] [], .arrs L S | .arrs L S, .refs f fs [] [] [] [] => [.callable f fs L S]
    | .refs f fs [] [] [] [], .callable c cs L S | .callable c cs L S, .refs f fs [] [] [] [] =>
      [.callable (f ++ c) (fs ++ cs) L S]
    | a, b => (PositiveNormalization.meet a b).filter Clause.consistent
  let pairs := A.flatMap fun a => B.map fun b => (a, b)
  let met := pairs.flatMap fun (a, b) => pair a b
  if met.isEmpty && pairs.any (fun (a, b) => (plainRecord a && calls b) || (calls a && plainRecord b)) then
    throw "the intersection of a function type and a record with readonly or optional fields, methods or an index is a callable with them, which no clause states"
  return met

/-- A clause row's template at arguments. -/
def instantiateClauses (cs : List (Clause (List Tree))) (args : List Union) : List (Clause (List Tree)) :=
  cs.map (Clause.map (·.flatMap (treeSubst (fun i => args.getD i []) (fun j => [.local j]))))

def ctxValue (ctx : Ctx) : Item → Except String Union
  | .param i => match ctx.params[i]? with
    | some v => .ok v
    | none => .error s!"{ctx.site}: declaration parameter index {i} outside the application"
  | .binder n => match ctx.binders.lookup n with
    | some b => .ok b.value
    | none => .error s!"{ctx.site}: the type parameter {n} is not in scope"
  | .self => match ctx.self with
    | some v => .ok v
    | none => .error s!"{ctx.site}: a receiver outside a declaration's methods"

def ctxKind (ctx : Ctx) : Item → ParameterKind
  | .binder n => if (ctx.binders.lookup n).any (·.pack) then .arguments else .value
  | _ => .value

/-- The scope inside a head lifted over `items`: each item is its argument. -/
def liftedCtx (ctx : Ctx) (items : List Item) (h : Nat) : Ctx :=
  let indexed := items.zipIdx
  let size := indexed.foldl (fun n (it, _) => match it with | .param i => max n (i + 1) | _ => n) 0
  { decl := ctx.decl
    params := (Array.range size).map fun i =>
      match indexed.find? (fun (it, _) => it == .param i) with
      | some (_, j) => [.argument j]
      | none => []
    self := (indexed.find? (·.1 == .self)).map fun (_, j) => [.argument j]
    binders := indexed.filterMap fun (it, j) => match it with
      | .binder n => some (n, ⟨(ctx.binders.lookup n).any (·.pack), [.argument j]⟩)
      | _ => none
    owner := some h
    site := ctx.site
    checkBounds := ctx.checkBounds
    bounds := ctx.bounds.filterMap fun (p, U) => do
      let (_, j) ← indexed.find? fun (it, _) => (ctxValue ctx it).toOption == some [p]
      let moved (q : Tree) : Option Union :=
        (indexed.find? fun (it, _) => (ctxValue ctx it).toOption == some [q]).map fun (_, k) => [.argument k]
      -- A bound naming what the head is lifted over names its argument.
      let U' ← U.mapM fun t => match moved t with
        | some m => some m
        | none => if treeOpen t then none else some [t]
      return (.argument j, U'.flatten) }

def literalName (term : Json) : String :=
  s!"literal {(kindOf term).getD "?"} at {(term.getObjValD "span").compress}"

/-- The head of a source occurrence, lifted over the items it mentions and
applied to their values here (§8.1). The key is the occurrence's text and the
kinds of what it mentions: equal keys lower to equal templates. -/
def occurrence (ctx : Ctx) (tag : String) (term : Json) (shadow : List String := [])
    (binders : List Binder := []) (job : Nat → Ctx → Job) : M Tree := do
  let items := mentions shadow term
  let args ← items.mapM fun it => (ctxValue ctx it : Except String Union)
  let kinds := items.map (ctxKind ctx)
  let key := s!"{tag}|{reprStr kinds}|{term.compress}"
  let kind := if tag == "scheme" then HeadKind.scheme else .literal
  let h ← alloc key { name := literalName term, kind, kinds, binders } fun h =>
    some (job h (liftedCtx ctx items h))
  return mkApp h args

/-- The array heads and the realm's prototype. Without an `ArrayProto`
declaration in the document (a library bound naming an array, in a source
with none), the prototype is an object of which nothing is known. -/
def arrayHead (readonly : Bool) (proto : Tree) : M Nat := do
  let excluded := (← get).excluded
  modify fun s => { s with arrays := true }
  alloc s!"array|{readonly}"
    { name := if readonly then "ReadonlyArray" else "Array", kind := .array readonly, kinds := [.value],
      body := some (.clauses [arrayClauseOf [.argument 0] [proto] excluded readonly]) } fun _ => none

/-! ### Heads added after the declarations

What the store adds while a unit is extracted (`EquationStore`): a union of
clauses, a scheme over fresh binders, a bounded binder's meet. A template
holds no owned parameter or variable (§3.1: it names parameters only through
its arguments), so each such closed subtree is lifted to an argument, as a
literal is lifted over the binders it mentions (§8.1). The head is keyed by
the lifted template, so equal templates share a head. -/

/-- A closed subtree a template cannot hold. -/
def Tree.rigid : Tree → Bool
  | .bound .. | .var .. => true
  | _ => false

/-- A tree with its rigid subtrees lifted to arguments, in first-occurrence
order: the arguments so far and the template. -/
partial def liftTree (acc : Array Tree) : Tree → Array Tree × Tree
  | t@(.bound ..) | t@(.var ..) =>
    match acc.toList.idxOf? t with
    | some i => (acc, .argument i)
    | none => (acc.push t, .argument acc.size)
  | .app h args =>
    let (acc, ts) := args.toList.foldl (fun (acc, out) ts =>
      let (acc, us) := ts.toList.foldl (fun (acc, us) u =>
        let (acc, u) := liftTree acc u
        (acc, us ++ [u])) (acc, [])
      (acc, out ++ [Types.ofList us])) (acc, [])
    (acc, .app h (Args.ofList ts))
  | .meet ps =>
    let (acc, us) := ps.toList.foldl (fun (acc, us) u =>
      let (acc, u) := liftTree acc u
      (acc, us ++ [u])) (acc, [])
    (acc, canonMeet us)
  | t => (acc, t)

def liftUnion (acc : Array Tree) (U : Union) : Array Tree × Union :=
  U.foldl (fun (acc, out) t => let (acc, t) := liftTree acc t; (acc, out ++ [t])) (acc, [])

/-- A rigid subtree's kind: an owned parameter's is its binder's, a
variable's its own. -/
def rigidKindIn (heads : Array Draft) : Tree → ParameterKind
  | .bound h _ j => ((heads[h]?.bind (·.binders[j]?)).map (·.kind)).getD .value
  | .var _ _ k => k
  | _ => .value

/-- Clauses with their rigid subtrees lifted: the arguments and the
template. -/
def liftClauses (cs : List (Clause (List Tree))) : Array Tree × List (Clause (List Tree)) :=
  cs.foldl (fun (acc, out) c =>
    let ops := c.operands
    let (acc, lifted) := ops.foldl (fun (acc, out) U =>
      let (acc, U) := liftUnion acc U
      (acc, out ++ [U])) (acc, [])
    let table := ops.zip lifted
    (acc, out ++ [c.map fun U => (table.lookup U).getD U])) ((#[] : Array Tree), [])

/-- The key of a union of clauses' head, and what it is applied to: the key
`ground` gives when nothing is lifted. -/
def internKey (heads : Array Draft) (cs : List (Clause (List Tree))) : String × List Union :=
  let (acc, cs') := liftClauses cs
  if acc.isEmpty then (s!"ground|{reprStr cs}", [])
  else (s!"lifted|{reprStr (acc.toList.map (rigidKindIn heads))}|{reprStr cs'}", acc.toList.map ([·]))

/-- The label of a union of clauses: its head, lifted over its rigid
subtrees, applied to them. Nullary when there are none, and then the head
`ground` would give. -/
def internLifted (name : String) (cs : List (Clause (List Tree))) : M Tree := do
  let (acc, cs') := liftClauses cs
  if acc.isEmpty then return ← ground name cs
  let heads := (← get).heads
  let (key, args) := internKey heads cs
  let h ← alloc key
    { name, kind := .literal, kinds := acc.toList.map (rigidKindIn heads), body := some (.clauses cs') }
    fun _ => none
  return mkApp h args

/-- A fresh placeholder for a scheme's binder, until the scheme's head binds
it (`schemeOver`). -/
def freshBinder (name : String) : M Tree := do
  let s ← get
  set { s with fresh := s.fresh.push name }
  return .var freshOwner s.fresh.size .value

/-- A scheme over binders from `freshBinder`: its head's template has the
binders as its locals, and every other rigid subtree lifted. The label is the
head applied to what was lifted; its binders are the head's owned
parameters, which the caller reads from the label's row. -/
def schemeOver (binders : List Tree) (sigs : List (Arrow (List Tree))) (bounds : List (Tree × List Tree))
    (rests : List (RestArrow (List Tree))) : M Tree := do
  let loc (t : Tree) : Option Union := (binders.idxOf? t).map fun j => [.local j]
  let local_ (U : Union) : Union := U.flatMap (treeReplace loc)
  let sigs := sigs.map (Arrow.map local_)
  let rests := rests.map (RestArrow.map local_)
  let bounds := bounds.filterMap fun (b, U) => (binders.idxOf? b).map fun j => (Tree.local j, local_ U)
  let liftA (acc : Array Tree) (a : Arrow (List Tree)) : Array Tree × Arrow (List Tree) :=
    let ops := a.operands
    let (acc, lifted) := ops.foldl (fun (acc, out) U =>
      let (acc, U) := liftUnion acc U; (acc, out ++ [U])) (acc, [])
    (acc, a.map fun U => ((ops.zip lifted).lookup U).getD U)
  let liftR (acc : Array Tree) (a : RestArrow (List Tree)) : Array Tree × RestArrow (List Tree) :=
    let ops := a.operands
    let (acc, lifted) := ops.foldl (fun (acc, out) U =>
      let (acc, U) := liftUnion acc U; (acc, out ++ [U])) (acc, [])
    (acc, a.map fun U => ((ops.zip lifted).lookup U).getD U)
  let (acc, sigs) := sigs.foldl (fun (acc, out) a => let (acc, a) := liftA acc a; (acc, out ++ [a]))
    ((#[] : Array Tree), [])
  let (acc, bounds) := bounds.foldl (fun (acc, out) (b, U) =>
    let (acc, U) := liftUnion acc U; (acc, out ++ [(b, U)])) (acc, [])
  let (acc, rests) := rests.foldl (fun (acc, out) a => let (acc, a) := liftR acc a; (acc, out ++ [a]))
    (acc, [])
  let kinds := acc.toList.map (rigidKindIn (← get).heads)
  let s ← get
  let names := binders.map fun b => match b with
    | .var o i _ => if o == freshOwner then (s.fresh[i]?).getD "_" else "_"
    | _ => "_"
  let bs : List Binder := (names.zip binders).map fun (n, b) => ⟨n, match b with
    | .var _ _ k => k
    | _ => .value⟩
  let row : GraphRow Tree (List Tree) :=
    .scheme ((List.range binders.length).map Tree.local) sigs bounds rests
  let key := s!"schemeOver|{reprStr kinds}|{reprStr bs}|{reprStr row}"
  let h ← alloc key { name := "scheme", kind := .scheme, kinds, binders := bs, body := some row }
    fun _ => none
  return mkApp h (acc.toList.map ([·]))

/-! ### Lowering source types -/

private def unitBinders (names : List String) (packs : List String) : List Binder :=
  names.map fun n => ⟨n, if packs.contains n then .arguments else .value⟩

/-- A scheme's binders, their kinds, and the refusals of forms a scheme
cannot state. -/
def schemeBinders (site : String) (term : Json) : Except String (List String × List String) := do
  fieldsExactly term ["k", "binders", "signatures", "span"]
  let bs ← arr term "binders"
  let sigTerms ← arr term "signatures"
  let refuse (reason : String) : Except String Unit :=
    throw s!"{site}: generic contract at {(term.getObjValD "span").compress}: {reason}; the contract cannot be erased"
  let names ← bs.toList.mapM fun b => do
    fieldsExactly b ["name", "bound", "default", "span"]
    str b "name"
  let own (j : Json) : Bool := names.any fun n => let u := binderUse n j; u.value || u.pack
  if bs.any (fun b => own (b.getObjValD "bound")) then refuse "dependent method bounds are not represented"
  let uses : List (String × BinderUse) := names.map fun n => (n, binderUse n (.arr sigTerms))
  if uses.any (fun (p : String × BinderUse) => p.2.pack && p.2.value) then
    refuse "a binder used as both a value and an argument pack is not represented"
  return (names, (uses.filter fun (p : String × BinderUse) => p.2.pack).map Prod.fst)

def referenceIndex (term : Json) : M Nat := do
  fieldsExactly term ["k", "reference", "args", "span"]
  let target ← field (← field term "reference") "target"
  let ds := (← get).doc
  match (List.range ds.size).filter fun i => ds[i]!.identity == target with
  | [i] => return i
  | [] => throw "reference has no declaration equation"
  | _ => throw "duplicate declaration identity"

/-- A literal type's labels. A numeric zero is both zeros, as TypeScript's
literal type `0` is. -/
def literalLabels (term : Json) : M Union := do
  fieldsExactly term ["k", "name", "text", "span"]
  match ← str term "name" with
  | "true" => return [← prim "true" (.boolLit true)]
  | "false" => return [← prim "false" (.boolLit false)]
  | "number" =>
    let text ← str term "text"
    let bits ← (Model.numBits text : Except String UInt64)
    let one ← prim s!"{text}" (.numLit bits)
    if Float.ofBits bits == 0.0 then
      return [one, ← prim "-0" (.numLit (9223372036854775808 : UInt64))]
    return [one]
  | "string" => let text ← str term "text"; return [← prim (Json.str text).compress (.strLit text)]
  | "bigint" =>
    let text ← str term "text"
    return [← prim s!"{text}n" (.bigintLit (← (Verification.decodeBigint text : Except String Int)))]
  | _ => throw "unsupported source literal"

def atomLabels (term : Json) : M Union := do
  match ← str term "name" with
  | "null" => return [← prim "null" .nul]
  | "undefined" => return [← prim "undefined" .undef]
  | "boolean" => return [← prim "true" (.boolLit true), ← prim "false" (.boolLit false)]
  | "number" => return [← prim "number" .num]
  | "string" => return [← prim "string" .str]
  | "bigint" => return [← prim "bigint" .bigint]
  | "symbol" => return [← prim "symbol" .symbol]
  | "unknown" | "void" => return [← top]
  | "never" => return []
  | "object" =>
    return normUnion [← prim "object" (.refs [] [] []), ← prim "function" (.arrs [] []),
      ← prim "constructor" (.ctors [])]
  | _ => throw "unsupported declaration primitive"

mutual
/-- A source type as a union of trees in `ctx`. -/
partial def lowerType (ctx : Ctx) (term : Json) : M Union := do
  match ← str term "k" with
  | "atom" => atomLabels term
  | "literal" => literalLabels term
  | "union" => return normUnion ((← (← arr term "parts").mapM (lowerType ctx)).toList.flatten)
  | "intersection" => intersect ctx term
  | "parameter" =>
    fieldsExactly term ["k", "index", "span"]
    ctxValue ctx (.param (← (← field term "index").getNat?))
  | "self" =>
    fieldsExactly term ["k", "span"]
    ctxValue ctx .self
  | "binder" =>
    fieldsExactly term ["k", "name", "span"]
    let n ← str term "name"
    match ctx.binders.lookup n with
    | some ⟨false, v⟩ => return v
    | some ⟨true, _⟩ => throw s!"{ctx.site}: an argument pack used as a value type"
    | none => throw s!"{ctx.site}: the type parameter {n} is not in scope"
  | "reference" => reference ctx term
  | "array" | "tuple" =>
    let readonly ← bool term "readonly"
    let store ← occurrence ctx "store" term (job := fun h c => .store h c term)
    let proto ← protoLabel
    return [mkApp (← arrayHead readonly proto) [[store]]]
  | "function" | "constructor" | "object" =>
    return [← occurrence ctx "literal" term (job := fun h c => .term h c term)]
  | "callable" =>
    fieldsExactly term ["k", "span"]
    return normUnion [← prim "function" (.arrs [] []), ← prim "constructor" (.ctors [])]
  | "scheme" =>
    let (names, packs) ← schemeBinders ctx.site term
    return [← occurrence ctx "scheme" term names (unitBinders names packs) fun h c => .scheme h c term]
  | "pack" => throw s!"{ctx.site}: a pack parameter outside a signature's rest"
  | k => throw s!"{ctx.site}: source type constructor '{k}' outside the graph fragment"

/-- A rest's type: a pack binder, or the pack of any number of actuals at an
element. -/
partial def lowerRest (ctx : Ctx) (term : Json) : M Union := do
  if kindOf term == some "pack" then
    fieldsExactly term ["k", "of", "span"]
    let operand ← field term "of"
    if kindOf operand != some "binder" then throw s!"{ctx.site}: a pack rest must name a type parameter"
    match ctx.binders.lookup (← str operand "name") with
    | some ⟨true, v⟩ => return v
    | some ⟨false, _⟩ => throw s!"{ctx.site}: a value parameter used as an argument pack"
    | none => throw s!"{ctx.site}: a pack parameter outside its generic method"
  return [← occurrence ctx "pack" term (job := fun h c => .pack h c [] (some term))]

/-- The realm's array prototype. -/
partial def protoLabel : M Tree := do
  let ds := (← get).doc
  if ds[0]?.any (·.identity == arrayProtoIdentity) then
    return mkApp (← declHead 0) []
  let d : Draft := { name := "ArrayProto", kind := .proto, kinds := [] }
  let h ← alloc "proto" { d with body := some (.clauses [.refs [] [] []]) } fun _ => none
  return mkApp h []

/-- A declaration's head, its row lowered later. -/
partial def declHead (i : Nat) : M Nat := do
  let d := (← get).doc[i]!
  let kind := if d.identity == arrayProtoIdentity then HeadKind.proto else .declaration i
  alloc s!"decl|{i}" { name := d.name, kind, kinds := List.replicate d.parameters.size .value }
    fun h => some (.declaration h i)

/-- A reference: its arguments, with defaults completed and bounds checked,
applied to the declaration's head or inlined into its alias. -/
partial def reference (ctx : Ctx) (term : Json) : M Union := do
  let i ← referenceIndex term
  let supplied ← (← arr term "args").mapM (lowerType ctx)
  let values ← application ctx i supplied.toList
  instantiateDecl ctx i values

/-- Complete an application's arguments with its defaults, which may mention
earlier parameters, and record its bound obligations. -/
partial def application (ctx : Ctx) (i : Nat) (supplied : List Union) : M (List Union) := do
  let d := (← get).doc[i]!
  if supplied.length > d.parameters.size then throw s!"{ctx.site}: {d.name} applied to too many type arguments"
  let mut values := supplied.toArray
  for p in d.parameters.toList.drop supplied.length do
    fieldsExactly p ["name", "span", "bound", "default"]
    let default ← field p "default"
    if default == .null then throw s!"{ctx.site}: {d.name} applied without its required argument {← str p "name"}"
    values := values.push (← lowerType { ctx with decl := some i, params := values, self := none, binders := [] } default)
  for index in [:d.parameters.size] do
    let p := d.parameters[index]!
    let bound ← field p "bound"
    if bound != .null && ctx.checkBounds then
      let upper ← lowerType { ctx with decl := some i, params := values, self := none, binders := [] } bound
      modify fun s => { s with obligations := s.obligations ++ [⟨values[index]!, upper, ctx.bounds,
        s!"{ctx.site}: the type argument for {d.name}'s {p.getObjValD "name" |>.compress} at {(p.getObjValD "span").compress}"⟩] }
  return values.toList

/-- A declaration at arguments: its head applied, or its alias inlined. An
alias met again before a constructor is an unguarded cycle (§8.3). -/
partial def instantiateDecl (ctx : Ctx) (i : Nat) (values : List Union) : M Union := do
  let d := (← get).doc[i]!
  if d.isHead then return [mkApp (← declHead i) values]
  if ctx.aliases.contains i then
    throw s!"{ctx.site}: unguarded alias cycle through {d.name}: a recursive alias must reach itself through an object, array, tuple or function type"
  let inner := { ctx with decl := some i, params := values.toArray, self := none }
  -- The alias's own bounds are checked where it is applied (`application`);
  -- its body's applications are its declaration's, well formed at every
  -- argument within those bounds, as TypeScript checks the declaration.
  lowerType { inner with binders := [], aliases := i :: ctx.aliases, checkBounds := false } d.expression

/-- An intersection: meet labels over the product of the operands' unions
(§3.3). On ground rows only, where TypeScript reads a record met with a
function as one callable, that row is a literal head of its own. -/
partial def intersect (ctx : Ctx) (term : Json) : M Union := do
  fieldsExactly term ["k", "parts", "span"]
  let parts := (← (← arr term "parts").mapM (lowerType ctx)).toList
  meetOf ctx.site parts (mentions [] term).isEmpty

/-- The intersection of unions (§3.3): the meet labels over their product,
unless the operands are ground (`ground`) and their rows clause rows: then,
where TypeScript reads a record met with a function as one callable, that
row is a head of its own. An intersection none of whose meets has a value is
refused where it is written (`meetChecks`). -/
partial def meetOf (site : String) (parts : List Union) (ground : Bool) : M Union := do
  if parts.any List.isEmpty then throw s!"{site}: {emptyMeet}"
  if parts.length == 1 then return parts[0]!
  if ground then
    if let some rows ← groundRows parts then
      let some last := rows.getLast? | throw "empty intersection"
      let met ← (rows.dropLast.foldrM sourceMeetLists last : Except String _)
      if met.isEmpty then throw s!"{site}: {emptyMeet}"
      let model := rows.dropLast.foldr meetLists last
      if met != model then return [← EquationLowering.ground "callable" met]
  let meets := meetUnions parts
  modify fun s => { s with meetChecks := s.meetChecks ++ [(meets, site)] }
  return meets

/-- The clauses of ground operands whose rows are clause rows, when every
operand's is. -/
partial def groundRows (parts : List Union) : M (Option (List (List (Clause (List Tree))))) := do
  let mut rows := []
  for U in parts do
    let mut cs := []
    for t in U do
      match t with
      | .app g args =>
        if !(← tryEnsure g) then return none
        match (← draft g).body with
        | some (.clauses c) => cs := cs ++ instantiateClauses c ((args.toList.map Types.toList))
        | _ => return none
      | _ => return none
    rows := rows ++ [cs]
  return some rows

/-- Lower a head's row now, if it is not being lowered. -/
partial def tryEnsure (h : Nat) : M Bool := do
  if (← draft h).body.isSome then return true
  if (← get).processing.contains h then return false
  match (← get).jobs.find? (·.head == h) with
  | some job =>
    modify fun s => { s with jobs := s.jobs.filter (·.head != h) }
    runJob job
    return true
  | none => return false

/-- A base's clauses in the deriving declaration's placeholders: each label
an application of a head with a clause row. -/
partial def heritage (ctx : Ctx) (base : Json) : M (List (Clause (List Tree))) := do
  let labels ← lowerType ctx base
  labels.flatMapM fun t => do
    match t with
    | .app g args =>
      if !(← tryEnsure g) then throw s!"{ctx.site}: cyclic heritage through {(← draft g).name}"
      match (← draft g).body with
      | some (.clauses cs) => return instantiateClauses cs (args.toList.map Types.toList)
      | _ => throw s!"{ctx.site}: a base whose row is not a clause row"
    | _ => throw s!"{ctx.site}: a base that is a type parameter or an intersection is outside heritage"

/-- An object type's clause. A
generic method is a head of its own, owned by the head whose row this is. -/
partial def objectClause (ctx : Ctx) (term : Json) : M (Clause (List Tree)) := do
  fieldsExactly term (objectMembers term)
  let hidden ← match term.getObjVal? "prototype" with
    | .ok t => do
      let P ← lowerType ctx t
      let keys ← (← arr t "fields").mapM fun f => do PropKey.decode (← field f "name")
      pure (some (P, keys.toList))
    | .error _ => pure none
  let mut methods : List (MethodMembers.Sig (List Tree)) := []
  let mut all : Array (PropKey × List Tree × Bool × Bool) := #[]
  for f in ← arr term "fields" do
    let name ← PropKey.decode (← field f "name")
    if RequestJson.reservedKey name then
      throw s!"{ctx.site}: a declared member cannot use the model's internal key {repr name}"
    let ty ← field f "type"
    let optional ← bool f "optional"
    match (if optional then none else methodForms ty) with
    | some forms =>
      let mut calls : List (MethodArrow (List Tree)) := []
      let mut rests : List (MethodRestArrow (List Tree)) := []
      -- The types the host must meet, which every form states alike: the
      -- member states them once, for all its signatures.
      let mut receivers : Option (List (List Tree)) := none
      for form in forms do
        fieldsExactly form ["k", "receiver", "params", "rest", "result", "effect", "span"]
        let stated ← ((statedReceivers form).getD #[]).mapM (lowerType ctx)
        match receivers with
        | none => receivers := some stated.toList
        | some rs => if rs != stated.toList then
            throw s!"{ctx.site}: a method's signatures state its receiver unalike"
        let domains ← (← arr form "params").mapM (lowerType ctx)
        let rest ← field form "rest"
        let result ← lowerType ctx (← field form "result")
        let effect : CallEffects.Effect ← fromJson? (← field form "effect")
        if rest == .null then calls := calls ++ [⟨(), domains.toList, result, effect⟩]
        else rests := rests ++ [⟨(), (domains.toList, ← lowerRest ctx rest), result, effect⟩]
      methods := methods ++ [⟨name, calls, rests, [], receivers.getD []⟩]
    | none =>
      match (if optional then none else schemeMethod ty) with
      | some t =>
        let some o := ctx.owner | throw s!"{ctx.site}: a generic method outside a head"
        let (names, packs) ← (schemeBinders ctx.site t : Except String _)
        let owner ← draft o
        let key := (toJson name).compress
        let m ← alloc s!"method|{o}|{key}"
          { name := s!"{owner.name}.{key}", kind := .method o key, kinds := owner.kinds,
            binders := unitBinders names packs } fun m => some (.scheme m ctx t)
        let args := (List.range owner.kinds.length).map fun k => [Tree.argument k]
        methods := methods ++ [⟨name, [], [], [[mkApp m args]], []⟩]
      | none =>
        let value ← lowerType ctx ty
        all := all.push (name, value, ← bool f "readonly", optional)
  let fs := all.filterMap fun (n, v, r, o) => if o then none else some (n, v, r)
  let optional := all.toList.filterMap fun (n, v, r, o) =>
    if o then some (⟨n, r, v⟩ : OptionalField (List Tree)) else none
  let names := fs.toList.map (·.1) ++ optional.map (·.key) ++ methods.map (·.key)
  if names.eraseDups.length != names.length then throw s!"{ctx.site}: duplicate declaration field"
  let mut indexes : List (IndexKeys × List Tree) := []
  let mut cells : List (IndexKeys × List Tree) := []
  for (_, keys, index) in indexSignatures term do
    fieldsExactly index ["readonly", "value", "span"]
    let value ← lowerType ctx (← field index "value")
    indexes := indexes ++ [(keys, value)]
    if !(← bool index "readonly") then cells := cells ++ [(keys, value)]
  let writes := fs.toList.filterMap fun (name, value, readonly) =>
    if readonly then none else some (name, value)
  let views := fs.toList.filterMap fun (name, value, readonly) =>
    if readonly then some (name, value) else none
  let mut fixed : List (Arrow (List Tree)) := []
  let mut variadic : List (RestArrow (List Tree)) := []
  for call in ← arr term "calls" do
    fieldsExactly call ["k", "receiver", "params", "rest", "result", "effect", "span"]
    if (← str call "k") != "function" then throw s!"{ctx.site}: call signature is not a function"
    let recv ← field call "receiver"
    let receiver ← if recv == .null then pure [← top] else lowerType ctx recv
    let domains ← (← arr call "params").mapM (lowerType ctx)
    let rest ← field call "rest"
    let result ← lowerType ctx (← field call "result")
    let effect : CallEffects.Effect ← fromJson? (← field call "effect")
    if rest == .null then fixed := fixed ++ [⟨receiver, domains.toList, result, effect⟩]
    else variadic := variadic ++ [⟨receiver, (domains.toList, ← lowerRest ctx rest), result, effect⟩]
  if hidden.isSome && (!fixed.isEmpty || !variadic.isEmpty || !indexes.isEmpty) then
    throw s!"{ctx.site}: a prototype of hidden members is stated of a plain record only"
  if fixed.isEmpty && variadic.isEmpty then
    if indexes.isEmpty then
      match hidden with
      | some (P, keys) =>
        return .refs writes [] (views ++ [(CallArguments.protoField, P)]) optional methods [⟨false, keys⟩]
      | none => return .refs writes [] views optional methods
    else return .dict writes [] views indexes optional methods [] cells
  else if !methods.isEmpty then throw s!"{ctx.site}: a callable object with methods needs a combined clause"
  else if !optional.isEmpty then throw s!"{ctx.site}: a callable object with an optional field needs a combined clause"
  else if !indexes.isEmpty || !views.isEmpty then
    throw s!"{ctx.site}: callable object with index or readonly field needs a combined clause"
  else if writes.isEmpty then return .arrs fixed variadic
  else return .callable writes [] fixed variadic

/-- A function type's clause. -/
partial def functionClause (ctx : Ctx) (term : Json) : M (Clause (List Tree)) := do
  fieldsExactly term ["k", "receiver", "params", "rest", "result", "effect", "span"]
  let recv ← field term "receiver"
  let receiver ← if recv == .null then pure [← top] else lowerType ctx recv
  let domains ← (← arr term "params").mapM (lowerType ctx)
  let restTerm ← field term "rest"
  let result ← lowerType ctx (← field term "result")
  let effect : CallEffects.Effect ← fromJson? (← field term "effect")
  if restTerm == .null then return .arrs [⟨receiver, domains.toList, result, effect⟩] []
  return .arrs [] [⟨receiver, (domains.toList, ← lowerRest ctx restTerm), result, effect⟩]

/-- The row a literal head's term states. -/
partial def termRow (ctx : Ctx) (term : Json) : M (GraphRow Tree (List Tree)) := do
  match ← str term "k" with
  | "object" => return .clauses [← objectClause ctx term]
  | "function" => return .clauses [← functionClause ctx term]
  | "constructor" =>
    fieldsExactly term ["k", "params", "rest", "result", "span"]
    let ps ← (← arr term "params").mapM (lowerType ctx)
    let restTerm ← field term "rest"
    let result ← lowerType ctx (← field term "result")
    if restTerm == .null then return .clauses [.ctors [(ps.toList, result)]]
    return .clauses [.ctors [] [(ps.toList, ← lowerRest ctx restTerm, result)]]
  | k => throw s!"{ctx.site}: no row for a '{k}' term"

/-- A scheme's row: its binders the head's locals, its bounds read outside
them (§3.1). -/
partial def schemeRow (ctx : Ctx) (term : Json) : M (GraphRow Tree (List Tree)) := do
  let (names, packs) ← (schemeBinders ctx.site term : Except String _)
  let bs ← arr term "binders"
  let inner : Ctx := { ctx with binders := (names.zipIdx.map fun ((n : String), (k : Nat)) =>
    (n, (⟨packs.contains n, [.local k]⟩ : Binding))) ++ ctx.binders }
  let mut bounds : List (Tree × List Tree) := []
  for (b, k) in bs.toList.zipIdx do
    let bound ← field b "bound"
    if bound == .null then continue
    let n ← str b "name"
    if packs.contains n then
      let pack ← match kindOf bound with
        | some "array" => pure [← occurrence ctx "pack" (← field bound "element")
            (job := fun h c => .pack h c [] (some (bound.getObjValD "element")))]
        | some "tuple" =>
          if !(← arr bound "optional").isEmpty || (← field bound "rest") != .null then
            throw s!"{ctx.site}: the argument-pack bound is not represented; the contract cannot be erased"
          let required := (← arr bound "required").toList
          pure [← occurrence ctx "packbound" bound (job := fun h c => .pack h c required none)]
        | _ => throw s!"{ctx.site}: the argument-pack bound is not represented; the contract cannot be erased"
      bounds := bounds ++ [(.local k, pack)]
    else bounds := bounds ++ [(.local k, ← lowerType ctx bound)]
  let inner := { inner with bounds := ctx.bounds ++ bounds }
  let mut fixed : List (Arrow (List Tree)) := []
  let mut rests : List (RestArrow (List Tree)) := []
  for f in ← arr term "signatures" do
    fieldsExactly f ["k", "receiver", "params", "rest", "result", "effect", "span"]
    let recv ← lowerType inner (← field f "receiver")
    let ps ← (← arr f "params").toList.mapM (lowerType inner)
    let restTerm ← field f "rest"
    let res ← lowerType inner (← field f "result")
    let effect : CallEffects.Effect ← fromJson? (← field f "effect")
    if restTerm == .null then fixed := fixed ++ [⟨recv, ps, res, effect⟩]
    else rests := rests ++ [⟨recv, (ps, ← lowerRest inner restTerm), res, effect⟩]
  return .scheme ((List.range names.length).map Tree.local) fixed bounds rests

/-- A declaration's row: the source meet of its own members with its bases'
rows (§8.1, heritage). -/
partial def declarationRow (h i : Nat) : M (GraphRow Tree (List Tree)) := do
  let d := (← get).doc[i]!
  let n := d.parameters.size
  let args := (List.range n).map fun k => [Tree.argument k]
  let ctx : Ctx :=
    { decl := some i, params := args.toArray, self := some [mkApp h args], owner := some h,
      site := d.name }
  let bounds ← d.parameters.toList.zipIdx.filterMapM fun (p, k) => do
    let b ← field p "bound"
    if b == .null then pure none else pure (some (Tree.argument k, ← lowerType ctx b))
  let ctx := { ctx with bounds }
  let own := d.expression
  let empty := kindOf own == some "object" &&
    ((own.getObjValAs? (Array Json) "fields").toOption.getD #[1]).isEmpty &&
    ((own.getObjValAs? (Array Json) "calls").toOption.getD #[1]).isEmpty &&
    (indexSignatures own).isEmpty && (own.getObjVal? "prototype").toOption.isNone
  let mut rows ← if empty && !d.bases.isEmpty then pure [.top]
    else if kindOf own == some "object" then pure [← objectClause ctx own]
    else heritage ctx own
  for base in d.bases do
    let inherited ← heritage ctx base
    rows ← (sourceMeetLists rows inherited : Except String _)
    if rows.isEmpty then throw s!"{d.name}: {emptyMeet}"
  return .clauses rows

/-- A unit head's row: a scheme binding its binders, stating no signature.
The head owns the unit's binders (§8.1); the unit's type is read from its
annotations and a generic value's from its lowered type
(`GenericValue`), never from this row, so it states nothing further, and a
bound naming another binder of the unit (`U extends T`) needs no scheme bound
(the unit reads it as a meet, `SourceClaimJson.binderRows`). -/
partial def unitRow (_ctx : Ctx) (node : Json) : M (GraphRow Tree (List Tree)) := do
  let tps := (node.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
  return .scheme ((List.range tps.size).map Tree.local) [] [] []

/-- Producer row `n`'s head, lifted over the binder names it mentions
freely; its row is a job. -/
partial def rowHead (n : Nat) : M Nat := do
  let P := (← get).rows
  let own := P.own[n]!
  alloc s!"row|{n}"
    { name := s!"row {n}", kind := if own.isEmpty then .literal else .scheme,
      kinds := P.free[n]!.map fun _ => .value, binders := own.map (⟨·, .value⟩) } fun h => some (.row h n)

/-- Producer row `n` as a label in `scope`: its head applied to what its free
binder names are there, a name out of scope its placeholder. The primitive
rows are the primitive heads. -/
partial def rowLabel (scope : List (String × Binding)) (n : Nat) : M Union := do
  let P := (← get).rows
  if n < 4 then return [mkApp n []]
  if n ≥ P.rows.size then throw s!"source claims: no row {n}"
  let h ← rowHead n
  let args ← P.free[n]!.mapM fun name => do
    match scope.lookup name with
    | some b => pure b.value
    | none => pure [← placeholder name .value]
  return [mkApp h args]

/-- Producer row `n`'s row: its free names its arguments, its own binders
its locals. -/
partial def rowBody (n : Nat) : M (GraphRow Tree (List Tree)) := do
  let P := (← get).rows
  let scope : List (String × Binding) :=
    (P.own[n]!.zipIdx.map fun (name, j) => (name, (⟨false, [.local j]⟩ : Binding))) ++
    (P.free[n]!.zipIdx.map fun (name, i) => (name, (⟨false, [.argument i]⟩ : Binding)))
  let row := P.rows[n]!
  let lowered ← row.operands.mapM fun A => do return (A, ← claimUnion scope (.arr A.toArray))
  let own := P.own[n]!
  let binder (b : Json) : Tree := match (b.getObjValAs? String "binder").toOption.bind own.idxOf? with
    | some j => .local j
    | none => .local 0
  return row.map binder fun A => (lowered.lookup A).getD []

/-- The canonical order of source-claims labels, on their spelling: rows by
index, then declarations, intersections, arrays and binders, each by its
fields in order, lists lexicographically. -/
partial def claimCmp (a b : Json) : Ordering :=
  let rank (j : Json) : Nat := match j with
    | .num _ => 0
    | _ => if (j.getObjVal? "decl").isOk then 1 else if (j.getObjVal? "meet").isOk then 2
      else if (j.getObjVal? "array").isOk then 3 else 4
  let lex : Ordering → Ordering → Ordering := fun | .eq, o => o | o, _ => o
  let list (f : Json → Json → Ordering) : List Json → List Json → Ordering := fun as bs =>
    let rec go : List Json → List Json → Ordering
      | [], [] => .eq
      | [], _ :: _ => .lt
      | _ :: _, [] => .gt
      | a :: as, b :: bs => lex (f a b) (go as bs)
    go as bs
  let arr (j : Json) : List Json := ((j.getArr?).toOption.getD #[]).toList
  let labels (x y : Json) : Ordering := list claimCmp (arr x) (arr y)
  let field (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD (.arr #[])
  match rank a, rank b with
  | 0, 0 => compare ((a.getNat?).toOption.getD 0) ((b.getNat?).toOption.getD 0)
  | 1, 1 => lex (compare ((field a "decl").getNat?.toOption.getD 0) ((field b "decl").getNat?.toOption.getD 0))
      (list labels (arr (field a "args")) (arr (field b "args")))
  | 2, 2 => list labels (arr (field a "meet")) (arr (field b "meet"))
  | 3, 3 => lex (labels (field a "array") (field b "array"))
      (compare ((field a "readonly").getBool?.toOption.getD false) ((field b "readonly").getBool?.toOption.getD false))
  | 4, 4 => compare ((field a "binder").getStr?.toOption.getD "") ((field b "binder").getStr?.toOption.getD "")
  | r, s => compare r s

/-- A source-claims label: a `decl` application (arity full), a `meet`, an
`array` of its store, or a `binder`: the binder `scope` gives the name, else
its name placeholder. A `types` row index is the producer's row, which the
claims map in the same scope (`rowLabel`). -/
partial def claimLabel (scope : List (String × Binding)) (j : Json) : M Union := do
  let get? (name : String) : Option Json := (j.getObjVal? name).toOption
  match j with
  | .num _ => rowLabel scope (← j.getNat?)
  | .obj _ =>
    if let some k := get? "decl" then
      fieldsExactly j (if (j.getObjVal? "args").isOk then ["decl", "args"] else ["decl"])
      let i ← k.getNat?
      let ds := (← get).doc
      if i ≥ ds.size then throw s!"source claims: a declaration's label names no declaration: {i}"
      let spelled ← match j.getObjVal? "args" with
        | .ok a => do
          let a ← a.getArr?
          if a.isEmpty then throw "source claims: a nullary declaration's label leaves its arguments out"
          pure a.toList
        | .error _ => pure []
      let args ← spelled.mapM (claimUnion scope)
      if args.length != ds[i]!.parameters.size then
        throw s!"source claims: a declaration's label has one argument per parameter: {ds[i]!.name} has {ds[i]!.parameters.size}, given {args.length}"
      let ctx : Ctx := { binders := scope, site := "source claims", checkBounds := false }
      let values ← application ctx i args
      instantiateDecl ctx i values
    else if let some ps := get? "meet" then
      fieldsExactly j ["meet"]
      let parts ← (← ps.getArr?).toList.mapM (claimUnion scope)
      if parts.length < 2 then throw "source claims: a meet has at least two parts"
      meetOf "source claims" parts (parts.all (·.all fun t => !treeOpen t && !hasRigid t))
    else if let some s := get? "array" then
      fieldsExactly j ["array", "readonly"]
      let store ← claimUnion scope s
      return [mkApp (← arrayHead (← bool j "readonly") (← protoLabel)) [store]]
    else if let some n := get? "binder" then
      fieldsExactly j ["binder"]
      let n ← n.getStr?
      if n.isEmpty then throw "source claims: a binder's label names it"
      match scope.lookup n with
      | some ⟨false, v⟩ => return v
      | some ⟨true, _⟩ => throw s!"source claims: the argument pack {n} used as a value type"
      | none => return [← placeholder n .value]
    else throw s!"source claims: not a label: {j.compress}"
  | _ => throw s!"source claims: not a label: {j.compress}"

/-- A union of source-claims labels. -/
partial def claimUnion (scope : List (String × Binding)) (j : Json) : M Union := do
  let ls := (← j.getArr?).toList
  unless (ls.zip ls.tail).all (fun (a, b) => claimCmp a b == .lt) do
    throw "source claims: a label list is in canonical order, each label once"
  return normUnion ((← ls.mapM (claimLabel scope)).flatten)
/-- Lower one pending row. -/
partial def runJob (job : Job) : M Unit := do
  let h := job.head
  if (← draft h).body.isSome then return
  modify fun s => { s with processing := h :: s.processing }
  let row ← match job with
    | .declaration h i => declarationRow h i
    | .term _ ctx term => termRow ctx term
    | .store _ ctx term =>
      let readonly ← bool term "readonly"
      let presence : ArrayPresence ← fromJson? (← field term "presence")
      if kindOf term == some "array" then
        fieldsExactly term ["k", "readonly", "presence", "element", "span"]
        let element ← lowerType ctx (← field term "element")
        pure (.clauses [.list ⟨[], [], some element, readonly, presence⟩ []])
      else
        fieldsExactly term ["k", "readonly", "presence", "required", "optional", "rest", "span"]
        let required ← (← arr term "required").toList.mapM (lowerType ctx)
        let optional ← (← arr term "optional").toList.mapM (lowerType ctx)
        let restTerm ← field term "rest"
        let rest ← if restTerm == .null then pure none else some <$> lowerType ctx restTerm
        pure (.clauses [.list ⟨required, optional, rest, readonly, presence⟩ []])
    | .pack _ ctx required rest =>
      let required ← required.mapM (lowerType ctx)
      let rest ← rest.mapM (lowerType ctx)
      pure (.clauses [.pack ⟨required, [], rest, false, .dense⟩ []])
    | .scheme _ ctx term => schemeRow ctx term
    | .unit _ ctx node => unitRow ctx node
    | .row _ n => rowBody n
  setBody h row
  modify fun s => { s with processing := s.processing.erase h }
end

/-- Lower every pending row. -/
partial def drain : M Unit := do
  match (← get).jobs with
  | [] => return
  | job :: rest =>
    modify fun s => { s with jobs := rest }
    runJob job
    drain

/-! ### Units and annotations -/

/-- The fields of the function tree that hold a source annotation. -/
def annotationFields : List String :=
  ["annot", "functionType", "bagType", "type", "result", "bound", "retType"]

/-- The terms a unit's scheme reads: its parameters' and result's types and
its binders' bounds. -/
def unitTerms (node : Json) : Json :=
  let tps := (node.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
  let params := (node.getObjValAs? (Array Json) "params").toOption.getD #[]
  .arr (tps.map (·.getObjValD "bound") ++ params.map (·.getObjValD "type") ++
    #[node.getObjValD "retType", node.getObjValD "result", node.getObjValD "type"])

/-- Enter a generic unit's binders: the unit is a head of its own, lifted over
the enclosing binders its scheme names, whose binders are `bound(f, A⃗, j)`,
met with its bound when it has one (§8.1). -/
def enterUnit (path : String) (scope : List (String × Binding)) (node : Json) (tps : Array Json) :
    M (List (String × Binding)) := do
  let names ← tps.toList.mapM fun p => (str p "name" : Except String String)
  let ctx : Ctx := { binders := scope, site := path }
  let items := (mentions names (unitTerms node)).filter fun it => match it with
    | .binder n => (scope.lookup n).isSome
    | _ => false
  let args ← items.mapM fun it => (ctxValue ctx it : Except String Union)
  let name := (node.getObjValAs? String "name").toOption.getD path
  let d : Draft :=
    { name, kind := .unit path, kinds := items.map fun _ => .value,
      binders := names.map fun n => ⟨n, .value⟩ }
  let u ← alloc s!"unit|{path}" d fun u => some (.unit u (liftedCtx ctx items u) node)
  let rigid := names.zipIdx.map fun (n, j) => (n, (⟨false, [mkBound u args j]⟩ : Binding))
  let inner := rigid ++ scope
  let bounded ← (tps.toList.zip rigid).mapM fun (p, (n, r)) => do
    let b := p.getObjValD "bound"
    if b == .null then return (n, r, none)
    return (n, r, some (← lowerType { ctx with binders := inner } b))
  let bindings := bounded.map fun (n, r, B) => match B with
    | none => (n, r)
    | some B => (n, (⟨false, meetUnions [r.value, B]⟩ : Binding))
  let owned := bounded.filterMap fun (n, r, B) => match r.value with
    | [t] => some (n, t, B)
    | _ => none
  modify fun s => { s with scopes := (path, bindings) :: s.scopes, unitBinders := (path, owned) :: s.unitBinders }
  return bindings ++ scope

/-- A node's binders as their name placeholders: what each name stands for
is decided where the unit or closure is checked (`EquationStore.rebind`). A
name used as an argument pack is a placeholder of that kind. -/
def bindNames (scope : List (String × Binding)) (bounds : List (Tree × Union)) (node : Json)
    (tps : Array Json) : M (List (String × Binding) × List (Tree × Union)) := do
  let names ← tps.toList.mapM fun p => (str p "name" : Except String String)
  let bound ← names.mapM fun n => do
    let pack := (binderUse n node).pack
    return (n, (⟨pack, [← placeholder n (if pack then .arguments else .value)]⟩ : Binding))
  let inner := bound ++ scope
  -- A value binder's declared bound, read where an application over it
  -- checks a declaration's bound (`closeObligation`).
  let mut out := bounds
  for (p, (n, b)) in tps.toList.zip bound do
    let t := p.getObjValD "bound"
    if t == .null || b.pack then continue
    let B ← lowerType { binders := inner, bounds := bounds, site := s!"the bound of {n}" } t
    if let [q] := b.value then out := (q, B) :: out
  return (inner, out)

/-- An array or tuple type's parts. -/
def arrayParts (ctx : Ctx) (term : Json) : M (Option ArrayParts) := do
  match kindOf term with
  | some "array" =>
    let element ← lowerType ctx (← field term "element")
    return some ⟨[], [], some element, ← bool term "readonly", ← field term "presence"⟩
  | some "tuple" =>
    let required ← (← arr term "required").toList.mapM (lowerType ctx)
    let optional ← (← arr term "optional").toList.mapM (lowerType ctx)
    let restTerm ← field term "rest"
    let rest ← if restTerm == .null then pure none else some <$> lowerType ctx restTerm
    return some ⟨required, optional, rest, ← bool term "readonly", ← field term "presence"⟩
  | _ => return none

/-- Every annotation of the function tree lowered in its scope, keyed by its
path. A binder is its name placeholder (`bindNames`). -/
partial def walk (path : String) (scope : List (String × Binding)) (bounds : List (Tree × Union))
    (j : Json) : M (List (String × Union)) := do
  match j with
  | .arr xs => return (← xs.toList.zipIdx.mapM fun (x, i) => walk s!"{path}/{i}" scope bounds x).flatten
  | .obj kvs =>
    let tps := (j.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
    let (scope, bounds) ← if tps.isEmpty then pure (scope, bounds) else bindNames scope bounds j tps
    let ctx : Ctx := { binders := scope, site := path, bounds }
    let mut out := []
    for (name, value) in kvs.toList do
      let here := s!"{path}/{name}"
      if annotationFields.contains name && value != .null then
        out := out ++ [(here, ← lowerType { ctx with site := here } value)]
        if let some parts ← arrayParts { ctx with site := here } value then
          modify fun s => { s with arrayAnnotations := s.arrayAnnotations ++ [(here, parts)] }
      else if name == "typeArgs" then
        let .arr values := value | throw s!"{here}: type arguments are a list"
        for (v, i) in values.toList.zipIdx do
          out := out ++ [(s!"{here}/{i}", ← lowerType { ctx with site := s!"{here}/{i}" } v)]
      else out := out ++ (← walk here scope bounds value)
    return out
  | _ => return []

/-- The top-level code's scope: every generic class's binders, one per
spelling. -/
def classScope (init : Json) : M (List (String × Binding)) := do
  let mut scope := []
  let .arr sts := init | return []
  for (st, si) in sts.toList.zipIdx do
    if kindOf st != some "const" then continue
    let .ok (.arr bs) := st.getObjVal? "bindings" | continue
    for (b, bi) in bs.toList.zipIdx do
      let init := b.getObjValD "init"
      if kindOf init != some "ctor" then continue
      let tps := (init.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
      if tps.isEmpty then continue
      let inner ← enterUnit s!"/init/{si}/bindings/{bi}/init" [] init tps
      for (n, v) in inner do
        if (scope.lookup n).isNone then scope := scope ++ [(n, v)]
  return scope

/-! ### Source-claims labels (§9.1) -/

/-! ### Finishing: hash-consing, validation, checks -/

/-- Merge literal and scheme heads with equal templates (§8.1), until no two
more are equal: each round only merges, so there are at most as many rounds
as heads. Returns each head's representative. -/
def hashCons (heads : Array Draft) : Array Nat := Id.run do
  let mergeable (d : Draft) : Bool := d.kind == .literal || d.kind == .scheme || d.kind == .primitive
  let mut rep : Array Nat := Array.range heads.size
  for _ in [0:heads.size + 1] do
    let mut seen : Std.HashMap String Nat := {}
    let mut next := rep
    for h in [0:heads.size] do
      let d := heads[h]!
      if !mergeable d then continue
      let r := rep
      let body := d.body.map (mapRow fun U => U.map (treeRename fun g => r[g]!))
      let key := s!"{reprStr d.kinds}|{reprStr d.binders}|{reprStr body}"
      match seen.get? key with
      | some g => next := next.set! h (min g next[h]!)
      | none => seen := seen.insert key h
    if next == rep then break
    rep := next
  return rep

/-- A closed tree as a label of `E`, or a located refusal. -/
def closedLabel (E : Equations) (site : String) (t : Tree) : Except String (Label E.signature) :=
  match Label.ofTree? t with
  | some l => .ok l
  | none => .error s!"{site}: {(t.problem E.signature 0 0 .label).getD "not a closed label"}"

def closedUnion (E : Equations) (site : String) (U : Union) : Except String (List (Label E.signature)) :=
  U.mapM (closedLabel E site)

/-! ### Instances by substitution (§4.3, §9.2)

What an equation label proposes for an instance of a scheme row
(`CertificateProducer.Instantiates`): the binders' instances found by
matching the scheme's signatures against the target's trees, and each
operand's image its structural substitution (`Label.substitute`), which
`substitutionTableOk` checks. Untrusted. -/

/-- Whether a tree mentions one of `bs`. -/
partial def mentionsAny (bs : List Tree) (t : Tree) : Bool :=
  bs.contains t || match t with
    | .app _ args | .bound _ args _ => args.toList.any fun ts => ts.toList.any (mentionsAny bs)
    | .meet ps => ps.toList.any (mentionsAny bs)
    | _ => false

private def sameSet (a b : List Tree) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

/-- One step of a label's unfolding, as trees: the clauses the equations
give it. -/
abbrev Unfold := Tree → Option (List (Clause (List Tree)))

/-- How many unfoldings deep two applications of different heads are
compared. -/
def unfoldDepth : Nat := 4

mutual
/-- Extend `θ` so that the union `S`, its binders `bs` read as `θ` gives
them, is `T`. -/
partial def unifyUnion (unfold : Unfold) (fuel : Nat) (bs : List Tree) (θ : List (Tree × List Tree))
    (S T : List Tree) : Option (List (Tree × List Tree)) :=
  match S with
  | [b] =>
    if bs.contains b then
      match θ.lookup b with
      | some U => if sameSet U T then some θ else none
      | none => some (θ ++ [(b, T)])
    else match T with
      | [t] => unifyTree unfold fuel bs θ b t
      | _ => none
  | _ =>
    -- The union's labels mentioning no binder are themselves; the one that
    -- does takes the rest of `T`.
    let fixed := S.filter fun t => !mentionsAny bs t
    if !fixed.all (T.contains ·) then none else
    match S.filter (mentionsAny bs ·) with
    | [] => if sameSet S T then some θ else none
    | [x] =>
      match θ.lookup x with
      -- A binder already found: with the fixed labels, its instance is `T`.
      | some U => if bs.contains x && sameSet (fixed ++ U) T then some θ else
          unifyUnion unfold fuel bs θ [x] (T.filter (!fixed.contains ·))
      | none => unifyUnion unfold fuel bs θ [x] (T.filter (!fixed.contains ·))
    | xs => do
      -- A binder beside labels mentioning it (`R | PromiseLike<R>` against
      -- `string | PromiseLike<string>`): each such label is one of `T`'s,
      -- which may find the binder; a binder then found is its instance, and
      -- one still unfound takes the rest of `T`. Several unfound binders
      -- (`T1 | T2` against `string`) are left to the other operands.
      let (θ, img) ← (xs.filter (!bs.contains ·)).foldlM (fun (acc : List (Tree × List Tree) × List Tree) x =>
        T.findSome? fun t => (unifyTree unfold fuel bs acc.1 x t).map fun θ => (θ, acc.2 ++ [t]))
        (θ, fixed)
      let bare := xs.filter (bs.contains ·)
      let img := img ++ (bare.filterMap fun b => θ.lookup b).flatten
      if !img.all (T.contains ·) then none
      match bare.filter (fun b => (θ.lookup b).isNone) with
      | [] => if T.all (img.contains ·) then some θ else none
      | [b] => some (θ ++ [(b, T.filter (!img.contains ·))])
      | _ => some θ
/-- Extend `θ` so that the tree `s` is `t`. Two applications of different
heads are compared by one step of their unfoldings (a literal the target
spells as a row of its own), at most `fuel` steps deep. -/
partial def unifyTree (unfold : Unfold) (fuel : Nat) (bs : List Tree) (θ : List (Tree × List Tree))
    (s t : Tree) : Option (List (Tree × List Tree)) :=
  if !mentionsAny bs s then (if s == t then some θ else none) else
  match s, t with
  | .app h a, .app h' a' =>
    if h == h' && a.toList.length == a'.toList.length then
      (a.toList.zip a'.toList).foldlM (fun θ (x, y) => unifyUnion unfold fuel bs θ x.toList y.toList) θ
    else match fuel, unfold s, unfold t with
      | fuel + 1, some cs, some ds =>
        if cs.length == ds.length && (cs.zip ds).all (fun (c, d) => c.map (fun _ => ()) == d.map (fun _ => ())) then
          (cs.zip ds).foldlM (fun θ (c, d) =>
            (c.operands.zip d.operands).foldlM (fun θ (x, y) => unifyUnion unfold fuel bs θ x y) θ) θ
        else none
      | _, _, _ => none
  | .bound h a _, .bound h' a' _ =>
    if h != h' || a.toList.length != a'.toList.length then none
    else (a.toList.zip a'.toList).foldlM (fun θ (x, y) => unifyUnion unfold fuel bs θ x.toList y.toList) θ
  | .meet ps, .meet qs =>
    if ps.toList.length != qs.toList.length then none
    else (ps.toList.zip qs.toList).foldlM (fun θ (x, y) => unifyTree unfold fuel bs θ x y) θ
  | _, _ => none
end

/-- The binders' instances making a scheme's signatures cover the target
arrows, each target matched against one of the scheme's; unmatched binders
stand for themselves. -/
def unifyScheme (unfold : Unfold) (s : SchemeRow Tree) (L : PositiveRules.Ops Tree) (M : List (RestArrow (List Tree))) :
    Option (List (Tree × List Tree)) := do
  let unifyArrow (θ : List (Tree × List Tree)) (p q : List (List Tree)) : Option (List (Tree × List Tree)) :=
    if p.length != q.length then none
    else (p.zip q).foldlM (fun θ (x, y) => unifyUnion unfold unfoldDepth s.binders θ x y) θ
  -- A receiver a scheme states as every value admits any: it is not matched.
  -- The arguments come first, as TypeScript infers from them: the result
  -- (`Promise<T | TResult>` at `Promise<number>`) then checks their choice.
  let body (a : Arrow (List Tree)) := a.arguments ++ [a.result]
  let θ ← L.foldlM (fun θ q => s.signatures.findSome? fun p =>
    if p.effect != q.effect then none else unifyArrow θ (body p) (body q)) []
  M.foldlM (fun θ q => s.variadic.findSome? fun p =>
    if p.effect != q.effect then none
    else unifyArrow θ (p.arguments.2 :: p.result :: p.arguments.1) (q.arguments.2 :: q.result :: q.arguments.1)) θ

/-- An equation graph's proposal: instances by matching, images by
structural substitution. -/
def proposeLabels {sig : Signature} (unfold : Unfold) (s : SchemeRow (Label sig)) (L : PositiveRules.Ops (Label sig))
    (M : List (RestArrow (List (Label sig)))) : Option (List (List (Label sig)) × InstTable (Label sig)) := do
  let tree (U : List (Label sig)) : List Tree := U.map (·.1)
  let s' : SchemeRow Tree := ⟨tree s.binders, s.signatures.map (Arrow.map tree),
    s.bounds.map (fun (b, U) => (b.1, tree U)), s.variadic.map (RestArrow.map tree)⟩
  let θ ← unifyScheme unfold s' (L.map (Arrow.map tree)) (M.map (RestArrow.map tree))
  let θs ← s.binders.mapM fun b => ((θ.lookup b.1).getD [b.1]).mapM Label.ofTree?
  let κ : PositiveRules.Ctx (Label sig) := s.binders.zip θs
  let operands := (s.signatures.flatMap Arrow.operands ++ s.variadic.flatMap RestArrow.operands).flatten.eraseDups
  return (θs, operands.map fun l => (l, κ, l.substitute (parameterReplacement κ)))

instance {sig : Signature} : CertificateProducer.Instantiates (Label sig) := ⟨proposeLabels fun _ => none⟩

/-- The heads' raw rows. -/
def rawHeads (drafts : Array Draft) (bodies : Array (GraphRow Tree (List Tree))) : List RawHead :=
  (List.range drafts.size).map fun h =>
    let d := drafts[h]!
    { name := d.name
      header := { parameters := d.kinds.length, binders := d.binders, kinds := d.kinds }
      body := bodies[h]! }

def realmOf (E : Equations) (proto : Option Nat) (excluded : List PropKey) :
    Option (ArrayRealm (Label E.signature)) :=
  proto.bind fun p => (Label.ofTree? (mkApp p [])).map fun l => ⟨[l], excluded⟩

/-- A bound obligation's closed form: inside a template, the head's
parameters are read as bounded parameter labels, each a family variable met
with its declared bound (§8.2). -/
def closeObligation (o : Obligation) : Union × Union :=
  let var (p : Tree) : Tree := match p with
    | .argument i => .var 1000000 i .value
    | .local j => .var 2000000 j .value
    | t => t
  let plain (p : Tree) : Union := [var p]
  let σ (p : Tree) : Union := match o.bounds.find? (·.1 == p) with
    | some (_, b) => meetUnions [[var p], b.flatMap (treeSubst (plain ∘ .argument) (plain ∘ .local))]
    | none => plain p
  -- A name placeholder in scope is its binder met with its declared bound.
  let named (t : Tree) : Option Union :=
    if isPlaceholder t then (o.bounds.find? (·.1 == t)).map fun (_, b) => meetUnions [[t], b] else none
  let close (U : Union) :=
    (U.flatMap (treeSubst (σ ∘ .argument) (σ ∘ .local))).flatMap (treeReplace named)
  (close o.actual, close o.upper)

/-! ### Producer rows (§9.1)

A source-claims document's `types` rows are the producer's: clause rows, and
the scheme rows of classes' generic methods, whose binders are binder labels.
Each row is a head, lifted over the binder names it mentions freely (through
the rows it names too), as a literal is lifted over its binders (§8.1): a
row naming a binder of a unit is applied to that name's placeholder, and a
scheme row's own binders are its locals. -/

/-! ### The source-claims document's label lists -/

section
variable {m : Type → Type} [Monad m]

private def update (j : Json) (k : String) (f : Json → m Json) : m Json := do
  match j.getObjVal? k with
  | .ok v => return j.setObjVal! k (← f v)
  | .error _ => return j

private def each (f : Json → m Json) : Json → m Json
  | .arr xs => return .arr (← xs.mapM f)
  | j => return j

private def nullable (f : Json → m Json) : Json → m Json
  | .null => return .null
  | j => f j

/-- A claim type with each label list rewritten by `f`: labels, or a form
over claim types. With `pointForm`, `unitForm` and `documentForm`, the
claims document's label lists, in every unit: a claim's labels, what a point
asserts of each field, a call's type arguments. The traversal is the
document's shape (SOURCE-CLAIMS). -/
partial def claimForm (f : Json → m Json) (j : Json) : m Json := do
  match j with
  | .arr _ => f j
  | _ =>
    let j ← update j "union" (each (claimForm f))
    let j ← update j "array" (claimForm f)
    update j "scheme" fun s => do
      let s ← update s "typeParams" (each fun p => update p "bound" (nullable (claimForm f)))
      let s ← update s "this" (claimForm f)
      let s ← update s "params" (each (claimForm f))
      let s ← update s "rest" (nullable (claimForm f))
      update s "result" (claimForm f)

def pointForm (f : Json → m Json) (j : Json) : m Json := do
  let j ← update j "type" (claimForm f)
  let j ← update j "current" (nullable (each fun
    | .arr #[k, A] => do return .arr #[k, ← f A]
    | x => pure x))
  update j "instantiate" (nullable (each fun i => update i "type" (claimForm f)))

def unitForm (f : Json → m Json) (j : Json) : m Json := do
  let entries := each fun e => update e "bindings" (each (pointForm f))
  let j ← update j "params" (each (pointForm f))
  let j ← update j "result" (claimForm f)
  let j ← update j "entries" entries
  let j ← update j "expressions" (each (pointForm f))
  update j "arrows" (each fun a => update a "rows" (each fun r => do
    let r ← update r "expressions" (each (pointForm f))
    update r "entries" entries))

def documentForm (f : Json → m Json) (claims : Json) : m Json := do
  let claims ← update claims "functions" (each (unitForm f))
  update claims "init" (unitForm f)

end

/-- A union as its spelling (§9.2). -/
def unionJson (U : Union) : Json := .arr (U.map Tree.toJson).toArray

/-! ### Lowering a source for the source path -/

/-- A generic module value's type, its binders their name placeholders: a
function's signature (receiver, parameters, rest element and result), a
construct signature (parameters and result), or any other type. -/
inductive GenericType where
  | function (receiver : Option Union) (params : List Union) (rest : Option Union) (result : Union)
  | construct (params : List Union) (result : Union)
  | other (type : Union)

def GenericType.map (f : Union → Union) : GenericType → GenericType
  | .function r ps e res => .function (r.map f) (ps.map f) (e.map f) (f res)
  | .construct ps res => .construct (ps.map f) (f res)
  | .other t => .other (f t)

/-- A generic module value: a generic module function, a generic class or a
generic imported value. Its type and its binders' bounds have the binders
as their name placeholders; an instance substitutes them
(`EquationStore.rebind`). -/
structure GenericValue where
  name : String
  pos : Nat × Nat
  binders : List String
  type : Except String GenericType
  bounds : List (String × Option Union)

/-- A source lowered for the source path. -/
structure SourceLowering where
  /-- The store the units grow: the heads, hash-consed and compacted. -/
  store : State
  /-- Each annotation, by its path in the function tree. -/
  annotations : List (String × Union)
  /-- Each array or tuple annotation's parts, by its path. -/
  arrays : List (String × ArrayParts)
  /-- Each imported value's type, by its local name, with its span. -/
  values : List (String × (Nat × Nat) × Union)
  generics : List GenericValue
  /-- Each generic unit's binders, by its path: an owned parameter of the
  unit's head, with its declared bound over those parameters (`enterUnit`). -/
  units : List (String × List (String × Tree × Option Union))
  /-- The module initialization's binders: every generic class's, one per
  name, the first class's. -/
  initBinders : List (String × Tree × Option Union)
  /-- The claims document, its label lists spelled as trees (§9.2). -/
  claims : Json

/-- A generic value's type term: a function or construct signature by its
parts, so that several instances conjoin as one callable; any other type
whole. A rest is the pack of its element (`lowerRest`). -/
def genericType (ctx : Ctx) (term : Json) : M GenericType := do
  match (term.getObjValAs? String "k").toOption with
  | some "function" =>
    fieldsExactly term ["k", "receiver", "params", "rest", "result", "effect", "span"]
    if (← str term "effect") != "unrestricted" then return .other (← lowerType ctx term)
    let recv ← field term "receiver"
    let receiver ← if recv == .null then pure none else some <$> lowerType ctx recv
    let params ← (← arr term "params").toList.mapM (lowerType ctx)
    let restTerm ← field term "rest"
    -- A rest is its element's claim; a pack binder has no claim form.
    if kindOf restTerm == some "pack" then return .other (← lowerType ctx term)
    let rest ← if restTerm == .null then pure none else some <$> lowerType ctx restTerm
    return .function receiver params rest (← lowerType ctx (← field term "result"))
  | some "constructor" =>
    fieldsExactly term ["k", "params", "rest", "result", "span"]
    if (← field term "rest") != .null then return .other (← lowerType ctx term)
    let params ← (← arr term "params").toList.mapM (lowerType ctx)
    return .construct params (← lowerType ctx (← field term "result"))
  | _ => return .other (← lowerType ctx term)

/-- Lower a generic module value's pieces with its binders as placeholders.
Its declared bounds are checked at each instance a call names
(`Scheme.moduleInstances`), not here. -/
private def genericOf (name : String) (pos : Nat × Nat) (path : String) (node : Json) (tps : Array Json)
    (type : List (String × Binding) → M GenericType) : M GenericValue := do
  let (scope, _) ← bindNames [] [] node tps
  let binders ← tps.toList.mapM fun p => (str p "name" : Except String String)
  let t ← tryCatch (do return Except.ok (← type scope)) fun e => pure (.error e)
  let bounds ← tps.toList.mapM fun p => do
    let n ← (str p "name" : Except String String)
    let b := p.getObjValD "bound"
    if b == .null then return (n, none)
    return (n, some (← lowerType { binders := scope, site := s!"{path}: the bound of {n}", checkBounds := false } b))
  return { name, pos, binders, type := t, bounds }

/-- Everything the source path lowers, in one run: the declarations, every
annotation, the imported values, the generic units' binders, the producer's
rows and the claims. -/
def lowerSource (ast claims : Json) : M (List (String × Union) × List (String × (Nat × Nat) × Union) ×
    List GenericValue × List (String × List (String × Tree × Option Union)) ×
    List (String × Tree × Option Union) × Json) := do
  primitives
  let ds := (← get).doc
  let excluded ← match ds[0]? with
    | some d =>
      if d.identity == arrayProtoIdentity then
        let names ← (← arr d.expression "fields").mapM fun f => do PropKey.decode (← field f "name")
        pure (RequestJson.arrayExcludedKeys names.toList)
      else pure (RequestJson.arrayExcludedKeys [])
    | none => pure (RequestJson.arrayExcludedKeys [])
  modify fun s => { s with excluded }
  -- Every declaration: heads now, aliases where they are used.
  for i in [:ds.size] do
    if ds[i]!.isHead then let _ ← declHead i
  -- The realm's array prototype.
  let proto ← protoLabel
  modify fun s => { s with proto := match proto with | .app h _ => some h | _ => none }
  drain
  let functionTrees := (ast.getObjValAs? (Array Json) "functions").toOption.getD #[]
  let annotations ← walk "/functions" [] [] (ast.getObjValD "functions")
  -- Generic module functions: their binders, and their types at them.
  let mut generics : List GenericValue := []
  let mut units : List (String × List (String × Tree × Option Union)) := []
  for (f, i) in functionTrees.toList.zipIdx do
    let tps := (f.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
    if tps.isEmpty then continue
    let path := s!"/functions/{i}"
    let _ ← enterUnit path [] f tps
    units := units ++ [(path, (((← get).unitBinders.lookup path).getD []))]
    let name ← str f "name"
    let pos ← (fromJson? (← field f "namePos") : Except String (Nat × Nat))
    generics := generics ++ [← genericOf name pos path f tps fun scope => do
      -- Its signature by its parameters' annotations: a rest's element, the
      -- claim of a rest being its element's (`Fragment.callableType`).
      let ctx : Ctx := { binders := scope, site := path, checkBounds := false }
      let mut params := []
      let mut rest := none
      for p in ← arr f "params" do
        let ty ← field p "type"
        if ty == .null then
          throw s!"{path}: a generic module function's type needs every parameter's annotation"
        if (p.getObjVal? "rest").isOk then
          if kindOf ty != some "array" || (← bool ty "readonly") then
            throw s!"{path}: a generic module function's rest parameter needs a mutable array contract"
          rest := some (← lowerType ctx (← field ty "element"))
        else params := params ++ [← lowerType ctx ty]
      let result ← field f "retType"
      if result == .null then throw s!"{path}: a generic module function's type needs its result's annotation"
      return .function none params rest (← lowerType ctx result)]
  let init := ast.getObjValD "init"
  let classes ← classScope init
  let initBinders := ((← get).unitBinders.reverse.filter (·.1.startsWith "/init/")).flatMap (·.2)
    |>.foldl (fun (acc : List (String × Tree × Option Union)) (n, t, B) =>
      if (acc.lookup n).isSome then acc else acc ++ [(n, t, B)]) []
  -- The top-level code reads every generic class's binders by name, each
  -- with its declared bound, as a class's own code does.
  let ctors : List Json := match init with
    | .arr sts => sts.toList.flatMap fun st => match st.getObjVal? "bindings" with
      | .ok (.arr bs) => bs.toList.filterMap fun b =>
        let c := b.getObjValD "init"
        if (c.getObjValAs? String "k").toOption == some "ctor" &&
            ((c.getObjValAs? (Array Json) "typeParams").toOption.getD #[]).size > 0 then some c else none
      | _ => []
    | _ => []
  let (initScope, initBounds) ← ctors.foldlM (fun (acc : List (String × Binding) × List (Tree × Union)) c => do
    let tps := (c.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
    let (scope, bounds) ← bindNames [] [] c tps
    let fresh := scope.filter fun (n, _) => (acc.1.lookup n).isNone
    return (acc.1 ++ fresh, acc.2 ++ bounds.filter fun (q, _) => !acc.2.any (·.1 == q))) ([], [])
  let initAnnotations ← walk "/init" initScope initBounds init
  -- Generic classes: their construct signatures at their binders.
  let .arr sts := init | throw "the module initialization is a list"
  for (st, si) in sts.toList.zipIdx do
    if (st.getObjValAs? String "k").toOption != some "const" then continue
    let .ok (.arr bs) := st.getObjVal? "bindings" | continue
    for (b, bi) in bs.toList.zipIdx do
      let ctor := b.getObjValD "init"
      if (ctor.getObjValAs? String "k").toOption != some "ctor" then continue
      let tps := (ctor.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
      if tps.isEmpty then continue
      let path := s!"/init/{si}/bindings/{bi}"
      let name ← str b "name"
      let pos ← (fromJson? (← field b "namePos") : Except String (Nat × Nat))
      generics := generics ++ [← genericOf name pos path ctor tps fun scope => do
        genericType { binders := scope, site := s!"{path}/annot", checkBounds := false } (← field b "annot")]
  -- Imported values: a generic one is instantiated at each call.
  let mut values := []
  let document := ast.getObjValD "declarations"
  for (v, vi) in ((document.getObjValAs? (Array Json) "values").toOption.getD #[]).toList.zipIdx do
    fieldsExactly v ["binding", "declaration", "construct", "typeParams", "type"]
    let binding ← field v "binding"
    fieldsExactly binding ["local", "imported", "specifier", "span"]
    let name ← str binding "local"
    let span ← (fromJson? (← field binding "span") : Except String (Nat × Nat))
    let _ ← bool v "construct"
    let path := s!"/declarations/values/{vi}"
    let tps ← arr v "typeParams"
    if tps.isEmpty then
      values := values ++ [(name, span, ← lowerType { site := path } (← field v "type"))]
    else
      let _ ← enterUnit path [] v tps
      units := units ++ [(path, (((← get).unitBinders.lookup path).getD []))]
      generics := generics ++ [← genericOf name span path v tps fun scope => do
        genericType { binders := scope, site := path, checkBounds := false } (← field v "type")]
  -- The producer's rows and the claims.
  let types ← arr claims "types"
  let P ← (producerRows types : Except String ProducerRows)
  modify fun s => { s with rows := P }
  -- Rows 0 to 3 are the primitive values: null, true, false, undefined.
  let primitives : List (GraphRow Nat) := [.clauses [.nul], .clauses [.boolLit true],
    .clauses [.boolLit false], .clauses [.undef]]
  if types.toList.take 4 != primitives.map toJson then
    throw "invalid source claims: the type table must start with the primitives"
  let claims ← documentForm (fun A => do return unionJson (← claimUnion [] A)) claims
  drain
  return (annotations ++ initAnnotations, values, generics, units, initBinders, claims)

/-- The lowered heads, hash-consed and compacted, before validation. -/
structure Built where
  state : State
  /-- Old head index to new. -/
  rename : Nat → Nat
  drafts : Array Draft
  bodies : Array (GraphRow Tree (List Tree))

def Built.rn (b : Built) (U : Union) : Union := normUnion (U.map (treeRename b.rename))

/-- Merge equal templates and compact (§8.1): the kept heads in order, so
the four primitives stay first. -/
def compact (s : State) : Except String Built := do
  let rep := hashCons s.heads
  let kept := (List.range s.heads.size).filter fun h => rep[h]! == h
  let index : Std.HashMap Nat Nat := kept.zipIdx.foldl (fun m (h, i) => m.insert h i) {}
  let f (h : Nat) : Nat := (index.get? rep[h]!).getD 0
  let rn (U : Union) : Union := normUnion (U.map (treeRename f))
  let drafts := (kept.map fun h => s.heads[h]!).toArray
  let bodies ← drafts.mapM fun d => match d.body with
    | some b => pure (mapRow rn b)
    | none => throw s!"{d.name}: its row was never lowered"
  return { state := s, rename := f, drafts, bodies }

/-- Validated equations, with the realm. -/
def Built.equations (b : Built) : Except String Equations := do
  let E ← Equations.ofRaw (rawHeads b.drafts b.bodies)
  let proto := b.state.proto.map b.rename
  return { E with realm := if b.state.arrays then realmOf E proto b.state.excluded else none }

/-- The checks lowering owes the source (§5): every closed meet with a value;
every declared bound where an application is written. Variances are not
lowering's: the checker computes them (RECURSIVE-EQUATIONS §4.3). -/
def Built.finish (b : Built) : Except String Equations := do
  let (s, f, rn, drafts, bodies) := (b.state, b.rename, b.rn, b.drafts, b.bodies)
  let E ← b.equations
  -- Closed meets: an empty one is refused where it is lowered.
  let base (t : Tree) : Option (List (Clause (List Tree))) := match t with
    | .app g args => match bodies[g]? with
      | some (.clauses cs) => some (instantiateClauses cs (args.toList.map Types.toList))
      | _ => none
    | _ => none
  -- An intersection distributes over its operands' unions: it is empty when
  -- each of its meets is, a meet of clause rows whose meet has no value.
  let empty (t : Tree) : Bool := match treeRename f t with
    | .meet ps => match ps.toList.mapM base with
      | some lists => ((meetAll lists).filter Clause.isValue).isEmpty
      | none => false
    | _ => false
  for (U, site) in s.meetChecks do
    if !U.isEmpty && !U.any treeOpen && U.all empty then throw s!"{site}: {emptyMeet}"
  -- Declared bounds, where written.
  for o in s.obligations do
    let o : Obligation := { o with actual := rn o.actual, upper := rn o.upper, bounds := o.bounds.map fun (p, U) => (p, rn U) }
    let (A, B) := closeObligation o
    let A ← closedUnion E o.site A
    let B ← closedUnion E o.site B
    if (CertificateProducer.comparisonUsing E.graph { E.instanceImageCheck with budget := s.subtypeBudget } A B).accepted then
      continue
    let names (h : Nat) : String := (drafts[h]?.map (·.name)).getD s!"{h}"
    throw s!"{o.site} does not establish its declared bound: {showUnion names (A.map (·.1))} ≤ {showUnion names (B.map (·.1))}"
  return E

/-- The store the units grow, from the compacted heads: their rows, their
keys (a key that spells a head index spelled again with the new one), the
generic units' binders, the placeholders and the realm. -/
def Built.store (b : Built) : State :=
  let (s, f) := (b.state, b.rename)
  let drafts := (b.drafts.zip b.bodies).map fun (d, body) => { d with body := some body }
  -- Keys that spell a head index or a tree are made again from the new rows.
  let spelled (k : String) : Bool :=
    k.startsWith "ground|" || k.startsWith "method|" || k.startsWith "lifted|" || k.startsWith "schemeOver|"
  let kept := s.keys.fold (fun (m : Std.HashMap String Nat) k h =>
    if spelled k then m else m.insert k (f h)) {}
  let keys := (List.range drafts.size).foldl (fun (m : Std.HashMap String Nat) h =>
    let d := drafts[h]!
    match d.kind, d.body with
    | .method o key, _ => m.insert s!"method|{f o}|{key}" h
    -- Every nullary head is found by its clauses, a declaration's among
    -- them, as a finite table finds a row by its clauses.
    | _, some (.clauses cs) =>
      if d.kinds.isEmpty && !m.contains s!"ground|{reprStr cs}" then m.insert s!"ground|{reprStr cs}" h
      else m
    | _, _ => m) kept
  let rnB (b : Binding) : Binding := { b with value := b.value.map (treeRename f) }
  let owned (d : Draft) : Draft := match d.kind with
    | .method o key => { d with kind := .method (f o) key }
    | _ => d
  { s with heads := drafts.map owned, keys := keys, jobs := [], processing := [], obligations := [],
           meetChecks := [], unitBinders := [],
           scopes := s.scopes.map (fun (p, bs) => (p, bs.map fun (n, x) => (n, rnB x))),
           proto := s.proto.map f }

/-- **The source path's lowering.** `ast` is the parser's function tree with
its declaration document (`tools/declaration-types.mts`), `claims` the
source-claims document (§9.1). -/
def source (ast claims : Json) (budget : PositiveCertificates.SearchBudget := {}) : Except String SourceLowering := do
  let document ← field ast "declarations"
  let ds ← definitions document
  if let some i := (List.range ds.size).find? (fun i => ds[i]!.identity == arrayProtoIdentity) then
    if i != 0 || !ds[i]!.parameters.isEmpty then throw "ArrayProto must be the first declaration"
  let ((annotations, values, generics, units, initBinders, claims), s) ←
    (lowerSource ast claims).run { doc := ds, subtypeBudget := budget }
  let b ← compact s
  let _ ← b.finish
  let rn := b.rn
  let rename (j : Json) : Except String Json := do
    let ts ← (← j.getArr?).toList.mapM Tree.fromJson
    return unionJson (rn ts)
  return {
    store := b.store
    annotations := annotations.map fun (p, U) => (p, rn U)
    arrays := s.arrayAnnotations.map fun (p, a) => (p, a.map rn)
    values := values.map fun (n, sp, U) => (n, sp, rn U)
    generics := generics.map fun g =>
      { g with type := g.type.map (·.map rn), bounds := g.bounds.map fun (n, B) => (n, B.map rn) }
    units := units.map fun (p, bs) => (p, bs.map fun (n, t, B) => (n, treeRename b.rename t, B.map rn))
    initBinders := initBinders.map fun (n, t, B) => (n, treeRename b.rename t, B.map rn)
    claims := ← documentForm rename claims }

/-! ### Equation labels

Equation labels are closed trees (`Tree`), store-independent: the four
primitive values are the nullary heads 0 to 3, which `primitives` allocates
first and compaction keeps first. -/

instance : LabelStore.Labels Tree where
  -- An extracted label's store still grows: instances are proposed over the
  -- frozen equations (`EquationStore.Checked`).
  propose _ _ _ := none
  toJson := Tree.toJson
  fromJson? j := Tree.fromJson j
  decEq := inferInstance
  nul := mkApp 0 []
  tru := mkApp 1 []
  fls := mkApp 2 []
  undef := mkApp 3 []

end Verification.Model.EquationLowering
