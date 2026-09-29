import Std.Data.HashMap
import Verification.Model.Types.EquationFamilies
import Verification.Model.Types.EquationValidator
import Verification.Model.Types.EquationJson
import Verification.Model.Programs.CertificateProducer
import Verification.Model.Programs.CellClaims
import Verification.Model.Source.LabelStore

/-! Lowering source declarations to recursive equations (RECURSIVE-EQUATIONS
§8). The parser's declaration document, the function tree's annotations and
the source-claims labels become one table of equations, validated by
`Equations.ofRaw`, and unions of closed labels over it. Heads are made per
source declaration, per unit and per type-literal occurrence, never per
instance, so a growing family (`Pair<[T, U]>`, `Promise`'s `catch`) is
finitely many heads. There is no budget, colour, depth limit or truncation:
an alias cycle not guarded by a constructor is refused, and everything else
terminates because heads are keyed by source occurrence.

Lowering is untrusted in what it proposes (the variance declarations, the
hash-consing of literal heads) and trusted in what it states: the equations
are the meaning of the source, as the finite table is today. It is not yet
read by any request (`SourceClaimJson` still takes `DeclarationGraph`'s
table); S6 wires it in. -/
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

/- Renaming heads, meets re-canonicalized: their order depends on head
indices. -/
mutual
partial def treeRename (f : Nat → Nat) : Tree → Tree
  | .app h args => .app (f h) (argsRename f args)
  | .bound h args j => .bound (f h) (argsRename f args) j
  | .meet ps => canonMeet (ps.toList.map (treeRename f))
  | t => t
partial def argsRename (f : Nat → Nat) (args : Args) : Args :=
  Args.ofList (args.toList.map fun ts => Types.ofList (ts.toList.map (treeRename f)))
end

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

/-! ### Variance proposal (§7.5)

A least fixpoint over the head graph on `none < co, contra < inv`. A
writable position is `inv`, a readonly one or a result `co`, a parameter or
receiver `contra`; a nested application composes with its head's current
variance, and a scheme bound is `inv`. Untrusted: the declarations must pass
`Equations.checkVariance`. -/

/-- The variance at a position of polarity `p` of a head of variance `q`. -/
def compose : Variance → Variance → Variance
  | _, .none => .none
  | .none, _ => .none
  | .co, q => q
  | .contra, .co => .contra
  | .contra, .contra => .co
  | .contra, .inv => .inv
  | .inv, _ => .inv

def join : Variance → Variance → Variance
  | .none, v => v
  | v, .none => v
  | .co, .co => .co
  | .contra, .contra => .contra
  | _, _ => .inv

private def arrowPolar (a : Arrow α) : List (Variance × α) :=
  (.contra, a.receiver) :: a.arguments.map (.contra, ·) ++ [(.co, a.result)]

private def restPolar (a : RestArrow α) : List (Variance × α) :=
  (.contra, a.receiver) :: a.arguments.1.map (.contra, ·) ++
    [(.contra, a.arguments.2), (.co, a.result)]

private def sigPolar (s : MethodMembers.Sig α) : List (Variance × α) :=
  s.calls.flatMap (fun m => m.arguments.map (.contra, ·) ++ [(.co, m.result)]) ++
    s.rests.flatMap (fun m => m.arguments.1.map (.contra, ·) ++
      [(.contra, m.arguments.2), (.co, m.result)]) ++
    s.schemes.map (.co, ·)

/-- Each operand of a clause with the polarity of its position. -/
def clausePolar : Clause α → List (Variance × α)
  | .list a bs => (a :: bs).flatMap fun t => t.operands.map ((if t.readonly then .co else .inv), ·)
  | .pack a bs => (a :: bs).flatMap fun t => t.operands.map (.co, ·)
  | .refs a bs vs os ms _ =>
    (a ++ bs.flatten).map (fun f => (.inv, f.2)) ++ vs.map (fun f => (.co, f.2)) ++
      os.map (fun o => ((if o.readonly then .co else .inv), o.type)) ++ ms.flatMap sigPolar
  | .dict a bs vs ds os ms _ cs =>
    (a ++ bs.flatten).map (fun f => (.inv, f.2)) ++ vs.map (fun f => (.co, f.2)) ++
      ds.map (fun f => (.co, f.2)) ++
      os.map (fun o => ((if o.readonly then .co else .inv), o.type)) ++ ms.flatMap sigPolar ++
      cs.map (fun f => (.inv, f.2))
  | .arrs L S => L.flatMap arrowPolar ++ S.flatMap restPolar
  | .callable a bs L S =>
    (a ++ bs.flatten).map (fun f => (.inv, f.2)) ++ L.flatMap arrowPolar ++ S.flatMap restPolar
  | .ctors L S => L.flatMap (fun q => q.1.map (.contra, ·) ++ [(.co, q.2)]) ++
      S.flatMap fun q => q.1.map (.contra, ·) ++ [(.contra, q.2.1), (.co, q.2.2)]
  | _ => []

def rowPolar : GraphRow Tree (List Tree) → List (Variance × List Tree)
  | .clauses cs => cs.flatMap clausePolar
  | .scheme _ sigs bounds rests =>
    sigs.flatMap arrowPolar ++ bounds.map (fun b => (.inv, b.2)) ++ rests.flatMap restPolar
  | _ => []

/-- The parameters a tree reads at polarity `p`, under the current
variances `v`. -/
partial def treePolar (v : Array (Array Variance)) (p : Variance) : Tree → List (Nat × Variance)
  | .argument i => [(i, p)]
  | .app g args =>
    (args.toList.zipIdx).flatMap fun (ts, k) =>
      let q := compose p ((v[g]?.bind (·[k]?)).getD .inv)
      if q == .none then [] else ts.toList.flatMap (treePolar v q)
  | .meet ps => ps.toList.flatMap (treePolar v p)
  | _ => []

/-- One round: every head's variance from its template and the others'. -/
def varianceRound (bodies : Array (GraphRow Tree (List Tree))) (arity : Array Nat)
    (v : Array (Array Variance)) : Array (Array Variance) :=
  (bodies.zip arity).map fun (body, n) =>
    let reads := (rowPolar body).flatMap fun (p, U) => U.flatMap (treePolar v p)
    (Array.range n).map fun i => reads.foldl (fun acc (j, q) => if j == i then join acc q else acc) .none

/-- The least fixpoint. Each round that changes something raises at least
one of the finitely many entries one step in a lattice of height two, so
`2 × entries + 1` rounds reach it; the result is checked stable. -/
def proposeVariance (bodies : Array (GraphRow Tree (List Tree))) (arity : Array Nat) :
    Except String (Array (Array Variance)) := do
  let entries := arity.foldl (· + ·) 0
  let mut v : Array (Array Variance) := arity.map fun n => Array.replicate n .none
  for _ in [0:2 * entries + 1] do
    let next := varianceRound bodies arity v
    if next == v then return v
    v := next
  if varianceRound bodies arity v != v then throw "variance proposal: no fixpoint"
  return v

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
    CellClaims.fieldsExactly j ["declaration", "parameters", "bases", "expression"]
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
  deriving Inhabited

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

/-- A field's method forms: one signature or an intersection of several, each
with the declaration as receiver. -/
private def methodForms (t : Json) : Option (Array Json) :=
  let forms := if kindOf t == some "intersection"
    then (t.getObjValAs? (Array Json) "parts").toOption.getD #[] else #[t]
  if !forms.isEmpty && forms.all (fun f => kindOf f == some "function" &&
      ((f.getObjVal? "receiver").toOption.bind kindOf) == some "self")
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

/-- A row still to lower. -/
inductive Job where
  | declaration (head index : Nat)
  | term (head : Nat) (ctx : Ctx) (term : Json)
  | store (head : Nat) (ctx : Ctx) (term : Json)
  | pack (head : Nat) (ctx : Ctx) (required : List Json) (rest : Option Json)
  | scheme (head : Nat) (ctx : Ctx) (term : Json)
  | unit (head : Nat) (ctx : Ctx) (node : Json)
  deriving Inhabited

def Job.head : Job → Nat
  | .declaration h _ | .term h .. | .store h .. | .pack h .. | .scheme h .. | .unit h .. => h

/-- A declared bound to check where an application is written (§8.2): the
actual union within the declared one. Inside a template, `owner` is the head
whose placeholders they hold. -/
structure Obligation where
  actual : Union
  upper : Union
  /-- The bounds of the placeholders `actual` and `upper` may hold. -/
  bounds : List (Tree × Union)
  site : String

structure State where
  doc : Array Definition
  heads : Array Draft := #[]
  keys : Std.HashMap String Nat := {}
  jobs : List Job := []
  processing : List Nat := []
  excluded : List PropKey := []
  arrays : Bool := false
  obligations : List Obligation := []
  meetChecks : List (Tree × String) := []
  /-- Each generic unit's binders, by the unit's path. -/
  scopes : List (String × List (String × Binding)) := []

abbrev M := StateT State (Except String)

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

/-- The empty intersection's refusal (as `DeclarationGraph`). -/
def emptyMeet : String :=
  "the intersection is empty: its operands have no value in common (no value has two shapes, and an array owns no key its prototype provides), and an empty intersection is refused rather than verified vacuously"

/-- Two operands' clauses as TypeScript meets them: the model's meet, except
that a record of invariant fields met with a function type is the function
carrying those fields, a `callable` (`DeclarationGraph.sourceMeetLists`, over
any operands). -/
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
    bounds := ctx.bounds.filterMap fun (p, U) => do
      let (_, j) ← indexed.find? fun (it, _) => (ctxValue ctx it).toOption == some [p]
      let moved (q : Tree) : Option Union :=
        (indexed.find? fun (it, _) => (ctxValue ctx it).toOption == some [q]).map fun (_, k) => [.argument k]
      let U' ← U.mapM fun t => if treeOpen t then
          (match t with | .argument _ | .local _ => moved t | _ => none) else some [t]
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

/-! ### Lowering source types -/

private def unitBinders (names : List String) (packs : List String) : List Binder :=
  names.map fun n => ⟨n, if packs.contains n then .arguments else .value⟩

/-- A scheme's binders, their kinds, and the refusals of forms a scheme
cannot state. -/
def schemeBinders (site : String) (term : Json) : Except String (List String × List String) := do
  CellClaims.fieldsExactly term ["k", "binders", "signatures", "span"]
  let bs ← arr term "binders"
  let sigTerms ← arr term "signatures"
  let refuse (reason : String) : Except String Unit :=
    throw s!"{site}: generic contract at {(term.getObjValD "span").compress}: {reason}; the contract cannot be erased"
  let names ← bs.toList.mapM fun b => do
    CellClaims.fieldsExactly b ["name", "bound", "default", "span"]
    str b "name"
  let own (j : Json) : Bool := names.any fun n => let u := binderUse n j; u.value || u.pack
  if bs.any (fun b => own (b.getObjValD "bound")) then refuse "dependent method bounds are not represented"
  let uses : List (String × BinderUse) := names.map fun n => (n, binderUse n (.arr sigTerms))
  if uses.any (fun (p : String × BinderUse) => p.2.pack && p.2.value) then
    refuse "a binder used as both a value and an argument pack is not represented"
  return (names, (uses.filter fun (p : String × BinderUse) => p.2.pack).map Prod.fst)

def referenceIndex (term : Json) : M Nat := do
  CellClaims.fieldsExactly term ["k", "reference", "args", "span"]
  let target ← field (← field term "reference") "target"
  let ds := (← get).doc
  match (List.range ds.size).filter fun i => ds[i]!.identity == target with
  | [i] => return i
  | [] => throw "reference has no declaration equation"
  | _ => throw "duplicate declaration identity"

/-- A literal type's labels. A numeric zero is both zeros, as TypeScript's
literal type `0` is. -/
def literalLabels (term : Json) : M Union := do
  CellClaims.fieldsExactly term ["k", "name", "text", "span"]
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
    CellClaims.fieldsExactly term ["k", "index", "span"]
    ctxValue ctx (.param (← (← field term "index").getNat?))
  | "self" =>
    CellClaims.fieldsExactly term ["k", "span"]
    ctxValue ctx .self
  | "binder" =>
    CellClaims.fieldsExactly term ["k", "name", "span"]
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
    CellClaims.fieldsExactly term ["k", "span"]
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
    CellClaims.fieldsExactly term ["k", "of", "span"]
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
    CellClaims.fieldsExactly p ["name", "span", "bound", "default"]
    let default ← field p "default"
    if default == .null then throw s!"{ctx.site}: {d.name} applied without its required argument {← str p "name"}"
    values := values.push (← lowerType { ctx with decl := some i, params := values, self := none, binders := [] } default)
  for index in [:d.parameters.size] do
    let p := d.parameters[index]!
    let bound ← field p "bound"
    if bound != .null then
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
  lowerType { inner with binders := [], aliases := i :: ctx.aliases } d.expression

/-- An intersection: meet labels over the product of the operands' unions
(§3.3). On ground rows only, where TypeScript reads a record met with a
function as one callable, that row is a literal head of its own. -/
partial def intersect (ctx : Ctx) (term : Json) : M Union := do
  CellClaims.fieldsExactly term ["k", "parts", "span"]
  let parts := (← (← arr term "parts").mapM (lowerType ctx)).toList
  if parts.any List.isEmpty then throw s!"{ctx.site}: {emptyMeet}"
  if parts.length == 1 then return parts[0]!
  if (mentions [] term).isEmpty then
    if let some rows ← groundRows parts then
      let some last := rows.getLast? | throw "empty intersection"
      let met ← (rows.dropLast.foldrM sourceMeetLists last : Except String _)
      if met.isEmpty then throw s!"{ctx.site}: {emptyMeet}"
      let model := rows.dropLast.foldr meetLists last
      if met != model then
        let d : Draft := { name := literalName term, kind := .literal, kinds := [] }
        let h ← alloc s!"callable|{term.compress}" { d with body := some (.clauses met) } fun _ => none
        return [mkApp h []]
  let meets := meetUnions parts
  modify fun s => { s with meetChecks := s.meetChecks ++ (meets.flatMap treeMeets).map (·, ctx.site) }
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

/-- An object type's clause (`DeclarationGraph`'s object arm, over trees). A
generic method is a head of its own, owned by the head whose row this is. -/
partial def objectClause (ctx : Ctx) (term : Json) : M (Clause (List Tree)) := do
  CellClaims.fieldsExactly term (objectMembers term)
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
      for form in forms do
        CellClaims.fieldsExactly form ["k", "receiver", "params", "rest", "result", "effect", "span"]
        let domains ← (← arr form "params").mapM (lowerType ctx)
        let rest ← field form "rest"
        let result ← lowerType ctx (← field form "result")
        let effect : CallEffects.Effect ← fromJson? (← field form "effect")
        if rest == .null then calls := calls ++ [⟨(), domains.toList, result, effect⟩]
        else rests := rests ++ [⟨(), (domains.toList, ← lowerRest ctx rest), result, effect⟩]
      methods := methods ++ [⟨name, calls, rests, []⟩]
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
        methods := methods ++ [⟨name, [], [], [[mkApp m args]]⟩]
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
    CellClaims.fieldsExactly index ["readonly", "value", "span"]
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
    CellClaims.fieldsExactly call ["k", "receiver", "params", "rest", "result", "effect", "span"]
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
  CellClaims.fieldsExactly term ["k", "receiver", "params", "rest", "result", "effect", "span"]
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
    CellClaims.fieldsExactly term ["k", "params", "rest", "result", "span"]
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
    CellClaims.fieldsExactly f ["k", "receiver", "params", "rest", "result", "effect", "span"]
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

/-- A unit head's row: a scheme over its binders, with the unit's call
signature when it is a fully annotated function (§8.1). -/
partial def unitRow (ctx : Ctx) (node : Json) : M (GraphRow Tree (List Tree)) := do
  let tps := (node.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
  let names := tps.toList.filterMap fun p => (p.getObjValAs? String "name").toOption
  let inner : Ctx := { ctx with binders := (names.zipIdx.map fun ((n : String), (k : Nat)) =>
    (n, (⟨false, [.local k]⟩ : Binding))) ++ ctx.binders }
  let mut bounds : List (Tree × List Tree) := []
  for (p, k) in tps.toList.zipIdx do
    let b := p.getObjValD "bound"
    if b == .null then continue
    if (mentions [] b).any (fun it => match it with | .binder n => names.contains n | _ => false) then
      throw s!"{ctx.site}: the bound of {names.getD k "?"} names a binder of the same unit, which a scheme's bounds cannot state"
    bounds := bounds ++ [(.local k, ← lowerType ctx b)]
  let inner := { inner with bounds := ctx.bounds ++ bounds }
  let signature ← unitSignature inner node
  let (fixed, rests) := match signature with
    | some (.inl a) => ([a], [])
    | some (.inr r) => ([], [r])
    | none => ([], [])
  return .scheme ((List.range names.length).map Tree.local) fixed bounds rests

/-- A unit's call signature, when it is a fully annotated function. -/
partial def unitSignature (ctx : Ctx) (node : Json) :
    M (Option (Arrow (List Tree) ⊕ RestArrow (List Tree))) := do
  if let some ty := (node.getObjVal? "type").toOption then
    if kindOf ty != some "function" then return none
    match ← functionClause ctx ty with
    | .arrs [a] [] => return some (.inl a)
    | .arrs [] [r] => return some (.inr r)
    | _ => return none
  let some params := (node.getObjValAs? (Array Json) "params").toOption | return none
  let result := (node.getObjVal? "retType").toOption <|> (node.getObjVal? "result").toOption
  let some result := result | return none
  if result == .null then return none
  let mut fixed : List (List Tree) := []
  let mut rest : Option (List Tree) := none
  for p in params do
    let ty := p.getObjValD "type"
    if ty == .null then return none
    if (p.getObjVal? "rest").isOk then
      if kindOf ty != some "array" || (← bool ty "readonly") then
        throw s!"{ctx.site}: a generic unit's rest parameter needs a mutable array contract"
      rest := some (← lowerRest ctx (← field ty "element"))
    else fixed := fixed ++ [← lowerType ctx ty]
  let res ← lowerType ctx result
  let receiver := [← top]
  match rest with
  | none => return some (.inl ⟨receiver, fixed, res, .unrestricted⟩)
  | some P => return some (.inr ⟨receiver, (fixed, P), res, .unrestricted⟩)

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
        CellClaims.fieldsExactly term ["k", "readonly", "presence", "element", "span"]
        let element ← lowerType ctx (← field term "element")
        pure (.clauses [.list ⟨[], [], some element, readonly, presence⟩ []])
      else
        CellClaims.fieldsExactly term ["k", "readonly", "presence", "required", "optional", "rest", "span"]
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

/-- The fields of the function tree that hold a source annotation
(`DeclarationGraph.annotationFields`). -/
def annotationFields : List String :=
  ["annot", "functionType", "bagType", "type", "result", "bound", "retType"]

/-- A class generic method's binder, as the parser spells it:
`"key"#k:null^0` (§8.1). The member key's JSON spelling and the position. -/
def methodBinder? (name : String) : Option (String × Nat) :=
  match name.splitOn "#" with
  | [key, rest] =>
    match rest.splitOn ":" with
    | [k, "null^0"] => k.toNat?.map (key, ·)
    | _ => none
  | _ => none

/-- The terms a unit's scheme reads: its parameters' and result's types and
its binders' bounds. -/
def unitTerms (node : Json) : Json :=
  let tps := (node.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
  let params := (node.getObjValAs? (Array Json) "params").toOption.getD #[]
  .arr (tps.map (·.getObjValD "bound") ++ params.map (·.getObjValD "type") ++
    #[node.getObjValD "retType", node.getObjValD "result", node.getObjValD "type"])

/-- Enter a node's binders. A class's generic method closure binds the owned
binders of its class's method head; any other generic unit is a head of its
own, lifted over the enclosing binders its scheme names, whose binders are
`bound(f, A⃗, j)`, met with its bound when it has one (§8.1). -/
def enterUnit (path : String) (scope : List (String × Binding)) (node : Json) (tps : Array Json) :
    M (List (String × Binding)) := do
  let names ← tps.toList.mapM fun p => (str p "name" : Except String String)
  let ctx : Ctx := { binders := scope, site := path }
  let spelled := names.map methodBinder?
  if spelled.all Option.isSome && !names.isEmpty then
    let recv ← field (← field node "receiver") "type"
    match ← lowerType ctx recv with
    | [.app d args] =>
      let _ ← tryEnsure d
      let bindings ← (spelled.filterMap id).zip names |>.mapM fun ((key, k), n) => do
        match (← get).keys.get? s!"method|{d}|{key}" with
        | some m =>
          let dr ← draft m
          if k ≥ dr.binders.length then throw s!"{path}: {n} names no binder of the generic method {dr.name}"
          return (n, (⟨false, [mkBound m (args.toList.map Types.toList) k]⟩ : Binding))
        | none => throw s!"{path}: {n} names no generic method of its class"
      return bindings ++ scope
    | _ => throw s!"{path}: a class generic method's receiver is not its class's instance type"
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
  let bindings ← (tps.toList.zip rigid).mapM fun (p, (n, r)) => do
    let b := p.getObjValD "bound"
    if b == .null then return (n, r)
    let B ← lowerType { ctx with binders := inner } b
    return (n, (⟨false, meetUnions [r.value, B]⟩ : Binding))
  modify fun s => { s with scopes := (path, bindings) :: s.scopes }
  return bindings ++ scope

/-- Every annotation of the function tree lowered in its scope, keyed by its
path. -/
partial def walk (path : String) (scope : List (String × Binding)) (j : Json) :
    M (List (String × Union)) := do
  match j with
  | .arr xs => return (← xs.toList.zipIdx.mapM fun (x, i) => walk s!"{path}/{i}" scope x).flatten
  | .obj kvs =>
    let tps := (j.getObjValAs? (Array Json) "typeParams").toOption.getD #[]
    let scope ← if tps.isEmpty then pure scope else enterUnit path scope j tps
    let ctx : Ctx := { binders := scope, site := path }
    let mut out := []
    for (name, value) in kvs.toList do
      let here := s!"{path}/{name}"
      if annotationFields.contains name && value != .null then
        out := out ++ [(here, ← lowerType { ctx with site := here } value)]
      else if name == "typeArgs" then
        let .arr values := value | throw s!"{here}: type arguments are a list"
        for (v, i) in values.toList.zipIdx do
          out := out ++ [(s!"{here}/{i}", ← lowerType { ctx with site := s!"{here}/{i}" } v)]
      else out := out ++ (← walk here scope value)
    return out
  | _ => return []

/-- The top-level code's scope: every generic class's binders, one per
spelling (`DeclarationGraph.prepare`'s `classScope`). -/
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

mutual
/-- A source-claims label: a `decl` application (arity full), a `meet`, an
`array` of its store, or a `binder` in `scope`. A `types` row index is the
producer's row, which the caller maps (`rows`). -/
partial def claimLabel (scope : List (String × Binding)) (rows : Nat → M Union) (j : Json) : M Union := do
  let get? (name : String) : Option Json := (j.getObjVal? name).toOption
  match j with
  | .num _ => rows (← j.getNat?)
  | .obj _ =>
    if let some k := get? "decl" then
      CellClaims.fieldsExactly j (if (j.getObjVal? "args").isOk then ["decl", "args"] else ["decl"])
      let i ← k.getNat?
      let ds := (← get).doc
      if i ≥ ds.size then throw s!"source claims: declaration {i} is not in the document"
      let args ← ((j.getObjValAs? (Array Json) "args").toOption.getD #[]).toList.mapM (claimUnion scope rows)
      if args.length != ds[i]!.parameters.size then
        throw s!"source claims: {ds[i]!.name} applied to {args.length} arguments, not its {ds[i]!.parameters.size}"
      let ctx : Ctx := { binders := scope, site := "source claims" }
      let values ← application ctx i args
      instantiateDecl ctx i values
    else if let some ps := get? "meet" then
      CellClaims.fieldsExactly j ["meet"]
      let parts ← (← ps.getArr?).toList.mapM (claimUnion scope rows)
      if parts.length < 2 then throw "source claims: a meet has at least two parts"
      if parts.any List.isEmpty then throw s!"source claims: {emptyMeet}"
      let meets := meetUnions parts
      modify fun s => { s with meetChecks := s.meetChecks ++ (meets.flatMap treeMeets).map (·, "source claims") }
      return meets
    else if let some s := get? "array" then
      CellClaims.fieldsExactly j ["array", "readonly"]
      let store ← claimUnion scope rows s
      return [mkApp (← arrayHead (← bool j "readonly") (← protoLabel)) [store]]
    else if let some n := get? "binder" then
      CellClaims.fieldsExactly j ["binder"]
      let n ← n.getStr?
      match scope.lookup n with
      | some ⟨false, v⟩ => return v
      | _ => throw s!"source claims: the binder {n} is not in scope"
    else throw s!"source claims: not a label: {j.compress}"
  | _ => throw s!"source claims: not a label: {j.compress}"

/-- A union of source-claims labels. -/
partial def claimUnion (scope : List (String × Binding)) (rows : Nat → M Union) (j : Json) : M Union := do
  return normUnion ((← (← j.getArr?).toList.mapM (claimLabel scope rows)).flatten)
end

/-! ### Finishing: hash-consing, validation, variance, checks -/

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

/-- Arrow evidence proposed for a family's pairs: every source signature for
every target signature, the target's renamed to the source's binders. The
checker accepts only the evidence it checks (`EquationFamilyTests`). -/
def arrowCandidates (E : Equations) (pairs : List (List (Label E.signature) × List (Label E.signature))) :
    Evidence (Label E.signature) :=
  pairs.flatMap fun (A, B) =>
    ((sourceClauses E.graph A).flatMap fun a => (clausesOf E.graph B).flatMap fun b =>
      match a, b with
      | .arrs L _, .arrs M _ => M.flatMap fun q => L.map fun p => (L, (q, ArrowCert.source p))
      | _, _ => []) ++
    (A.flatMap fun i => B.flatMap fun j => match E.graph.schemes i, E.graph.schemes j with
      | some s, some s' =>
        let σ := s'.binders.zip (s.binders.map fun p => [p])
        (s'.signatures.map (Arrow.map (E.renaming.substitute σ)) ++ s'.signatures).flatMap fun q =>
          s.signatures.map fun p => (s.signatures, (q, ArrowCert.source p))
      | _, _ => [])

/-- The pairs a head's declaration entry reads that no hypothesis, subset or
`Var` instance discharges by itself (§7.2, case 2 is not recursive): each
argument of a nested application at a position it varies in, and each meet
over the parameters, on the entry's two sides and oriented by the position's
polarity (both ways where invariant). The entry's variables stand for the
parameters, and the head's own binders are the source side's on both, as
quantified-α renames them. -/
partial def entryPairs (v : Array (Array Variance)) (h : Nat) (kinds : List ParameterKind)
    (body : GraphRow Tree (List Tree)) : List (Union × Union) :=
  let xs := kinds.zipIdx.map fun (k, i) => [Tree.var h (2 * i) k]
  let ys := kinds.zipIdx.map fun (k, i) => [Tree.var h (2 * i + 1) k]
  let loc (j : Nat) : Union := [mkBound h xs j]
  let sx (U : Union) : Union := normUnion (U.flatMap (treeSubst (fun i => xs.getD i []) loc))
  let sy (U : Union) : Union := normUnion (U.flatMap (treeSubst (fun i => ys.getD i []) loc))
  let oriented (p : Variance) (U : Union) : List (Union × Union) :=
    let a := sx U
    let b := sy U
    if a == b then [] else match p with
      | .co => [(a, b)]
      | .contra => [(b, a)]
      | .inv => [(a, b), (b, a)]
      | .none => []
  let rec walk (p : Variance) : Tree → List (Union × Union)
    | .app g args => (args.toList.zipIdx).flatMap fun (ts, k) =>
        let q := compose p ((v[g]?.bind (·[k]?)).getD .inv)
        if q == .none then [] else oriented q ts.toList ++ ts.toList.flatMap (walk q)
    | t@(.meet ps) => oriented p [t] ++ ps.toList.flatMap (walk p)
    | _ => []
  ((rowPolar body).flatMap fun (p, U) => U.flatMap (walk p)).eraseDups

/-- The variance evidence proposed for the declarations: each head's table
(`entryPairs`), and arrow candidates for every entry's pairs. -/
def varianceEvidence (E : Equations) (bodies : Array (GraphRow Tree (List Tree)))
    (v : Array (Array Variance)) : VarianceEvidence E.signature :=
  let label (U : Union) : Option (List (Label E.signature)) := U.mapM Label.ofTree?
  let tables := (List.range bodies.size).filterMap fun h =>
    let kinds := (E.signature[h]?.map fun hd => hd.variance.map (·.1)).getD []
    let pairs := (entryPairs v h kinds bodies[h]!).filterMap fun (A, B) =>
      match label A, label B with
      | some a, some b => some (a, b)
      | _, _ => none
    if pairs.isEmpty then none else some (h, pairs)
  let entries := varianceEntries (sig := E.signature) { tables }
  { tables, arrows := arrowCandidates E (entries.flatMap (·.pairs)) }

/-- The lowered equations with what the source names over them. -/
structure Lowered where
  equations : Equations
  /-- The proposed variance declarations, checked (§7.5); or the heads whose
  declaration is refused even as invariant. The check belongs to the
  request (`checkRequests`), which refuses at those heads. -/
  variances : Except (List String) (Variances equations)
  names : Array String
  kinds : Array HeadKind
  /-- Each declaration's head, for the declarations that are heads. -/
  declarations : List (Nat × Nat)
  /-- Each generic unit's head, by its path in the function tree. -/
  units : List (String × Nat)
  /-- Each annotation, by its path in the function tree. -/
  annotations : List (String × List (Label equations.signature))
  /-- Each imported value's type, by its local name. -/
  values : List (String × List (Label equations.signature))
  /-- The requested source-claims labels, in order. -/
  claims : List (List (Label equations.signature))

/-- The heads' raw rows at variances `v`. -/
def rawHeads (drafts : Array Draft) (bodies : Array (GraphRow Tree (List Tree)))
    (v : Array (Array Variance)) : List RawHead :=
  (List.range drafts.size).map fun h =>
    let d := drafts[h]!
    { name := d.name
      header :=
        { parameters := d.kinds.length, binders := d.binders,
          variance := d.kinds.zip (v[h]!.toList) }
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
  let close (U : Union) := U.flatMap (treeSubst (σ ∘ .argument) (σ ∘ .local))
  (close o.actual, close o.upper)

/-- Lower a function tree's declarations, units and annotations, and the
given source-claims labels, to equations. -/
def lowerAll (ast : Json) (claims : List Json) : M (List (String × Union) × List (String × Union) ×
    List Union) := do
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
  drain
  let functions ← walk "/functions" [] (ast.getObjValD "functions")
  let init := ast.getObjValD "init"
  let scope ← classScope init
  let initAnnotations ← walk "/init" scope init
  let mut values := []
  let document := ast.getObjValD "declarations"
  for (v, vi) in ((document.getObjValAs? (Array Json) "values").toOption.getD #[]).toList.zipIdx do
    CellClaims.fieldsExactly v ["binding", "declaration", "construct", "typeParams", "type"]
    let name ← str (← field v "binding") "local"
    let path := s!"/declarations/values/{vi}"
    let tps ← arr v "typeParams"
    let scope ← if tps.isEmpty then pure [] else enterUnit path [] v tps
    values := values ++ [(name, ← lowerType { binders := scope, site := path } (← field v "type"))]
  let claimLabels ← claims.mapM (claimUnion [] fun n => throw s!"source claims: row {n} is a producer row, which the caller maps")
  drain
  return (functions ++ initAnnotations, values, claimLabels)

/-- The lowered heads, hash-consed and compacted, before validation. -/
structure Built where
  state : State
  /-- Old head index to new. -/
  rename : Nat → Nat
  drafts : Array Draft
  bodies : Array (GraphRow Tree (List Tree))
  annotations : List (String × Union)
  values : List (String × Union)
  claims : List Union

def Built.rn (b : Built) (U : Union) : Union := normUnion (U.map (treeRename b.rename))

def build (ast : Json) (claims : List Json := []) : Except String Built := do
  let document ← field ast "declarations"
  let ds ← definitions document
  if let some i := (List.range ds.size).find? (fun i => ds[i]!.identity == arrayProtoIdentity) then
    if i != 0 || !ds[i]!.parameters.isEmpty then throw "ArrayProto must be the first declaration"
  let ((annotations, values, claimLabels), s) ← (lowerAll ast claims).run { doc := ds }
  -- Hash-consing, then compaction: the kept heads in order, so the four
  -- primitives stay first.
  let rep := hashCons s.heads
  let kept := (List.range s.heads.size).filter fun h => rep[h]! == h
  let index : Std.HashMap Nat Nat := kept.zipIdx.foldl (fun m (h, i) => m.insert h i) {}
  let f (h : Nat) : Nat := (index.get? rep[h]!).getD 0
  let rn (U : Union) : Union := normUnion (U.map (treeRename f))
  let drafts := (kept.map fun h => s.heads[h]!).toArray
  let bodies ← drafts.mapM fun d => match d.body with
    | some b => pure (mapRow rn b)
    | none => throw s!"{d.name}: its row was never lowered"
  return { state := s, rename := f, drafts, bodies, annotations, values, claims := claimLabels }

/-- Validated equations at variances `v`, with the realm. -/
def Built.equations (b : Built) (v : Array (Array Variance)) : Except String Equations := do
  let E ← Equations.ofRaw (rawHeads b.drafts b.bodies v)
  let proto := (List.range b.drafts.size).find? fun h => b.drafts[h]!.kind == .proto
  return { E with realm := if b.state.arrays then realmOf E proto b.state.excluded else none }

/-- **The lowering.** `ast` is the parser's function tree with its
declaration document (`tools/declaration-types.mts`); `claims` are
source-claims label unions (§9.1). -/
def lower (ast : Json) (claims : List Json := []) : Except String Lowered := do
  let b ← build ast claims
  let (s, f, rn, drafts, bodies) := (b.state, b.rename, b.rn, b.drafts, b.bodies)
  let (annotations, values, claimLabels) := (b.annotations, b.values, b.claims)
  let ds := s.doc
  let arity := drafts.map (·.kinds.length)
  -- The variance proposal, weakened to invariance at a refused head, until
  -- the declarations check or a refused head is invariant already.
  let mut v ← proposeVariance bodies arity
  for _ in [0:drafts.size + 1] do
    let E ← b.equations v
    if (Variances.check? E (varianceEvidence E bodies v)).isSome then break
    let refused := E.varianceRefused (varianceEvidence E bodies v)
    let mut changed := false
    for h in refused do
      let weakened := v[h]!.map fun x => if x == .none then .none else .inv
      if weakened != v[h]! then changed := true
      v := v.set! h weakened
    if !changed then break
  let E ← b.equations v
  let checked : Except (List String) (Variances E) :=
    match Variances.check? E (varianceEvidence E bodies v) with
    | some checked => .ok checked
    | none => .error ((E.varianceRefused (varianceEvidence E bodies v)).map (drafts[·]!.name))
  -- Closed meets: an empty one is refused where it is lowered.
  let base (t : Tree) : Option (List (Clause (List Tree))) := match t with
    | .app g args => match bodies[g]? with
      | some (.clauses cs) => some (instantiateClauses cs (args.toList.map Types.toList))
      | _ => none
    | _ => none
  for (m, site) in s.meetChecks do
    match treeRename f m with
    | .meet ps =>
      if let some lists := ps.toList.mapM base then
        if ((meetAll lists).filter Clause.isValue).isEmpty then throw s!"{site}: {emptyMeet}"
    | _ => pure ()
  -- Declared bounds, where written.
  for o in s.obligations do
    let o : Obligation := { o with actual := rn o.actual, upper := rn o.upper, bounds := o.bounds.map fun (p, U) => (p, rn U) }
    let (A, B) := closeObligation o
    let A ← closedUnion E o.site A
    let B ← closedUnion E o.site B
    let pool := CertificateProducer.reachablePool E.graph A B
    match CertificateProducer.subtypeUsing E.graph E.instanceImageCheck pool A B with
    | some proof => if E.checkSubtype A B proof then continue
    | none => pure ()
    let names (h : Nat) : String := (drafts[h]?.map (·.name)).getD s!"{h}"
    throw s!"{o.site} does not establish its declared bound: {showUnion names (A.map (·.1))} ≤ {showUnion names (B.map (·.1))}"
  let label (site : String) (U : Union) := closedUnion E site (rn U)
  let declarations := (List.range ds.size).filterMap fun i =>
    (s.keys.get? s!"decl|{i}").map fun h => (i, f h)
  let units := s.keys.toList.filterMap fun (k, h) =>
    if k.startsWith "unit|" then some ((k.drop 5).toString, f h) else none
  let annotations ← annotations.mapM fun (p, U) => do return (p, ← label p U)
  let values ← values.mapM fun (n, U) => do return (n, ← label n U)
  let claims ← claimLabels.mapM (label "source claims")
  return { equations := E, variances := checked, names := drafts.map (·.name),
           kinds := drafts.map (·.kind), declarations, units, annotations, values, claims }

/-! ### The label store over equation labels

`LabelStore` (S4) asks for labels apart from any store and a store that only
grows. Equation labels are closed trees (`Tree`), store-independent: the four
primitive values are the nullary heads 0 to 3, which `primitives` allocates
first and compaction keeps first. `Labels` and `Meets` are below.

**What S6's `Store` instance must provide.** Its state is this module's
`State` (the heads under construction), and its operations are functions
here: `intern` and `lookup` a nullary `ground` head (hash-consed by its
clauses); `binder` and `binders` a unit head's owned binders (`enterUnit`);
`bounded` the meet label of a binder and its bound (`meetUnions`); `scheme` a
scheme head; `arrayProto` the `ArrayProto` head (`protoLabel`). `graph` and
`row` need the validated equations: `Equations.ofRaw` of the state's heads,
their rows read by `Equations.row` and carried from `Label E.signature` to
`Tree` (an empty clause row off the signature). A head added after the
declarations is nullary, so it changes no older head's row and carries no
variance obligation; that is the signature-extension lemma §7.5 names. It
must also give the state a JSON spelling (`ToJson σ`, `FromJson σ`). -/

/-- The meet of unions is the exact meet labels over their product (§3.3);
an empty part is the empty intersection, refused. -/
instance : LabelStore.Meets State Tree where
  meet parts := do
    if parts.any List.isEmpty then throw emptyMeet
    return meetUnions parts

instance : LabelStore.Labels Tree where
  toJson := Tree.toJson
  fromJson? j := Tree.fromJson j
  decEq := inferInstance
  nul := mkApp 0 []
  tru := mkApp 1 []
  fls := mkApp 2 []
  undef := mkApp 3 []

end Verification.Model.EquationLowering
