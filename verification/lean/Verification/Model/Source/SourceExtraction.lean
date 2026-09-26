import Verification.Model.Source.SkjsSourceClaims
import Verification.Model.Programs.ExpressionClaims
import Verification.Model.Source.GenericSource
import Verification.Model.Source.GenericAlias

/-! First source adapter for the stateful consumer. Names are resolved against
initialized local bindings. Supplied expression types and source annotations
become distinct obligations. The consumer reconstructs the request from source
and claims; evidence never supplies the program it is checked against.

The currently supported fragment is deliberately small: primitive/callable parameters,
initialized consts, branches, variables, null/boolean literals and local plain
cells (allocation, reads and assignments), expression-bodied closures and calls,
with every path returning. Boolean variable tests, including negations, refine the tested binding.
Active-name shadowing is refused here: the parser gives a shadowing local a
name of its own (PROGRAM-TYPING.md, "Shadowing"). This compiler remains a reviewed
extraction boundary, not a proved TypeScript semantics. Its output is checked by the proved calculus consumer. -/
namespace Verification.Model.SourceExtraction
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment

private def distinct [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

/-- The type of the `i`-th actual past a variadic signature's fixed ones: its
position in the rest's one tuple contract. -/
private def restPosition (G : PositiveGraphs.NormalGraph Nat) (P : List Nat) (i : Nat) :
    Option (List Nat) :=
  match PositiveRules.expand G P with
  | [.pack T []] => ProgramTyping.positionTy T i
  | _ => none

/-- What a scope slot holds. A value slot holds the value itself. A cell slot
holds the identity of a private cell this lowering allocated: `contract` is the
stable storage type every assignment is checked against, and `reference` is the
slot's own type, interned once when the binding was declared so that building
an environment stays a pure projection.

Storage comes from source declarations and assignments. A producer's
claim about `x` describes what the cell currently holds, which is exactly what
must not become the type of the slot holding its identity. -/
private inductive Storage where
  | value
  | cell (contract : Ty Nat) (reference : Ty Nat)
  deriving Repr, Inhabited

/-- A scope slot: how the source names it, and what it holds. `Descriptor` is
explanatory source-map data that cannot affect acceptance, so the storage that
decides lowering lives here and is projected away before anything is emitted. -/
private structure ScopeBinding where
  source : Descriptor
  storage : Storage := .value
  /-- A module function's slot: its type is its own source signature, never a
  producer claim, and it is a value slot, so no assignment can reach it. -/
  fixed : Option (Ty Nat) := none
  /-- A `let`'s cell: the types of the slots below it when it was allocated,
  whose records' fields its fresh location differs from. -/
  apart : Option (List (Ty Nat)) := none
  /-- A constant bound to an object or array it allocated: its fields are
  fresh, so they differ from every older cell's location. -/
  fresh : Bool := false
  /-- A parameter: bound before the body runs, so before any cell the body
  allocates, and at the same time as an assigned parameter's cell. -/
  param : Bool := false
  deriving Repr

private def held (d : Descriptor) : ScopeBinding := { source := d }

/-- Explanatory projection: what a reader is shown, with the storage dropped. -/
private def sources (scope : List ScopeBinding) : List Descriptor := scope.map (·.source)

/-- Name lookup is unchanged: descriptors carry the same names in the same
order, and an unnamed one can never match a source identifier. -/
private def names (scope : List ScopeBinding) : List String := scope.map (·.source.name)

/-- The one place a source name becomes a slot, so no site can decide for
itself whether a name denotes a value or a location. -/
private def resolve (scope : List ScopeBinding) (name : String) : Option (Nat × Storage) := do
  let i ← (names scope).idxOf? name
  let b ← scope[i]?
  return (i, b.storage)

/-- Only immutable value slots may be substituted by a guard's saved value. -/
private def valueSlot (scope : List ScopeBinding) (name : String) : Option Nat := do
  let (i,.value) ← resolve scope name | none
  return i

/-- What the source says of one code request's graph, as of a unit's: its
source map, its statement entries' knowledge and its cuts. -/
structure CodeSource where
  sourceMap : SourceMap := []
  assertions : List (Nat × HeapKnowledge.Knowledge) := []
  cuts : List Nat := []

private structure Built where
  /-- The graph under construction: the claims' table, grown by annotations. -/
  types : SourceTypes.Table
  program : Program := []
  claims : List (PointClaim Nat) := []
  obligations : List ExpressionClaims.Required := []
  sourceMap : SourceMap := []
  assertions : List (Nat × HeapKnowledge.Knowledge) := []
  /-- Full statement-entry interfaces; absent assertions mean empty knowledge. -/
  cuts : List Nat := []
  /-- Labels the program mentions but no claim does, such as a pattern's
  literal index: search hints, never part of what is checked. -/
  hints : List Nat := []
  /-- The result an overloaded closure's body carries under the signature being
  compiled. A block body's type is its enclosing result annotation, which is
  one type for every signature; a closure that advertises several needs the
  one it is being checked against. Keyed by that body's span, so no nested
  expression is affected. -/
  resultOverride : Option (Span × Ty Nat) := none
  /-- While a `try` body or handler is compiled: where a throw out of a node
  goes, as a target over the handler's scope (the thrown value's slot, then
  the scope of the `try`), and the length of the `try`'s scope. Every node
  emitted meanwhile whose expression may throw names it. -/
  handler : Option (Target × Nat) := none
  /-- The graph code the body creates, nested code first, each at each
  signature it offers, and what the source says of each code's graph. -/
  codes : List CodeRequest := []
  codeSources : List CodeSource := []
  /-- Plans for nodes whose derivation the lowering already knows: search
  hints only, rendered where they can be and never obligations. -/
  nodePlans : List DirectProof.Plan := []

/-- Source-validation failures that already know their source site use the same
structured channel as proof obligations. Keeping the diagnostic construction
here prevents an adapter check from degrading into an unlocated exception. -/
private def locatedRefusal (T : SourceTypes.Table) (pos : Span)
    (role : DirectObligation.SourceRole) (reason : String) : String :=
  RequestJson.withDiagnostic s!"source refusal at [{pos.1},{pos.2}): {reason}"
    [("kind",toJson "source-refusal"),("phase",toJson "request-validation"),
     ("outcome",toJson "not-established"),("id",toJson s!"refusal:{pos.1}"),
     ("sourceMap",toJson (SourceMapEntry.mk pos role.wire none [])),
     ("reason",toJson reason),("fuel",toJson 0),("types",toJson T)]

private abbrev Compiler := StateT Built (Except String)

private def table : Compiler SourceTypes.Table := do return (← get).types

private def lower (m : SourceTypes.Lowering α) : Compiler α := do
  let s ← get
  let (a, T) ← m.run s.types
  set { s with types := T }
  return a

/-- Whether a claimed type is within a source annotation's: its rows among the
annotation's, up to rows with identical clauses, or else its inclusion proved
by a certificate the proved checker accepts. A generic application with
methods is one row for the module, the producer's `Values<number>` and the one
a method annotation names alike, so the first rule relates them; the proof is
for a claim narrower than its annotation. -/
def within (T : SourceTypes.Table) (C A : List Nat) : Bool :=
  (SourceTypes.canonical T C).all (SourceTypes.canonical T A).contains ||
    (let G := SourceTypes.graph T
     let pool := CertificateProducer.vocabulary G
       (ProgramTyping.readsFrom G ProgramTyping.closureFuel (C ++ A)) [] [C, A]
     match CertificateProducer.subtype G pool C A with
       | some proof => PositiveCertificates.check G C A proof
       | none => false)

/-- Whether two label lists denote the same type: each within the other. -/
def sameMeaning (T : SourceTypes.Table) (A B : List Nat) : Bool :=
  within T A B && within T B A

private def envCore (bound : Nat) (fc : SourceClaims.Function) (pos : Nat) (scope : List ScopeBinding) :
    Except String (List (Ty Nat)) := do
  let vars ← match fc.envs.lookup pos with
    | some vars => pure vars
    | none => throw s!"missing statement environment at {pos}"
  if !distinct (vars.map Prod.fst) then throw s!"duplicate environment binding at {pos}"
  scope.mapM fun b => do
    -- The slot holds the cell's identity. What the producer says `x` is now
    -- describes the contents, and is an observation, not this slot's type.
    let name := b.source.name
    if let some A := b.fixed then return A
    let some t := vars.lookup name | throw s!"missing claimed binding '{name}' at {pos}"
    let A ← (SourceClaims.resolve bound t).mapError fun msg =>
      if msg == "type claim unavailable from producer" then
        s!"unavailable claimed binding '{name}' at {pos}"
      else msg
    match b.storage with
    | .value => return A
    | .cell _ reference => return reference

private def env (fc : SourceClaims.Function) (pos : Nat) (scope : List ScopeBinding) :
    Compiler (List (Ty Nat)) := do
  (envCore (← table).length fc pos scope).mapError fun msg =>
    s!"source environment obligation at {pos}: {msg}"

/-- A pattern reads fields, never a method: a method is a member of its object,
called with it as receiver (`MethodMembers`); read off it, it is no function
value. -/
private def noMethodRead (G : PositiveGraphs.NormalGraph Nat) (A : Ty Nat) (fld : String) :
    Except String Unit :=
  if (PositiveRules.expand G A).any fun c => match c with
      | .refs _ _ _ _ ms _ => ms.any (·.key == fld) | _ => false then
    throw s!"a method '{fld}' read off its object is not a function value: it takes the object as its receiver"
  else pure ()

/-- Why an array rest is refused over an array whose contract does not fix its
length: its rest is a slice of a length known only at run time, which no
fixed list of reads is, and the calculus has no slice. -/
private def restOfUnknownLength : String :=
  "an array rest needs one tuple contract of required positions: the rest of an array of unknown length is a slice"

/-- The type claimed at a site: a source expression, or an array pattern's
rest. -/
private def claimAt (fc : SourceClaims.Function) (span : Span) : Compiler (Ty Nat) := do
  match fc.exprs.lookup span with
  | some t => (SourceClaims.resolve (← table).length t).mapError fun msg =>
      s!"source expression obligation at [{span.1},{span.2}): {msg}"
  | none => throw s!"no claimed type for the expression at {spanStr span}"

private def exprType (fc : SourceClaims.Function) (e : Fragment.Expr) : Compiler (Ty Nat) :=
  claimAt fc e.span

/-- The store type of an array claim: the type of its store field, held
invariantly or as a view. -/
private def storeOf (G : PositiveGraphs.NormalGraph Nat) (A : Ty Nat) : Option (Ty Nat) :=
  match PositiveRules.expand G A with
  | [.refs fs [] vs _ _ _] => fs.lookup SourceTypes.storeField <|> vs.lookup SourceTypes.storeField
  | _ => none

/-- A source numeric key must denote one valid array index. The two runtime
zeros name the same property although their numeric values remain distinct. -/
private def arrayIndex (G : PositiveGraphs.NormalGraph Nat) (K : Ty Nat) : Except String Nat := do
  let cs := PositiveRules.expand G K
  let .numLit b :: _ := cs
    | throw "a numeric array key needs a proved array-index singleton; ordinary numeric properties are not modeled"
  let some k := indexOfBits b
    | throw "numeric property keys outside the array-index range are outside the fragment"
  if !cs.all (fun c => match c with | .numLit b => indexOfBits b == some k | _ => false) then
    throw "a numeric array key needs one array index"
  return k

def arrayPrototypeName : String := SourceTypes.arrayPrototypeName

/-- A fresh array object's type: its store and prototype as fields, and its own
keys bounded to them, the type `alloc` gives before it is read as an array. -/
private def arrayObject (S : Ty Nat) : Compiler (Ty Nat) := do
  let label ← lower (SourceTypes.use (.refs [(SourceTypes.storeField, S),
    (SourceTypes.protoField, [SourceTypes.arrayProtoLabel])] [] [] [] []
    [⟨true, [SourceTypes.storeField, SourceTypes.protoField]⟩]))
  modify fun s => {s with hints := label :: s.hints}
  return [label]

/-- The slot holding `Array.prototype` in a scope. -/
private def prototypeSlot (scope : List ScopeBinding) : Except String Nat :=
  match resolve scope arrayPrototypeName with
  | some (i, .value) => pure i
  | _ => throw "an array needs Array.prototype, which this unit does not see"

/-- Allocate the array object holding the store in slot 0, with the prototype
from slot `proto`. -/
private def arrayTerm (proto : Nat) : Tm :=
  .makeAt .absent [SourceTypes.storeField, SourceTypes.protoField] [.var 0, .var proto]

/-- The literal index of one position, interned like any other number the
program mentions. -/
private def indexTerm (j : Nat) : Compiler Tm := do
  let b := bitsOfNat j
  let label ← lower (SourceTypes.use (.numLit b))
  modify fun s => {s with hints := label :: s.hints}
  return .num b

private def arrayKeyTerm (K : Ty Nat) : Compiler Tm := do
  let k ← arrayIndex (SourceTypes.graph (← table)) K
  let b := bitsOfNat k
  let label ← lower (SourceTypes.use (.numLit b))
  modify fun s => {s with hints := label :: s.hints}
  return .num b

/-- The type a binary operator's value is claimed at before it meets the
expression's claim: both Booleans for a comparison, strings for `+` with a
string operand, else the numeric family of its operands. -/
private def operatorResult (op : Arith) (A B : Ty Nat) : Compiler (Ty Nat) := do
  if op.relational || op == .eq then return [1, 2]
  let G := SourceTypes.graph (← table)
  let strings := fun (T : Ty Nat) =>
    let cs := PositiveRules.expand G T
    !cs.isEmpty && cs.all ProgramTyping.stringClause
  if op == .add && (strings A || strings B) then return [← lower (SourceTypes.use .str)]
  let cs := PositiveRules.expand G A
  if !cs.isEmpty && cs.all ProgramTyping.bigintClause then return [← lower (SourceTypes.use .bigint)]
  return [← lower (SourceTypes.use .num)]

/-- A unary operator as the binary one it is on its operand's numeric family,
with a constant right operand: `-x` is `x * -1`, `+x` is `x * 1` and `~x` is
`x ^ -1`, exactly, on numbers and on bigints alike. The family is the
operand's claimed one, which its own obligation establishes. `+` on a bigint
throws a `TypeError`, and an operand of both families has no one constant, so
each is refused. The constant's singleton is interned and offered to search. -/
private def unaryOperation (p : Span) (op : Fragment.UnaryOp) (B : Ty Nat) :
    Compiler (Arith × Tm × Ty Nat × ProgramCertificates.Rule Nat) := do
  let cs := PositiveRules.expand (SourceTypes.graph (← table)) B
  let located := s!"unsupported source expression at [{p.1},{p.2}): "
  let bigint ← if !cs.isEmpty && cs.all ProgramTyping.numberClause then pure false
    else if !cs.isEmpty && cs.all ProgramTyping.bigintClause then pure true
    else throw (located ++ "a unary numeric operator needs an operand of one numeric family, number or bigint")
  let (arith, factor) ← match op with
    | .neg => pure (Arith.mul, -1) | .plus => pure (.mul, 1) | .bitNot => pure (.xor, -1)
    | .typeof => throw "internal extraction error: typeof is not a numeric operator"
  if bigint then
    if op == .plus then throw (located ++ "unary + on a bigint throws a TypeError")
    let label ← lower (SourceTypes.use (.bigintLit factor))
    modify fun s => {s with hints := label :: s.hints}
    return (arith, .bigint factor, [label], .bigintLit)
  let b := (if factor < 0 then -1.0 else 1.0 : Float).toBits
  let label ← lower (SourceTypes.use (.numLit b))
  modify fun s => {s with hints := label :: s.hints}
  return (arith, .num b, [label], .numLit)

/-- The operand of `key in o`, whose test (`Tag.hasKey`) asks whether the
object owns the key. JavaScript throws on a primitive, where the test would
answer `false`, so the operand must be of object clauses. A class value is
refused: its static members are bound apart (`static C.x`), so it lacks keys
JavaScript's has. On the other objects of the fragment own keys are
JavaScript's, and the key names nothing a prototype holds
(`Fragment.inKeyRefusal`). -/
private def inOperand (p : Span) (tag : Tag) (B : Ty Nat) : Compiler Unit := do
  let .hasKey _ := tag | return
  let G := SourceTypes.graph (← table)
  let cs := PositiveRules.expand G B
  let located := s!"unsupported source expression at [{p.1},{p.2}): "
  if cs.any (fun | .ctors .. => true | _ => false) then
    throw (located ++ "`in` on a class value: its static members are bound apart from it")
  unless G.plainTy B && !cs.isEmpty && cs.all (fun
      | .refs .. | .dict .. | .arrs .. | .callable .. => true
      | _ => false) do
    throw (located ++ "`in` needs an object operand: it throws on a primitive")

/-- The keys `key in o` may test, from the key's claim: a union of string
singletons, each a key `in` answers as JavaScript does (`inKeyRefusal`). -/
private def inKeyList (p : Span) (K : Ty Nat) : Compiler (List String) := do
  let G := SourceTypes.graph (← table)
  let located := s!"unsupported source expression at [{p.1},{p.2}): "
  let keys := (PositiveRules.expand G K).filterMap fun
    | .strLit s => some s
    | _ => none
  unless G.plainTy K && !keys.isEmpty && keys.length == (PositiveRules.expand G K).length do
    throw (located ++ "`in` with a key that is not a union of string literals")
  let keys := keys.eraseDups
  for k in keys do
    if let some reason := Fragment.inKeyRefusal k then
      throw (located ++ s!"`in` with the key '{k}': {reason}")
  return keys

/-- `key in o` with the key in `keySlot` and the object in `slot`: the key's
singletons, tested in turn, each selecting its own key's test; the last
needs no test, since the key is one of them. -/
def inKeysTerm (keys : List String) (keySlot slot : Nat) : Tm :=
  match keys.reverse with
  | [] => .fls
  | last :: earlier => earlier.reverse.foldr (fun k rest =>
      .ite (.test (.strEq k) (.var keySlot)) (has k) rest) (has last)
where has (k : String) : Tm := .ite (.test (.hasKey (.str k)) (.var slot)) .tru .fls

/-- `o[k]` with the key in `keySlot` a union of singletons: each singleton,
tested in turn, selects the read of its own key (`reads`); the last needs no
test, since the key is one of them. -/
def keyedReadTerm (arms : List (Tag × Tm)) (keySlot : Nat) : Tm :=
  match arms.reverse with
  | [] => .undef
  | (_, last) :: earlier => earlier.reverse.foldr (fun (tag, read) rest =>
      .ite (.test tag (.var keySlot)) read rest) last

/-- `typeof v`, in the order the lowering tests it: each tag holds of exactly
the values `typeof` names by its string, and a value none of them holds of is
an object with call code, which `typeof` names `"function"`. -/
def typeofAnswers : List (Tag × String) :=
  [(.isUndef, "undefined"), (.typeofObject, "object"), (.isBool, "boolean"), (.isNum, "number"),
   (.isStr, "string"), (.isBigint, "bigint"), (.isSymbol, "symbol")]

/-- `typeof` of the value in `slot`: one tag test per answer, in order. -/
def typeofTerm (slot : Nat) : Tm :=
  typeofAnswers.foldr (fun (tag, s) rest => .ite (.test tag (.var slot)) (.str s) rest) (.str "function")

/-- What a computed key names, by its claimed type: a field for a string
singleton, a dictionary lookup for a broad string, or an element of the
array's store for a number. On a receiver that is only records and
dictionaries, a number singleton names the field its `ToString` spells
(`ToPropertyKey`), as `o[0]` reads `o["0"]`, both zeros spelling `0`; and a
broad number or symbol is a dictionary lookup, through an index over its keys.
The key stays in
the program, evaluated after the receiver and before any right side, and its
expression obligation must establish that claim. -/
private inductive KeyKind where
  | field (name : String)
  | dynamic
  | element

/-- Whether an expression is claimed only at records and dictionaries: no
array store, no primitive, nothing else. Such an object's property named by a
number is the field its `ToString` spells; an array's is its store's
element. -/
private def recordReceiver (fc : SourceClaims.Function) (e : Fragment.Expr) : Compiler Bool := do
  let G := SourceTypes.graph (← table)
  let R ← exprType fc e
  let cs := PositiveRules.expand G R
  return !cs.isEmpty && (storeOf G R).isNone && cs.all fun
    | .refs .. | .dict .. => true | _ => false

/-- Whether an expression is claimed only at dictionaries, whose indexes a
broad key reads through. -/
private def dictReceiver (fc : SourceClaims.Function) (e : Fragment.Expr) : Compiler Bool := do
  let cs := PositiveRules.expand (SourceTypes.graph (← table)) (← exprType fc e)
  return !cs.isEmpty && cs.all fun | .dict .. => true | _ => false

/-- The singletons of a key's claim, each with the tag that tests a value for
it and the property key it converts to (`ToPropertyKey`: a number's is the
key its `ToString` spells). `none` unless every clause is a string or number
singleton; NaN, which no equality test finds, is not one. -/
def keySingletons (G : PositiveGraphs.NormalGraph Nat) (K : Ty Nat) : Option (List (Tag × PropKey)) :=
  let cs := PositiveRules.expand G K
  if !G.plainTy K || cs.isEmpty then none else
  cs.mapM fun c => match c with
    | .strLit v => some (.strEq v, .str v)
    | .numLit b => if numberEqual b b then some (.numEq b, .str (numberToString b)) else none
    | _ => none

private def keyField (fc : SourceClaims.Function) (key : Fragment.Expr)
    (string : Bool := false) (record : Bool := false) (dict : Bool := false) : Compiler KeyKind := do
  let K ← exprType fc key
  let G := SourceTypes.graph (← table)
  let spelled := fun (s : String) =>
    if SourceTypes.reservedKey s then throw s!"'{s}' is internal to the model, not a source property"
    else pure (KeyKind.field s)
  -- Several singletons on an object: each reads the member its key names
  -- (`keyedReadTerm`).
  if record || dict then
    if let some keys := keySingletons G K then
      if (keys.map (·.2)).eraseDups.length > 1 then
        for (_, k) in keys do
          if let .str s := k then
            if SourceTypes.reservedKey s then throw s!"'{s}' is internal to the model, not a source property"
        return .dynamic
  match PositiveRules.expand G K with
  | [.strLit s] => spelled s
  | [.str] => pure .dynamic
  | [.num] | [.symbol] => if dict then pure .dynamic else
    if string && decide (Answers G K .isNum true) then return .element else do
      let _ ← arrayIndex G K
      pure .element
  | .numLit b :: cs =>
    if record && cs.all (fun c => match c with
        | .numLit b' => numberToString b' == numberToString b | _ => false) then
      spelled (numberToString b)
    else
      if string && decide (Answers G K .isNum true) then return .element
      let _ ← arrayIndex G K
      pure .element
  | _ =>
    -- A string's index properties are its code units: any number names one
    -- or none (`elemStr`); an array's needs one proved index.
    if string && decide (Answers G K .isNum true) then return .element
    let _ ← arrayIndex G K
    pure .element

/-- The tag testing equality with the one value every member of `A` is:
null, undefined, a number (both zeros are one), a string, a Boolean or a
bigint. -/
private def singletonTag (G : PositiveGraphs.NormalGraph Nat) (A : Ty Nat) : Option Tag :=
  if A == [0] then some Tag.isNul else if A == [3] then some Tag.isUndef else
    match PositiveRules.expand G A with
    | .numLit bits :: cs =>
      if cs.all (fun c => match c with | .numLit b => numberEqual bits b | _ => false)
      then some (.numEq bits) else none
    | [.strLit s] => some (.strEq s)
    | [.boolLit b] => some (.boolEq b)
    | [.bigintLit i] => some (.bigintEq i)
    | _ => none

mutual
/-- A claimed singleton operand (null, undefined, a number, a string, a Boolean
or a bigint) selects a tag-test implementation, never an assumption: both
operands remain in the program, in source order, and their expression
obligations must establish the singleton used by this translation. Without
one, the comparison is the strict-equality operator (`Arith.eq`), which the
operator rule admits where either operand is a primitive; `!==` is its
negation. -/
private partial def comparisonsExpr (fc : SourceClaims.Function) (e : Fragment.Expr) :
    Compiler Fragment.Expr := do
  match e with
  | .var .. | .lit .. | .done .. => pure e
  | .equality p eq l r =>
    let l ← comparisonsExpr fc l
    let r ← comparisonsExpr fc r
    let L ← exprType fc l
    let R ← exprType fc r
    let G := SourceTypes.graph (← table)
    let select := singletonTag G
    match select R, select L with
    | some tag, _ => pure (.singletonTest p tag eq true l r)
    | _, some tag => pure (.singletonTest p tag eq false l r)
    | _, _ =>
      -- Two objects are strictly equal when they are one object. An object
      -- value here is its field locations, so an object without a field
      -- (a function, a record of optional fields only, any value of
      -- `unknown`) carries no identity of its own: two operands that may
      -- both be such objects are refused.
      let identified := fun (c : PositiveNormalization.Clause (Ty Nat)) =>
        ProgramTyping.primitiveClause c || ProgramTyping.identityClause c
      if (PositiveRules.expand G L).any (fun c => !identified c) &&
          (PositiveRules.expand G R).any (fun c => !identified c) then
        throw s!"unsupported source expression at [{p.1},{p.2}): strict equality of two operands that may both be objects without a field compares identities, which such objects do not carry in the model"
      let same := Fragment.Expr.arith p .eq l r
      pure (if eq then same else .not p same)
  | .logical p a l r => return .logical p a (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .coalesce p l r => return .coalesce p (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .optional p m r b => return .optional p m (← comparisonsExpr fc r) (← comparisonsExpr fc b)
  | .nullishAssign p n np r => return .nullishAssign p n np (← comparisonsExpr fc r)
  | .assign p n np r => return .assign p n np (← comparisonsExpr fc r)
  | .shapeTest p t eq e => return .shapeTest p t eq (← comparisonsExpr fc e)
  | .singletonTest p t eq tl l r => return .singletonTest p t eq tl (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .not p e => return .not p (← comparisonsExpr fc e)
  | .unary p op e => return .unary p op (← comparisonsExpr fc e)
  | .cast p annot e => return .cast p annot (← comparisonsExpr fc e)
  | .ctor p lam => return .ctor p (← comparisonsExpr fc lam)
  | .construct p f args ts => return .construct p (← comparisonsExpr fc f) (← args.mapM (comparisonsExpr fc)) ts
  | .alloc p ns es => return .alloc p ns (← es.mapM (comparisonsExpr fc))
  | .build p ns es => return .build p ns (← es.mapM (comparisonsExpr fc))
  | .read p f e => return .read p f (← comparisonsExpr fc e)
  | .write p f l r => return .write p f (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .index p _ e key =>
    let key ← comparisonsExpr fc key
    let e ← comparisonsExpr fc e
    let string := decide (Answers (SourceTypes.graph (← table)) (← exprType fc e) .isStr true)
    match ← keyField fc key string (← recordReceiver fc e) (← dictReceiver fc e) with
    | .field s => return .index p (some s) e key
    | .dynamic => return .index p none e key
    | .element => return .elemAt p e key
  | .arrayLit p es => return .arrayLit p (← es.mapM (comparisonsExpr fc))
  | .arrayAssign p targets rest rhs =>
    let targets ← targets.mapM fun q => do
      return { q with default_ := ← q.default_.mapM (comparisonsExpr fc) }
    return .arrayAssign p targets rest (← comparisonsExpr fc rhs)
  | .elemAt p e key => return .elemAt p (← comparisonsExpr fc e) (← comparisonsExpr fc key)
  | .elemWrite p r key rhs =>
    return .elemWrite p (← comparisonsExpr fc r) (← comparisonsExpr fc key) (← comparisonsExpr fc rhs)
  | .arith p op l r => return .arith p op (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .comma p l r => return .comma p (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .inKeys p k o => return .inKeys p (← comparisonsExpr fc k) (← comparisonsExpr fc o)
  | .logicalAssign p op target rhs =>
    return .logicalAssign p op (← comparisonsExpr fc target) (← comparisonsExpr fc rhs)
  | .update p op target rhs post =>
    return .update p op (← comparisonsExpr fc target) (← rhs.mapM (comparisonsExpr fc)) post
  | .indexWrite p _ r key rhs =>
    let key ← comparisonsExpr fc key
    let r ← comparisonsExpr fc r
    let rhs ← comparisonsExpr fc rhs
    match ← keyField fc key (record := ← recordReceiver fc r) (dict := ← dictReceiver fc r) with
    | .field s => return .indexWrite p (some s) r key rhs
    | .dynamic => throw "a dynamic index write is outside the dictionary fragment: it may add a key, and the calculus adds no key to an existing object"
    | .element => return .elemWrite p r key rhs
  | .withValue p f i ft bt => return .withValue p (← comparisonsExpr fc f) (← comparisonsExpr fc i) ft bt
  | .lambda p receiver tps ps defaults rest result b =>
    return .lambda p receiver tps ps (← defaults.attach.mapM fun ⟨(i,d),_⟩ => do
      return (i, ← comparisonsExpr fc d)) rest result (← comparisonsExpr fc b)
  | .bindWithReceiver p c r args => return .bindWithReceiver p (← comparisonsExpr fc c) (← comparisonsExpr fc r) (← args.mapM (comparisonsExpr fc))
  | .callWithReceiver p c r args => return .callWithReceiver p (← comparisonsExpr fc c) (← comparisonsExpr fc r) (← args.mapM (comparisonsExpr fc))
  | .applyWithReceiver p c r list => return .applyWithReceiver p (← comparisonsExpr fc c) (← comparisonsExpr fc r) (← list.mapM (comparisonsExpr fc))
  | .call p c args spread ts =>
    return .call p (← comparisonsExpr fc c) (← args.mapM (comparisonsExpr fc)) spread ts
  | .invoke p c args spreads typeArgs =>
    -- A field, by name or by a string key, or an array element by a numeric
    -- key: `comparisonsExpr` resolves the key from its claim.
    return .invoke p (← comparisonsExpr fc c) (← args.mapM (comparisonsExpr fc)) spreads typeArgs
  | .atEnv p e => return .atEnv p (← comparisonsExpr fc e)
  | .seqBody p i b => return .seqBody p (← comparisonsExpr fc i) (← comparisonsExpr fc b)
  | .ifBody p result c t e => return .ifBody p result (← comparisonsExpr fc c) (← comparisonsExpr fc t) (← comparisonsExpr fc e)
  | .letBody p n annot i b => return .letBody p n annot (← comparisonsExpr fc i) (← comparisonsExpr fc b)
  | .throwBody p e => return .throwBody p (← comparisonsExpr fc e)
  | .destructBody p t i b => do
    let t ← t.mapDefaultsM (comparisonsExpr fc)
    return .destructBody p t (← comparisonsExpr fc i) (← comparisonsExpr fc b)
  | .block p ss => return .block p (← ss.mapM (comparisonsStmt fc))

private partial def comparisonsStmt (fc : SourceClaims.Function) (s : Fragment.Stmt) :
    Compiler Fragment.Stmt := do
  match s with
  | .ret p e => return .ret p (← comparisonsExpr fc e)
  | .constants p bs => return .constants p (← bs.mapM fun b => do return { b with init := ← comparisonsExpr fc b.init })
  | .mutables p bs => return .mutables p (← bs.mapM fun b => do return { b with init := ← comparisonsExpr fc b.init })
  | .destructure p target d init =>
    return .destructure p (← target.mapDefaultsM (comparisonsExpr fc)) (← d.mapM (comparisonsExpr fc))
      (← comparisonsExpr fc init)
  | .effect p e => return .effect p (← comparisonsExpr fc e)
  | .ite p c t e =>
    return .ite p (← comparisonsExpr fc c) (← t.mapM (comparisonsStmt fc))
      (← e.mapM (fun ss => ss.mapM (comparisonsStmt fc)))
  | .loop p c b u =>
    return .loop p (← comparisonsExpr fc c) (← b.mapM (comparisonsStmt fc)) (← u.mapM (comparisonsStmt fc))
  | .forOf p n np it i b => return .forOf p n np it (← comparisonsExpr fc i) (← b.mapM (comparisonsStmt fc))
  | .block p k b => return .block p k (← b.mapM (comparisonsStmt fc))
  | .throw p e => return .throw p (← comparisonsExpr fc e)
  | .tryStmt p b h f =>
    let h ← h.mapM fun (param, c) => do return (param, ← c.mapM (comparisonsStmt fc))
    return .tryStmt p (← b.mapM (comparisonsStmt fc)) h (← f.mapM (·.mapM (comparisonsStmt fc)))
  | .closing p c b => return .closing p (← c.mapM (comparisonsStmt fc)) (← b.mapM (comparisonsStmt fc))
  | .brk .. | .cont .. => pure s
end

mutual
/-- Storage is selected from source assignments, including writes in nested
closures. Active-name shadowing is rejected by the lowering, so a matching
name cannot silently designate a different binding. Producer claims cannot
choose which parameters are mutable. -/
private partial def assignsExpr (name : String) : Fragment.Expr → Bool
  | .var .. | .lit .. | .done .. => false
  | .assign _ target _ rhs | .nullishAssign _ target _ rhs => target == name || assignsExpr name rhs
  | .lambda _ _ _ _ defaults _ _ e =>
    defaults.attach.any (fun ⟨d,_⟩ => assignsExpr name d.2) || assignsExpr name e
  | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e | .atEnv _ e
  | .throwBody _ e =>
    assignsExpr name e
  | .equality _ _ a b | .logical _ _ a b | .coalesce _ a b | .optional _ _ a b
  | .singletonTest _ _ _ _ a b | .write _ _ a b | .withValue _ a b _ _ | .index _ _ a b
  | .seqBody _ a b | .letBody _ _ _ a b => assignsExpr name a || assignsExpr name b
  | .destructBody _ t a b => assignsExpr name a || t.defaults.any (assignsExpr name) || assignsExpr name b
  | .indexWrite _ _ a b c | .elemWrite _ a b c => assignsExpr name a || assignsExpr name b || assignsExpr name c
  | .arith _ _ a b | .elemAt _ a b | .comma _ a b | .inKeys _ a b => assignsExpr name a || assignsExpr name b
  | .arrayLit _ es => es.any (assignsExpr name)
  | .arrayAssign _ targets rest rhs => targets.any (fun q => q.name == name ||
      (q.default_.map (assignsExpr name)).getD false) || rest.any (·.2.2.name == name) ||
      assignsExpr name rhs
  | .logicalAssign _ _ target rhs =>
    (match target with | .var _ n => n == name | _ => false) ||
      assignsExpr name target || assignsExpr name rhs
  | .update _ _ target rhs _ =>
    (match target with | .var _ n => n == name | _ => false) ||
      assignsExpr name target || (rhs.map (assignsExpr name)).getD false
  | .alloc _ _ es | .build _ _ es => es.any (assignsExpr name)
  | .call _ f args _ _ | .invoke _ f args _ _ => assignsExpr name f || args.any (assignsExpr name)
  | .callWithReceiver _ f r args | .bindWithReceiver _ f r args =>
    assignsExpr name f || assignsExpr name r || args.any (assignsExpr name)
  | .ctor _ lam => assignsExpr name lam
  | .construct _ f args _ => assignsExpr name f || args.any (assignsExpr name)
  | .applyWithReceiver _ f r list =>
    assignsExpr name f || assignsExpr name r || (list.map (assignsExpr name)).getD false
  | .ifBody _ _ c t e => assignsExpr name c || assignsExpr name t || assignsExpr name e
  | .block _ ss => ss.any (assignsStmt name)

private partial def assignsStmt (name : String) : Fragment.Stmt → Bool
  | .ret _ e | .effect _ e | .throw _ e => assignsExpr name e
  | .tryStmt _ b h f => b.any (assignsStmt name) || ((h.map (·.2)).getD []).any (assignsStmt name) ||
    (f.getD []).any (assignsStmt name)
  | .constants _ bs | .mutables _ bs => bs.any fun b => assignsExpr name b.init
  | .destructure _ target d init => assignsExpr name init ||
    (d.toList ++ target.defaults).any (assignsExpr name)
  | .ite _ c t e => assignsExpr name c || t.any (assignsStmt name) ||
    (e.getD []).any (assignsStmt name)
  | .loop _ c b u => assignsExpr name c || b.any (assignsStmt name) || u.any (assignsStmt name)
  | .forOf _ _ _ _ i b => assignsExpr name i || b.any (assignsStmt name)
  | .block _ _ b => b.any (assignsStmt name)
  | .closing _ c b => c.any (assignsStmt name) || b.any (assignsStmt name)
  | .brk .. | .cont .. => false
end

/-- Every name a statement's expressions mention, bound or not: a superset of
the module functions its body can reach. -/
partial def stmtNames : Fragment.Stmt → List String
  | .ret _ e | .effect _ e | .throw _ e => e.freeNames
  | .tryStmt _ b h f => b.flatMap stmtNames ++ ((h.map (·.2)).getD []).flatMap stmtNames ++
    (f.getD []).flatMap stmtNames
  | .constants _ bs | .mutables _ bs => bs.flatMap fun b => b.init.freeNames
  | .destructure _ target d init => init.freeNames ++
    (d.toList ++ target.defaults).flatMap Fragment.Expr.freeNames ++ target.slices.map (Fragment.restFromName ·.2)
  | .ite _ c t e => c.freeNames ++ t.flatMap stmtNames ++ (e.getD []).flatMap stmtNames
  | .loop _ c b u => c.freeNames ++ b.flatMap stmtNames ++ u.flatMap stmtNames
  | .forOf _ _ _ it i b => it :: i.freeNames ++ b.flatMap stmtNames
  | .block _ _ b => b.flatMap stmtNames
  | .closing _ c b => c.flatMap stmtNames ++ b.flatMap stmtNames
  | .brk .. | .cont .. => []

/-- A module function's value as its callers see it: an ordinary function at
exactly its annotated parameters and result. A leading `this: T` parameter
is its receiver, which every call passes (a plain call `undefined`), and no
position; without one the receiver is irrelevant. A rest parameter
contributes its tuple's positions or its array's element. -/
def moduleArrow (g : Fragment.Fn) : Except String Json := do
  let top := Json.mkObj [("top", toJson true), ("atoms", toJson ([] : List Json))]
  let (receiver, params) := match g.params with
    | p :: ps => if p.name == "this" then (p.ty, ps) else (top, g.params)
    | [] => (top, [])
  let fixed := if params.getLast?.any (·.rest) then params.dropLast else params
  let (positions, rest) ← match params.getLast? with
    | some p =>
      if !p.rest then pure (fixed.map (·.ty), [])
      else match Fragment.arrayElement p.ty (readonly := true) with
        | some e => pure (fixed.map (·.ty), [("rest", e)])
        | none => pure (fixed.map (·.ty) ++ (← Fragment.tupleRequired p.ty), [])
    | none => pure ([], [])
  return Json.mkObj [("top", toJson false), ("atoms", toJson [Json.mkObj
    ([("a", toJson "function"), ("this", receiver), ("params", toJson positions)] ++ rest ++
      [("result", g.ret), ("construct", toJson "unknown"), ("array", toJson "unknown")])])]

/-- The same values with each label that is a union row, a declaration such as
`type Maybe = number | undefined`, replaced by one label per clause: a tag
slice tells the values apart clause by clause, never inside one label. -/
private def byClause (R : Ty Nat) : Compiler (Ty Nat) := do
  let G := SourceTypes.graph (← table)
  let parts ← R.mapM fun a =>
    let cs := PositiveRules.expand G [a]
    if !G.plain a || cs.length ≤ 1 then pure [a] else cs.mapM fun c => lower (SourceTypes.use c)
  pure parts.flatten.eraseDups

/-- A terminal branch uses the enclosing source result annotation, not a
fabricated expression claim at the if statement's span. -/
private def closureType (fc : SourceClaims.Function) (e : Fragment.Expr) : Compiler (Ty Nat) := do
  if let some (p, T) := (← get).resultOverride then
    if p == e.span then return T
  match e with
  | .atEnv _ b | .letBody _ _ _ _ b | .seqBody _ _ b | .destructBody _ _ _ b => closureType fc b
  | .done _ => pure [0]
  -- A throw has every type: the empty union, which every result contains.
  | .throwBody .. => pure []
  | .ifBody _ (some result) _ _ _ => do lower (Fragment.callableType result)
  | e => exprType fc e

/-- A term that cannot throw: a value, or a slot, which holds one. Every other
node inside a `try` names its handler. -/
private def cannotThrow : Tm → Bool
  | .var _ => true
  | t => isVal t

/-- The handler a node emitted now names: the current one, its target's slots
read from the thrown value's (0) and from the `try`'s scope, which the node's
scope ends with, past the node's own `Γ.length - n` inner slots. -/
private def nodeHandler (Γ : List (Ty Nat)) (t : Tm) : Compiler (Option Target) := do
  match (← get).handler with
  | none => return none
  | some (entry, n) =>
    if cannotThrow t then return none
    if Γ.length < n then
      throw "internal extraction error: a node inside a try is outside the try's scope"
    let inner := Γ.length - n
    return some ⟨entry.label, some ((entry.mapping.getD (List.range (n+1))).map
      fun i => if i == 0 then 0 else i + inner)⟩

private def emit (t : Tm) (k : Continuation) (Γ : List (Ty Nat)) (A : Ty Nat) :
    Compiler Target := do
  let handler ← nodeHandler Γ t
  let s : Built ← get
  set { s with program := s.program ++ [(⟨t,k,handler⟩ : ControlFlow.Node)]
               claims := s.claims ++ [(⟨Γ,A⟩ : PointClaim Nat)]
               sourceMap := s.sourceMap ++ [none] }
  return ⟨s.program.length, none⟩

/-- Record this node's source map entry. Explanatory only; never part of the
certified request. The context must be describable binding for binding: a
context this cannot name is an extraction bug, not a slot number for a reader,
so it fails here rather than reaching a message. -/
private def emitAt (pos : Span) (t : Tm) (k : Continuation) (Γ : List (Ty Nat)) (A : Ty Nat)
    (role : String := "node-typing") (environmentStart : Option Nat := none)
    (scope : List ScopeBinding := []) : Compiler Target := do
  let target ← emit t k Γ A
  if scope.length != Γ.length then
    throw s!"internal extraction error: source map covers {scope.length} of {Γ.length} bindings at {pos.1}"
  if let some b := scope.find? (!·.source.describes) then
    throw s!"internal extraction error: undescribed binding '{b.source.name}' at {pos.1}"
  modify fun s =>
    { s with sourceMap := s.sourceMap.set target.label (some ⟨pos,role,environmentStart,sources scope⟩) }
  return target

/-- The fields every record of a type names: where each of its clauses is a
record naming them, the locations of an object of the type. -/
private def commonFields (G : Verification.Model.PositiveGraphs.NormalGraph Nat) (A : Ty Nat) : List PropKey :=
  match PositiveRules.expand G A with
  | .refs fs _ _ _ _ _ :: _ =>
    (fs.map Prod.fst).eraseDups.filter (HeapExpressionRules.fieldOperand (PositiveRules.expand G A))
  | _ => []

/-- A node whose derivation the lowering knows: its plan, cast to the node's
claim, joins the search's known evidence, so the node is not searched. -/
private def emitPlanned (pos : Span) (plan : DirectProof.Plan) (k : Continuation)
    (Γ : List (Ty Nat)) (A : Ty Nat) (role : String := "node-typing")
    (scope : List ScopeBinding := []) : Compiler Target := do
  modify fun s => { s with nodePlans := s.nodePlans ++ [DirectProof.cast Γ A plan] }
  emitAt pos plan.term k Γ A role (scope := scope)

/-- The cells this lowering allocated sit at locations no other object in
scope has: a private cell's identity never becomes a source value, and every
record-typed slot holds something else. Stated at each cut so the allocation's
freshness survives the reset of knowledge there; every incoming edge proves
it, from the allocation or from the cut before. What the allocation proves is
about the fields the older slots' records named then (`apart`), whatever a
later test narrowed them to, and about the objects allocated after it, other
cells and fresh constants; an object a later call returned may be any
object. -/
private def distinctLinks (G : Verification.Model.PositiveGraphs.NormalGraph Nat) (scope : List ScopeBinding)
    (Γ : List (Ty Nat)) : HeapLinks.Links :=
  scope.zipIdx.flatMap fun (b,i) =>
    match b.storage with
    | .cell .. =>
      Γ.zipIdx.flatMap fun (A,j) =>
        if i == j then [] else
        let other := scope[j]?
        let isCell := other.any fun o => match o.storage with | .cell .. => true | .value => false
        let fields :=
          if j > i || (b.param && other.any (·.param)) then
            -- Older than the cell: the fields its record named when the cell
            -- was allocated, where that is known.
            match b.apart with
            | some older =>
              match older[j - i - 1]? with
              | some B => (commonFields G A).filter (commonFields G B).contains
              | none => []
            | none => commonFields G A
          else if isCell || other.any (·.fresh) then commonFields G A
          else []
        fields.map fun f => (⟨i,j,false,valueField,true,f,false⟩ : HeapLinks.Link)
    | .value => []

/-- A checkpoint is an actual no-op graph node. Every incoming edge must
justify its supplied current-heap assertion, including backedges. -/
private def checkpoint (pos : Span) (Γ : List (Ty Nat)) (facts : HeapFacts.Facts)
    (next : Target) (entry : Option Nat := none) (scope : List ScopeBinding := []) :
    Compiler Target := do
  let G := SourceTypes.graph (← table)
  let links := if entry.isSome then distinctLinks G scope Γ else []
  if facts.isEmpty && links.isEmpty then return next
  let t ← emitAt pos .nul (.effect next) Γ [0] "heap-observation" entry scope
  modify fun s => { s with assertions := s.assertions ++ [(t.label,⟨facts,[],links⟩)] }
  return t

private def contents (A : Ty Nat) : Compiler (List HeapFacts.Atom) := do
  let T ← table
  if !RequestJson.validTy T.length A then throw "invalid current-content type label"
  let some R := HeapKnowledge.atoms (SourceTypes.graph T) A
    | throw "current-content predicate must be a supported primitive predicate"
  return R

/-- Record a source obligation with its source map, under the same invariant as
`emitAt`: every context binding must be describable in the words of the source. -/
private def obligation (pos : Span) (j : ProgramCertificates.Sequent Nat) (plan : Option DirectProof.Plan)
    (role : String) (scope : List ScopeBinding) : Compiler Unit := do
  if scope.length != j.context.length then
    throw s!"internal extraction error: source map covers {scope.length} of {j.context.length} bindings at {pos.1}"
  if scope.any (!·.source.describes) then
    throw s!"internal extraction error: undescribed binding at {pos.1}"
  modify fun s => { s with obligations := s.obligations ++ [⟨pos,j,plan,role,sources scope⟩] }

/-- Ordinary lambda proofs cannot retain transient heap observations across
calls. Require their declared storage contract to imply such an observation
uniformly; this is a located proof obligation, never a discarded assertion. -/
private def persistentObservation (d : Descriptor) (pos : Span) (A : Ty Nat)
    (fld : PropKey) (R : Ty Nat) : Compiler Unit := do
  -- The obligation below is an inclusion of types, so the observed type needs
  -- only to be one this table names. It does not need a supported primitive predicate:
  -- that is what a primitive assertion on an edge needs, and this is not one.
  if !RequestJson.validTy (← table).length R then throw "invalid current-content type label"
  let clauses := PositiveRules.expand (SourceTypes.graph (← table)) A
  if clauses.isEmpty then throw "current-content assertion requires nonempty cell contracts"
  let invariants ← clauses.mapM fun clause => do
    let .refs W [] [] := clause
      | throw "current-content assertion requires only cell contracts"
    let some Wc := W.lookup fld
      | throw s!"current-content assertion names a field '{fld}' the contract does not have"
    pure Wc
  let W := invariants.flatten.eraseDups
  let plan := DirectProof.var [W] 0 R
  obligation pos plan.goal (some plan) "heap-observation" [held d]

/-- Mutable entry types are assertions about contents, not reference types.
Supported primitive assertions are checked on every incoming edge. Other claims
must follow from the stable storage contract; no claim is silently dropped. -/
private def entryFacts (fc : SourceClaims.Function) (pos : Nat) (scope : List ScopeBinding) :
    Compiler HeapFacts.Facts := do
  let cs := (fc.entryCurrent.lookup pos).getD []
  let vars := (fc.envs.lookup pos).getD []
  scope.zipIdx.foldlM (fun facts (b,i) => do
    let mut facts := facts
    if let .cell contract reference := b.storage then
      let some candidate := vars.lookup b.source.name
        | throw s!"missing claimed binding '{b.source.name}' at {pos}"
      let A ← SourceClaims.resolve (← table).length candidate
      let G := SourceTypes.graph (← table)
      if contract.all A.contains then
        persistentObservation b.source (pos,pos+1) reference valueField A
      else
        match HeapKnowledge.atoms G A with
        | some atoms => facts := facts ++ [⟨i,atoms,valueField⟩]
        | none =>
          -- Contents no `undefined` is among, of any shape: the cell holds
          -- some other value, and a read of it is its contract less
          -- `undefined` (`slicedRead`).
          if G.plainTy A && (PositiveRules.expand G A).all
              (fun c => ProgramTyping.tagClause .isUndef c == some false) then
            facts := facts ++ [⟨i,[.defined],valueField⟩]
          else persistentObservation b.source (pos,pos+1) reference valueField A
    match cs.lookup b.source.name with
    | none => return facts
    | some asserted =>
      -- One assertion per named field of the record this binding holds.
      -- A field claim outside the primitive predicate vocabulary is not
      -- dropped: the storage contract must imply it, as above.
      let T ← table
      let reference ← match b.storage with
        | .value =>
          let some candidate := vars.lookup b.source.name
            | throw s!"missing claimed binding '{b.source.name}' at {pos}"
          SourceClaims.resolve T.length candidate
        | .cell contract _ => pure contract
      for (fld, A) in asserted do
        if !RequestJson.validTy T.length A then throw "invalid current-content type label"
        match b.storage with
        | .cell .. =>
          -- Slot i is the private holder, not the object inside it. A field
          -- observation cannot be attached to the holder's own value field.
          persistentObservation b.source (pos,pos+1) reference fld A
        | .value => match HeapKnowledge.atoms (SourceTypes.graph T) A with
          | some atoms => facts := facts ++ [⟨i,atoms,fld⟩]
          | none => persistentObservation b.source (pos,pos+1) reference fld A
      return facts) []

/-- A dot cannot occur in a source binding identifier, so these names designate
administrative read snapshots without colliding with source variables. -/
private def snapshotName (name field : String) : String := name ++ "." ++ field
/-- The snapshot a read of a named field may be saved in: a string field's.
A symbol-keyed read (`xs[marker]`) is never saved; it is read where it is. -/
private def readSnapshot (name : String) : PropKey → Option String
  | .str field => some (snapshotName name field)
  | .sym _ => none
/-- A snapshot is named by a string field. Source syntax reads only string
keys, so a symbol key asserted for a snapshot is refused, not encoded: no
string spelling of it is distinct from every string key. -/
private def stringKey : PropKey → Except String String
  | .str name => .ok name
  | .sym _ => .error "a symbol-keyed field has no source snapshot"
-- A saved local value is different from a field of the object it contains.
-- This prefix cannot begin a source identifier or a name.field snapshot.
private def localSnapshotName (name : String) : String := ".local:" ++ name
private def isSnapshot (name : String) : Bool := name.any (· == '.')

private def observed (scope : List ScopeBinding) (Γ : List (Ty Nat))
    (snapshot : String) (d : Descriptor) (pos : Span) (A : Ty Nat)
    (fld : PropKey) (R : Ty Nat) : Compiler Unit := do
  if let some i := (names scope).idxOf? snapshot then
    let plan := DirectProof.var Γ i R
    obligation pos plan.goal (some plan) "heap-observation" scope
  else
    persistentObservation d pos A fld R

/-- The record a group of an object literal's fields allocates: exactly their
keys, each at its initializer's type, which its own obligation establishes. -/
private def groupType (ns : List String) (As : List (Ty Nat)) : Compiler (Ty Nat) := do
  let keys := ns.map PropKey.str
  let label ← lower (SourceTypes.use (.refs (keys.zip As) [] [] [] [] [⟨true, keys⟩]))
  -- A type the search may need at a node it types on its own.
  modify fun s => {s with hints := label :: s.hints}
  return [label]

/-- The type an object literal's claim states for each key it names, where
its records agree on it: a field initializer is built at it, as a literal's
fields are at its claim's. -/
private def claimedFields (A : Ty Nat) : Compiler (List (String × Ty Nat)) := do
  let G := SourceTypes.graph (← table)
  let keyed := fun (ps : List (PropKey × Ty Nat)) => ps.filterMap fun (k, T) => match k with
    | .str s => some (s, T) | .sym _ => none
  let each := (PositiveRules.expand G A).map fun c => match c with
    | .refs fs [] vs os _ _ | .dict fs [] vs _ os _ _ _ => keyed (fs ++ vs ++ os.map fun o => (o.key, o.type))
    | _ => []
  -- Over a union, a key every record naming it states at one type.
  let all := each.flatten
  return all.filter fun (k, T) => all.all fun (k', T') => k' != k || T' == T

/-- The type a merge of a source of type `B` onto an accumulator of type `A`
is given, less the dropped keys: one record per pair of their clauses
(`ObjectMerge.mergeResult`), which the merge rule checks. -/
private def mergeType (A B : Ty Nat) (drop : List PropKey := []) : Compiler (Ty Nat) := do
  let G := SourceTypes.graph (← table)
  let ca := PositiveRules.expand G A
  let cb := PositiveRules.expand G B
  if ca.isEmpty then throw "internal: an object literal's accumulator has no clause"
  if cb.isEmpty then
    throw "a spread's operand must have a type of plain objects, null, undefined, Booleans, numbers, bigints or symbols"
  let mut labels : List Nat := []
  for c in ca do
    for d in cb do
      let some r := ObjectMerge.mergeResult drop c d
        | throw "a spread copies the own enumerable properties of a plain object; one of a string, an array, a function or a class value is outside the fragment"
      labels := labels ++ [← lower (SourceTypes.use r)]
  modify fun s => {s with hints := labels ++ s.hints}
  return labels.eraseDups

/-- A saved read is usable only in a subtree with no possible heap effects or
escaping closure. Reads are plain modeled cells, never JavaScript accessors. -/
private partial def readOnly : Fragment.Expr → Bool
  | .var .. | .lit .. | .done .. => true
  | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e | .atEnv _ e => readOnly e
  | .throwBody .. => false
  | .equality _ _ a b | .singletonTest _ _ _ _ a b | .logical _ _ a b | .coalesce _ a b
  | .optional _ _ a b | .seqBody _ a b | .letBody _ _ _ a b | .index _ _ a b | .arith _ _ a b | .elemAt _ a b
  | .comma _ a b | .inKeys _ a b => readOnly a && readOnly b
  | .ifBody _ _ c t e => readOnly c && readOnly t && readOnly e
  | .destructBody _ t a b => readOnly a && t.defaults.all readOnly && readOnly b
  | .alloc .. | .build .. | .write .. | .indexWrite .. | .update .. | .logicalAssign .. | .assign .. | .arrayLit .. | .elemWrite .. | .arrayAssign .. | .nullishAssign .. | .lambda .. | .withValue .. | .bindWithReceiver ..
  | .callWithReceiver .. | .applyWithReceiver .. | .call .. | .invoke .. | .ctor .. | .construct .. | .block .. => false

/-- The other operand of a singleton comparison, when saving the tested read
before it changes nothing: a literal, a name, or one field read. Each is
effect-free, so the two operands' values are the same in either order. The
singleton itself comes from the operand's claimed type, which its expression
obligation must establish; a call or a write could change the tested cell. -/
private def pureOperand : Fragment.Expr → Bool
  | .lit .. | .var .. | .read _ _ (.var ..) => true
  | _ => false

/-- Save the plain read in a singleton comparison. The other operand is
effect-free; moving it across the read has no effect. -/
private def readGuard (scope : List ScopeBinding) :
    Fragment.Expr → Option (String × Fragment.Expr × Fragment.Expr)
  | .not pos e => (readGuard scope e).map fun (snapshot,r,c) => (snapshot,r,.not pos c)
  | .singletonTest pos tag equal testLeft left right => do
    let (r,lit) := if testLeft then (left,right) else (right,left)
    guard (pureOperand lit)
    let snapshot ← match r with
      | .read _ fld (.var _ name) => do
        let _ ← resolve scope name
        readSnapshot name fld
      | .var _ name => match resolve scope name with
        | some (_, .cell ..) => some (localSnapshotName name)
        | _ => none
      | _ => none
    let saved := Fragment.Expr.var r.span snapshot
    some (snapshot,r,.singletonTest pos tag equal testLeft
      (if testLeft then saved else lit) (if testLeft then lit else saved))
  | _ => none

/-- Statement claims name source bindings only. Preserve anonymous evaluation
slots at their already checked types while projecting the supplied named slots. -/
private def closureEnv (fc : SourceClaims.Function) (pos : Nat) (scope : List ScopeBinding)
    (Γ : List (Ty Nat)) : Compiler (List (Ty Nat)) := do
  -- The closure's environment keeps each captured binding's storage: a
  -- captured mutable local is the cell's identity, and rebuilding it from its
  -- name would type the slot by what the cell currently holds.
  -- A receiver slot is immutable and bound by the call, so it keeps its
  -- checked type like an anonymous slot; no statement claim names `this`.
  let captured := scope.filter (fun b => b.source.name != "" && b.source.name != "this" &&
    !isSnapshot b.source.name)
  let named := captured.map (·.source.name)
  let H ← env fc pos (captured.map fun b => { b with source := ⟨b.source.name,none⟩ })
  for (b,A) in captured.zip H do
    let name := b.source.name
    if let .cell _ reference := b.storage then
      let some candidate := ((fc.envs.lookup pos).getD []).lookup name
        | throw s!"missing claimed binding '{name}' at {pos}"
      let R ← SourceClaims.resolve (← table).length candidate
      observed scope Γ (localSnapshotName name) b.source (pos,pos+1) reference valueField R
    if let some asserted := ((fc.entryCurrent.lookup pos).getD []).lookup name then
      for (fld, R) in asserted do
        let receiver := match b.storage with
          | .value => A | .cell contract _ => contract
        observed scope Γ (snapshotName name (← stringKey fld)) ⟨name,none⟩ (pos,pos+1) receiver fld R
  (scope.zipIdx).mapM fun (b,i) => do
    let name := b.source.name
    let A := if name == "" || name == "this" || isSnapshot name then Γ[i]? else H[named.idxOf name]?
    match A with
    | some A => pure A
    | none => throw "internal closure slot mismatch"

/-- Negations of an immutable variable retain its identity and reverse the
branch polarity. Arbitrary expressions deliberately carry no alias refinement. -/
private def conditionVariable (scope : List ScopeBinding) : Fragment.Expr → Option (Nat × Bool)
  | .var _ name => (valueSlot scope name).map (·, false)
  | .not _ e => (conditionVariable scope e).map fun (i, reversed) => (i, !reversed)
  | _ => none

/-- Only a syntactic immutable variable retains an alias to the observed value.
Reads and calls deliberately do not qualify, even if their types look stable. -/
private def tagConditionVariable (scope : List ScopeBinding) : Fragment.Expr → Option (Nat × Tag × Bool)
  | .not _ e => (tagConditionVariable scope e).map fun (i, tag, equal) => (i, tag, !equal)
  | .shapeTest _ tag equal (.var _ name) =>
    (valueSlot scope name).map (·, tag, equal)
  | .singletonTest _ tag equal testLeft left right =>
    match (if testLeft then left else right) with
    | .var _ name => (valueSlot scope name).map (·, tag, equal)
    | _ => none
  | _ => none

/-- The tag a condition tests on an immutable variable: its own shape or
singleton test, or, for a variable that is not a Boolean, its truthiness
(`ToBoolean`), which is how JavaScript reads any other value as a condition. -/
private def conditionTag (G : PositiveGraphs.NormalGraph Nat) (scope : List ScopeBinding)
    (Γ : List (Ty Nat)) : Fragment.Expr → Option (Nat × Tag × Bool)
  | .not _ e => (conditionTag G scope Γ e).map fun (i, tag, equal) => (i, tag, !equal)
  | .var _ name => do
    let i ← valueSlot scope name
    let A ← Γ[i]?
    if BranchRefinement.onlyBoolean G A then none else some (i, .truthy, true)
  | e => tagConditionVariable scope e

private def tagTestTerm (tag : Tag) (equal : Bool) (slot : Nat) : Tm :=
  .ite (.test tag (.var slot)) (if equal then .tru else .fls) (if equal then .fls else .tru)

/-- Split an explicit union and require a known test outcome for each arm.
A broad numeric arm is not silently treated as unequal to the singleton. -/
private def tagTestPlan (G : PositiveGraphs.NormalGraph Nat) (tag : Tag) (Γ : List (Ty Nat)) (slot : Nat)
    (equal : Bool) (A : Ty Nat) : Except String DirectProof.Plan := do
  let some C := Γ[slot]? | throw "internal tag-test slot mismatch"
  let term := tagTestTerm tag equal slot
  let children ← C.mapM fun a => do
    let H := Γ.set slot [a]
    let q := decide (Answers G [a] tag true)
    let value := if q == equal then Tm.tru else .fls
    let B := if q == equal then [1] else [2]
    let rule := if q == equal then ProgramCertificates.Rule.truLit else .flsLit
    if !q && !(decide (Answers G [a] tag false)) then
      -- An arm whose answer its type leaves open (a number against a numeric
      -- singleton, an open record for a key, an unknown shape) is a real
      -- Boolean: the test's own value.
      let test := DirectProof.node H (.test tag (.var slot)) [1,2] .test [DirectProof.var H slot [a]]
      let yes := DirectProof.cast H A (DirectProof.node H (if equal then .tru else .fls) (if equal then [1] else [2])
        (if equal then .truLit else .flsLit))
      let no := DirectProof.cast H A (DirectProof.node H (if equal then .fls else .tru) (if equal then [2] else [1])
        (if equal then .flsLit else .truLit))
      return DirectProof.node H term A .ifBool [test, yes, no]
    pure (DirectProof.node H term A (if q then .ifTrue else .ifFalse)
      [DirectProof.cast H A (DirectProof.node H value B rule)])
  pure (DirectProof.node Γ term A (.unionVar slot) children)

/-- `ite (test tag x) yes no` on the value in `slot`, split by its labels: a
label the tag answers selects its arm, and a mixed label (a number's
truthiness, or an unknown one) needs a real Boolean branch, where both arms
must establish `B`. `??`, a default parameter and `&&`/`||` are this shape, on
the nullish, `undefined` and truthiness tags. -/
private def selectPlan (G : PositiveGraphs.NormalGraph Nat) (Γ : List (Ty Nat))
    (slot : Nat) (B : Ty Nat) (tag : Tag) (yes no : DirectProof.Plan) :
    Except String DirectProof.Plan := do
  let some C := Γ[slot]? | throw "internal selection slot mismatch"
  let term := Tm.ite (.test tag (.var slot)) yes.term no.term
  let children := C.map fun label =>
    let L := Γ.set slot [label]
    let q := decide (Answers G [label] tag true)
    if q || decide (Answers G [label] tag false) then
      DirectProof.node L term B (if q then .ifTrue else .ifFalse)
        [DirectProof.cast L B (if q then yes else no)]
    else
      let test := DirectProof.node L (.test tag (.var slot)) [1,2] .test
        [DirectProof.var L slot [label]]
      DirectProof.node L term B .ifBool [test, DirectProof.cast L B yes, DirectProof.cast L B no]
  pure (DirectProof.node Γ term B (.unionVar slot) children)

/-- A defaulted parameter's slot holds its declared type or `undefined`: the
value a call that omits the position binds there. This is the replacement the
body sees, and it is the same shape as `??`, on the `undefined` tag alone. -/
private def defaultValuePlan (G : PositiveGraphs.NormalGraph Nat) (Γ : List (Ty Nat))
    (slot : Nat) (B : Ty Nat) (d : DirectProof.Plan) : Except String DirectProof.Plan :=
  selectPlan G Γ slot B .isUndef d (DirectProof.var Γ slot B)

/-- Shared conditional proof construction for statement branches, ternaries and
short-circuit operators. Branch builders retain their own source claims; a
logical operator's constant arm is administrative and needs no invented claim. -/
private def conditionalPlan (scope : List ScopeBinding) (H : List (Ty Nat)) (A : Ty Nat)
    (cond : Fragment.Expr) (c : DirectProof.Plan)
    (yesBranch noBranch : List ScopeBinding → List (Ty Nat) → Compiler DirectProof.Plan) :
    Compiler DirectProof.Plan := do
  let G := SourceTypes.graph (← table)
  -- A tested variable's slot, past the saved condition; or, for a condition
  -- that is not a Boolean, the saved value itself, tested for truthiness.
  let tagged : Option (Nat × Tag × Bool) := match conditionTag G scope H cond with
    | some (i, tag, equal) => some (i+1, tag, equal)
    | none => if BranchRefinement.onlyBoolean G c.type then none else some (0, .truthy, true)
  if let some (tested, tag, equal) := tagged then
    -- Preserve the evaluated predicate and its claims in an anonymous slot.
    let K := c.type :: H
    let some C := K[tested]? | throw "internal closure tag-guard slot mismatch"
    let T := K.set tested (BranchRefinement.tagSlice G C tag true)
    let F := K.set tested (BranchRefinement.tagSlice G C tag false)
    let t ← yesBranch (held ⟨"",some cond.span⟩ :: scope) (if equal then T else F)
    let e ← noBranch (held ⟨"",some cond.span⟩ :: scope) (if equal then F else T)
    let yes := if equal then t else e
    let no := if equal then e else t
    pure (DirectProof.letE H c (← selectPlan G K tested A tag yes no))
  else
    -- A variable already known `true` or `false` keeps its singleton: the
    -- condition's type selects the reachable arm (`ifKnown`).
    match (conditionVariable scope cond).filter fun (i, _) => H[i]? != some [1] && H[i]? != some [2] with
    | some (i, reversed) =>
      let T := H.set i [1]
      let F := H.set i [2]
      let t ← yesBranch scope (if reversed then F else T)
      let e ← noBranch scope (if reversed then T else F)
      let yes := if reversed then e else t
      let no := if reversed then t else e
      pure (DirectProof.node H (.ite (.var i) yes.term no.term) A (.ifBoolVar [1] [2])
        [DirectProof.cast T A yes,DirectProof.cast F A no])
    | none =>
      let t ← yesBranch scope H
      let e ← noBranch scope H
      pure (DirectProof.ifE G H A c t e)

/-- The scope an operand saved in a fresh slot 0 extends. A named immutable
operand is identical to the saved value: its name moves to that slot, so what
follows sees the refinement a test of the saved value establishes. No mutable
read is given an alias. -/
private def savedOperandScope (scope : List ScopeBinding) (operand : Fragment.Expr) :
    List ScopeBinding :=
  match operand with
  | .var _ name =>
    if (valueSlot scope name).isSome then held ⟨name,some operand.span⟩ ::
      scope.map (fun b => if b.source.name == name then held ⟨"",some operand.span⟩ else b)
    else held ⟨"",some operand.span⟩ :: scope
  | _ => held ⟨"",some operand.span⟩ :: scope

/-- Label 3 is `undefined`: see `SourceTypes.initial`. A position a call may
omit is one whose declared contract admits that value, because `undefined` is
what the machine binds there. -/
private def admitsUndefined (G : PositiveGraphs.NormalGraph Nat) (A : Ty Nat) : Bool :=
  (PositiveRules.expand G A).any fun
    | .undef | .top => true
    | _ => false

/-- Select a signature these actuals can call: one declaring exactly the
arguments written, or a longer one whose remaining positions admit `undefined`.
An exact signature is preferred, then one covering every actual type. No actual
is invented for an omitted position; the call term keeps the arguments the
source writes. -/
private def selectSignature (G : PositiveGraphs.NormalGraph Nat) (L : PositiveRules.Ops Nat) (As : List (Ty Nat))
    (Rr : Ty Nat := [3]) :
    Except String (Ty Nat × List (Ty Nat) × Ty Nat) := do
  let covers (p : Ty Nat × List (Ty Nat) × Ty Nat) :=
    (As.zip p.2.1).all fun (A,D) => A.all D.contains
  -- Instances of one scheme may differ only in their receiver: prefer the
  -- signature naming the receiver passed.
  let receives (p : Ty Nat × List (Ty Nat) × Ty Nat) := Rr.all p.1.contains
  let pick (choices : List (Ty Nat × List (Ty Nat) × Ty Nat)) :=
    (choices.find? fun p => covers p && receives p) <|> (choices.find? covers) <|> choices.head?
  let exact := L.filter fun p => p.2.1.length == As.length
  let short := L.filter fun p =>
    As.length < p.2.1.length && (p.2.1.drop As.length).all (admitsUndefined G)
  let some p := pick exact <|> pick short
    | throw "callee has no signature with the actual argument count"
  return p

/-- A list `.apply` reads no element of: every member null or undefined. -/
private def nullishList (G : PositiveGraphs.NormalGraph Nat) (T : Ty Nat) : Bool :=
  !T.isEmpty && (PositiveRules.expand G T).all fun
    | .nul | .undef => true
    | _ => false

/-- A plain call passes `undefined` as its receiver: the premise proves it at
the selected signature's receiver contract. -/
private def plainReceiver (Γ : List (Ty Nat)) (Rt : Ty Nat) : DirectProof.Plan :=
  DirectProof.cast Γ Rt (DirectProof.node Γ .undef [3] .undef)

/-- One premise per position the selected signature declares and the call
omits, each proving `undefined` at that position's contract. -/
private def omittedPremises (Γ : List (Ty Nat)) (Ds : List (Ty Nat)) (supplied : Nat) :
    List DirectProof.Plan :=
  (Ds.drop supplied).map fun D =>
    DirectProof.cast Γ D (DirectProof.node Γ .undef [3] .undef)

/-- Nest saved operand plans in their original evaluation order. -/
private def saveOperands (ps : List DirectProof.Plan) (body : DirectProof.Plan) : DirectProof.Plan :=
  ps.foldr (fun p b => DirectProof.letE p.goal.context p b) body

private def creationChildren : DirectProof.Plan → Option (List DirectProof.Plan)
  | .cast _ p => creationChildren p
  | .rule _ .funE ps => some ps
  | _ => none
/-- A variadic creation: its own type, the rest-array types, and the bodies. -/
private def restCreation : DirectProof.Plan → Option (Ty Nat × List (Ty Nat) × List DirectProof.Plan)
  | .cast _ p => restCreation p
  | .rule j (.funRest As) ps => some (j.type, As, ps)
  | _ => none
private def allocationChildren : DirectProof.Plan → Option (List DirectProof.Plan)
  | .cast _ p => allocationChildren p
  | .rule _ .alloc ps => some ps
  | _ => none

/-- A method call's head: a host-relative member is read from the object in a
slot and bound to that same object (`bindMember`), before any actual runs; any
other member is read as a field. -/
def memberHead (G : PositiveGraphs.NormalGraph Nat) (O : Ty Nat) (fld : PropKey) (obj : Tm) : Tm :=
  match obj, (ProgramTyping.memberOf G O fld).isSome with
  | .var i, true => .letE (.readAt fld (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])
  | _, _ => .readAt fld obj

/-- The row a field read gives before any claim replaces it: the object's own
field or view, or, for a key an own-key bound does not admit, its prototype's, as
`readCell` and the top level's search read it. -/
private def fieldRow (G : PositiveGraphs.NormalGraph Nat) (O : Ty Nat) (fld : PropKey) :
    Option (Ty Nat) :=
  match PositiveRules.expand G O with
  | [.refs fs [] vs _ _ ks] => fs.lookup fld <|> vs.lookup fld <|> do
      if !ks.any (fun K => !K.admits fld) then none
      let P ← (fs ++ vs).lookup SourceTypes.protoField
      let [.refs gs [] ws _ _ _] := PositiveRules.expand G P | none
      (gs ++ ws).lookup fld
  | [.callable fs _ _ _] => fs.lookup fld
  | _ => none

/-- A method call's explicit type arguments, `o.m<A₁,…,Aₖ>(…)`, are a
requirement on the instance the call uses: the member read from `O` is a scheme
row, the claimed method type `M` is an instance of it by a checked instance map
(`checkInstArrs`), and that map sends the scheme's first `k` binders to types
of the same meaning as `A₁,…,Aₖ`. The binders past them are the ones the
call's receiver and actuals fix, as for a call without type arguments. The
check only refuses: acceptance still rests on the read's own `inst` proof and
the call's typing. -/
private def explicitInstance (pos : Span) (O M : Ty Nat) (fld : PropKey) (typeArgs : List Json) :
    Compiler Unit := do
  if typeArgs.isEmpty then return
  let args ← typeArgs.mapM fun t => lower (Fragment.translate t)
  let T ← table
  let G := SourceTypes.graph T
  let refuse (reason : String) := locatedRefusal T pos .schemeElimination reason
  let some S := fieldRow G O fld
    | throw (refuse s!"explicit type arguments name no member '{fld}' of the receiver")
  let [i] := S | throw (refuse "explicit type arguments need a generic member")
  let some s := G.schemes i | throw (refuse "explicit type arguments need a generic member")
  if args.length > s.binders.length then
    throw (refuse "more explicit type arguments than the member has binders")
  let [.arrs L Ms] := PositiveRules.expand G M
    | throw (refuse "the call's claimed method is not an instance of its member")
  let some c := CertificateProducer.instanceFor G 64 s L Ms
    | throw (refuse "the call's claimed method is not an instance of its member")
  if !PositiveCertificates.checkInstArrs G S L Ms c then
    throw (refuse "the call's claimed method is not an instance of its member")
  for (A, θ) in args.zip c.instances do
    if !sameMeaning T A θ then
      throw (refuse "the call's instance is not the one its explicit type arguments state")

/-- A plan at a meet row, a bounded binder read as its row met with its bound,
cast to the bound: the row holding exactly the meet's clauses, which the meet
is below (`PositiveRules.meetSources`). A member read through the binder reads
the bound's member. Any other plan is itself. -/
private def throughBound (Γ : List (Ty Nat)) (a : DirectProof.Plan) : Compiler DirectProof.Plan := do
  let T ← table
  let [l] := a.type | return a
  let some (.meet _ cs) := (T[l]? : Option RequestJson.Row) | return a
  let row := RequestJson.Row.clauses cs
  let m ← match T.idxOf? row with
    | some m => pure m
    | none => do
      modify fun s => { s with types := s.types ++ [row] }
      pure T.length
  modify fun s => { s with hints := m :: s.hints }
  return DirectProof.cast Γ [m] a

/-- Read a field from a cell plan under context `Γ`: one contract, a callable
bag, or an explicit union of cell contracts each naming the field. -/
private partial def readCell (G : PositiveGraphs.NormalGraph Nat) (Γ : List (Ty Nat)) (fld : PropKey)
    (a : DirectProof.Plan) : Compiler DirectProof.Plan := do
  match PositiveRules.expand G a.type with
  | [.refs fs [] vs os _ ks] =>
    -- An invariant field reads at its contract; a readonly view at its bound;
    -- an optional field at its type or `undefined` (`readOptional`); a key a
    -- bound of the object does not admit at its prototype's field or view
    -- (`readProto`), as at the top level.
    match fs.lookup fld, vs.lookup fld, (os.find? (·.key == fld)).map (·.type) with
    | some B, _, _ => pure (DirectProof.node Γ (.readAt fld a.term) B .read [a])
    | none, some B, _ => pure (DirectProof.node Γ (.readAt fld a.term) B .readView [a])
    | none, none, some E => pure (DirectProof.node Γ (.readAt fld a.term) (E ++ [3]) (.readOptional E [3]) [a])
    | none, none, none =>
      let inherited : Option (Ty Nat × Ty Nat) := do
        if !ks.any (fun K => !K.admits fld) then none
        let P ← (fs ++ vs).lookup SourceTypes.protoField
        let [.refs gs [] ws _ _ _] := PositiveRules.expand G P | none
        let B ← (gs ++ ws).lookup fld
        pure (P, B)
      let some (P, B) := inherited | throw s!"read of a field '{fld}' the contract does not name"
      pure (DirectProof.node Γ (.readAt fld a.term) B (.readProto P) [a])
  | [.dict fs [] vs ix [] [] [] _] =>
    -- A named field or view, else an index whose class surely admits the
    -- key, which may miss.
    match fs.lookup fld, vs.lookup fld with
    | some B, _ => pure (DirectProof.node Γ (.readAt fld a.term) B .read [a])
    | none, some B => pure (DirectProof.node Γ (.readAt fld a.term) B .readView [a])
    | none, none =>
      let some (K, B) := (PositiveNormalization.numericFirst ix).find? (fun (K, _) => K.surely fld)
        | throw s!"read of a key '{fld}' no index of the object constrains"
      pure (DirectProof.node Γ (.readAt fld a.term) (B ++ [3]) (.readDict K B [3]) [a])
  | [.callable fs _ _ _] =>
    let some B := fs.lookup fld | throw s!"read of a field '{fld}' the contract does not name"
    pure (DirectProof.node Γ (.readAt fld a.term) B .readCallable [a])
  | _ =>
    -- A union reads each alternative as that alternative reads, at the
    -- union of what they read.
    if a.type.length ≤ 1 then throw "read receiver must name a cell contract"
    let alternatives ← a.type.mapM fun label => do
      let H := [label] :: Γ
      pure (label, ← readCell G H fld (DirectProof.var H 0 [label]))
    let R := (alternatives.flatMap (·.2.type)).eraseDups
    let children := alternatives.map fun (label,plan) =>
      DirectProof.cast ([label] :: Γ) R plan
    pure (DirectProof.letE Γ a (DirectProof.node (a.type::Γ)
      (.readAt fld (.var 0)) R (.unionVar 0) children))

/-- How a member read reaches a primitive of one shape: a string's own
`length`, or the member of its wrapper's prototype, held in slot `proto` at
`P`, through a fresh wrapper of type `R` owning only its `[[proto]]` key. -/
private inductive PrimitiveArm where
  | length
  | proto (proto : Nat) (P R : Ty Nat)

/-- The shapes a member read of `O` dispatches on: each primitive shape among
`O`'s clauses, with the arm that reads it (`ToObject`'s wrapper, whose
prototype is the realm's). An object shape needs none. -/
private def primitiveArms (scope : List ScopeBinding) (K : List (Ty Nat)) (O : Ty Nat)
    (fld : PropKey) : Compiler (List (Tag × PrimitiveArm)) := do
  let G := SourceTypes.graph (← table)
  let shapeOf (c : PositiveNormalization.Clause (Ty Nat)) : Option Tag := match c with
    | .str | .strLit _ => some .isStr
    | .num | .numLit _ => some .isNum
    | .bigint | .bigintLit _ => some .isBigint
    | .bool | .boolLit _ => some .isBool
    | _ => none
  let shapes := SourceTypes.primitivePrototypes.filter fun (tag, _) =>
    (PositiveRules.expand G O).any (shapeOf · == some tag)
  shapes.mapM fun (tag, name) => do
    if tag == .isStr && fld == "length" then return (tag, .length)
    let some (p, .value) := resolve scope name
      | throw s!"a member of a primitive is read from {name}, which this unit does not see"
    let some P := K[p]? | throw "internal prototype slot mismatch"
    let R ← lower (SourceTypes.use (.refs [(SourceTypes.protoField, P)] [] [] [] []
      [⟨true, [SourceTypes.protoField]⟩]))
    modify fun s => {s with hints := R :: s.hints}
    return (tag, .proto p P [R])

/-- One arm's read of slot `o`. -/
private def PrimitiveArm.term (fld : PropKey) (o : Nat) : PrimitiveArm → Tm
  | .length => .lenOf (.var o)
  | .proto p _ _ => .readAt fld (.makeAt .absent [SourceTypes.protoField] [.var p])

/-- `x.k` with `x` in slot `o` of a type with primitive shapes: a test of each
shape selecting its arm, then the object read. Each arm is JavaScript's read
for values of its shape, and the object read is its read for an object; a
value of a shape no arm names reaches the object read, where a primitive is
stuck, never misread. -/
private def dispatchTerm (arms : List (Tag × PrimitiveArm)) (fld : PropKey) (o : Nat) (object : Tm) : Tm :=
  arms.foldr (fun (tag, arm) rest => .ite (.test tag (.var o)) (arm.term fld o) rest) object

/-- `x.k(a…)` with `x` in slot `o` of a union type and the actuals `args`
already evaluated: per shape of `x`, as `dispatchTerm` reads it, the member
that shape reads, invoked with `x` as its receiver. An object's member is
bound to it (`memberHead`) where every object alternative holds `k` as a
member, and read as a field otherwise. -/
private def dispatchCallTerm (G : PositiveGraphs.NormalGraph Nat) (O : Ty Nat)
    (arms : List (Tag × PrimitiveArm)) (fld : PropKey) (o : Nat) (args : List Tm) : Tm :=
  let objects := O.filter fun l => arms.all fun (tag, _) => !decide (Answers G [l] tag true)
  let member := !objects.isEmpty &&
    objects.all fun l => (ProgramTyping.memberOf G [l] fld).isSome
  let object := if member
    then Tm.letE (.readAt fld (.var o)) (.makeAt (.bound (.var 0) (.var (o + 1)) []) [] [])
    else .readAt fld (.var o)
  arms.foldr (fun (tag, arm) rest =>
    .ite (.test tag (.var o)) (.invoke (arm.term fld o) (.var o) args) rest)
    (.invoke object (.var o) args)

/-- The member read of slot `o` of `K` at `A`, planned per label of the slot:
a primitive's label selects its arm by its known shape answers, and any other
is read as an object (`readCell`). -/
private def memberReadPlan (G : PositiveGraphs.NormalGraph Nat) (K : List (Ty Nat)) (o : Nat)
    (fld : PropKey) (A : Ty Nat) (arms : List (Tag × PrimitiveArm)) : Compiler DirectProof.Plan := do
  let some O := K[o]? | throw "internal member receiver slot mismatch"
  let N : Ty Nat := [← lower (SourceTypes.use .num)]
  let armPlan (L : List (Ty Nat)) (label : Nat) : PrimitiveArm → Except String DirectProof.Plan
    | .length => pure (DirectProof.node L (.lenOf (.var o)) N .lenStr [DirectProof.var L o [label]])
    | .proto p P R => do
      let [.refs gs [] ws _ _ _] := PositiveRules.expand G P
        | throw "a primitive's prototype contract must be a record"
      let some B := (gs ++ ws).lookup fld
        | throw s!"read of a member '{fld}' the primitive's prototype contract does not name"
      let wrapper := DirectProof.node L (.makeAt .absent [SourceTypes.protoField] [.var p]) R .alloc
        [DirectProof.var L p P]
      pure (DirectProof.node L (.readAt fld wrapper.term) B (.readProto P) [wrapper])
  let object := Tm.readAt fld (.var o)
  let rec chain (L : List (Ty Nat)) (label : Nat) :
      List (Tag × PrimitiveArm) → Compiler DirectProof.Plan
    | [] => do return DirectProof.cast L A (← readCell G L fld (DirectProof.var L o [label]))
    | (tag, arm) :: rest => do
      let term := dispatchTerm ((tag, arm) :: rest) fld o object
      if decide (Answers G [label] tag true) then
        return DirectProof.node L term A .ifTrue [DirectProof.cast L A (← armPlan L label arm)]
      else if decide (Answers G [label] tag false) then
        return DirectProof.node L term A .ifFalse [← chain L label rest]
      else throw "a member read's receiver needs labels of one shape each"
  let children ← O.mapM fun label => chain (K.set o [label]) label arms
  return DirectProof.node K (dispatchTerm arms fld o object) A (.unionVar o) children

/-- The write node under context `H`, with the value in slot 0 and the
receiver, claimed at `B`, in slot `ri`. -/
private def writeCell (G : PositiveGraphs.NormalGraph Nat) (H : List (Ty Nat)) (fld : PropKey)
    (B C : Ty Nat) (ri : Nat) : Compiler DirectProof.Plan := do
  let term := Tm.writeAt fld (.var ri) (.var 0)
  match PositiveRules.expand G B with
  | [.refs fs [] vs [] _ _] =>
    let some D := fs.lookup fld
      | throw (if (vs.lookup fld).isSome then s!"write to a readonly field '{fld}'"
          else s!"write to a field '{fld}' the contract does not name")
    pure (DirectProof.node H term [0] .write
      [DirectProof.var H ri B,DirectProof.cast H D (DirectProof.var H 0 C)])
  | _ =>
    if B.length ≤ 1 then throw "write receiver must name a cell contract"
    let alternatives ← B.mapM fun label => do
      let [.refs fs [] [] [] _ _] := PositiveRules.expand G [label]
        | throw "every write alternative must name a cell contract"
      let some D := fs.lookup fld
        | throw s!"write to a field '{fld}' an alternative does not name"
      pure (label,D)
    let children := alternatives.map fun (label,D) =>
      let branch := H.set ri [label]
      DirectProof.node branch term [0] .write
        [DirectProof.var branch ri [label],DirectProof.cast branch D (DirectProof.var branch 0 C)]
    pure (DirectProof.node H term [0] (.unionVar ri) children)

/-- The element at literal index `b` of the array `r` reads under `H`, from
its store: a required position at its type, an optional or rest position at
its type or `undefined`. -/
private def elemReadPlan (G : PositiveGraphs.NormalGraph Nat) (H : List (Ty Nat))
    (r : DirectProof.Plan) (b : UInt64) : Compiler DirectProof.Plan := do
  let I : Ty Nat := [← lower (SourceTypes.use (.numLit b))]
  let store ← readCell G H SourceTypes.storeField r
  let [.list T []] := PositiveRules.expand G store.type | throw "an element read needs an array"
  let U : Ty Nat := [3]
  let (E, rule) ← match ProgramCertificates.requiredAt T b, ProgramCertificates.optionalAt T b U with
    | some E, _ => pure (E, ProgramCertificates.Rule.elem)
    | none, some E => pure (E, .elemOpt U)
    | none, none => throw "an element read at an index no contract names"
  pure (DirectProof.node H (.elemAt store.term (.num b)) E rule [store, DirectProof.node H (.num b) I .numLit])


/-- Leaving a block drops its local slots simultaneously. Active-name shadowing
is gated until the export can identify hidden bindings independently. With no
continuation the body completes rather than returns, producing `undefined`; that
is emitted as an exit claiming the declared result, attributed to the function
because an empty body has no statement to point at. -/
private def leave (pos : Span) (R : Ty Nat) (scope : List ScopeBinding)
    (tail : Option (Target × List ScopeBinding)) : Compiler Target := do
  match tail with
  | none =>
    let exit ← emitAt pos .undef .ret [] R "completion"
    return ⟨exit.label, some []⟩
  | some (target, outer) =>
    -- A binding is found by its descriptor first: a parameter may hide a
    -- module constant of its name, and the constant's slot is its own.
    let slots ← outer.mapM fun b =>
      match (sources scope).idxOf? b.source, (names scope).idxOf? b.source.name with
      | some i, _ | none, some i => pure i
      | none, none => throw s!"internal extraction error: lost outer binding '{b.source.name}'"
    return ⟨target.label, some slots⟩

/-- Branch binding pushes the actual tested value. For a source variable test,
map that variable to the pushed value (the same immutable value), exposing its
proved singleton refinement. Other slots retain their ordinary identities. -/
private def branchMapping (width : Nat) (tested : Option Nat) (target : Target) : Target :=
  ⟨target.label, some ((target.mapping.getD (List.range width)).map fun i =>
    if tested == some i then 0 else i+1)⟩

/-- Keep a pre-existing singleton fact rather than replacing it with the
branch witness. In particular, an impossible opposite edge must not force a
contradictory replacement of an otherwise valid immutable binding. -/
private def testedSlot (scope : List ScopeBinding) (Γ : List (Ty Nat)) (cond : Fragment.Expr) : Option Nat :=
  do
    let (i, _) ← conditionVariable scope cond
    if Γ[i]? == some [1] || Γ[i]? == some [2] then none else some i

/-- Share polarity handling between conditionals and loop heads. The saved
condition is in slot zero. Only a syntactically identified immutable variable
may be replaced by the recovered Boolean witness. -/
private def emitBranch (scope : List ScopeBinding) (Γ : List (Ty Nat)) (cond : Fragment.Expr)
    (A : Ty Nat) (yes no : Target) : Compiler Target := do
  let G := SourceTypes.graph (← table)
  if let some (i, tag, equal) := conditionTag G scope Γ cond then
    let some C := Γ[i]? | throw "internal tag-guard slot mismatch"
    let adapt := fun t =>
      let mapped := branchMapping scope.length (some i) t
      ⟨mapped.label, some ((mapped.mapping.getD []).map
        (fun j => if j == 0 then 0 else j+1))⟩
    -- The source predicate has already run and all operand claims were checked.
    -- Reading the same immutable variable observes its tag without repeating
    -- any source expression or trusting the saved Boolean's annotation.
    return ← emitAt cond.span (.var (i+1))
      (.tagBind tag (adapt (if equal then yes else no)) (adapt (if equal then no else yes)))
      (A::Γ) C "tag-dispatch" (scope := held ⟨"",some cond.span⟩ :: scope)
  let tested := testedSlot scope Γ cond
  -- Branch on the saved value; the edge maps discard its older copy and
  -- retain the new refinement slot supplied by branchBind.
  let adapt := fun t =>
    let mapped := branchMapping scope.length tested t
    ⟨mapped.label, some ((mapped.mapping.getD []).map
      (fun i => if i == 0 then 0 else i+1))⟩
  -- Negation is handled by swapping successors in compileCondition, so this
  -- dispatch always observes the saved operand itself, retaining its read link.
  -- A value that is not a Boolean is a condition by its truthiness.
  let transfer := if BranchRefinement.onlyBoolean G A then Continuation.branchBind (adapt yes) (adapt no)
    else .tagBind .truthy (adapt yes) (adapt no)
  emitAt cond.span (.var 0) transfer (A::Γ) A
    (scope := held ⟨"",some cond.span⟩ :: scope)

/-- Facts justified on the path to a short-circuit operand. Only immutable
source bindings are refined; every generated edge checks this candidate context.
A true conjunction / false disjunction establishes both operand outcomes. The
other outcomes deliberately retain the input context rather than compute a join. -/
private def conditionContext (G : PositiveGraphs.NormalGraph Nat) (scope : List ScopeBinding) (Γ : List (Ty Nat))
    (cond : Fragment.Expr) (answer : Bool) : List (Ty Nat) :=
  match cond with
  | .not _ e => conditionContext G scope Γ e (!answer)
  | .logical _ andOp left right =>
    if answer == andOp then
      conditionContext G scope (conditionContext G scope Γ left answer) right answer
    else Γ
  | _ =>
    if let some (i, tag, equal) := conditionTag G scope Γ cond then
      Γ.set i (BranchRefinement.tagSlice G (Γ[i]?.getD []) tag (answer == equal))
    else if let some i := testedSlot scope Γ cond then
      Γ.set i (if answer then [1] else [2])
    else Γ

/-- The span of the first read of `name` an expression always evaluates,
before any branch or closure: its claim is what the name holds on entry to
the expression. -/
private partial def firstUse (name : String) : Fragment.Expr → Option Span
  | .var p n => if n == name then some p else none
  | .lit .. | .done .. | .lambda .. | .ctor .. => none
  | .ifBody _ _ c _ _ => firstUse name c
  | .logical _ _ a _ | .coalesce _ a _ | .optional _ _ a _ => firstUse name a
  | .shapeTest _ _ _ e | .not _ e | .unary _ _ e | .cast _ _ e | .read _ _ e | .atEnv _ e
  | .throwBody _ e => firstUse name e
  | .construct _ f args _ | .call _ f args _ _ | .invoke _ f args _ _ =>
    (f :: args).findSome? (firstUse name)
  | .alloc _ _ es | .arrayLit _ es => es.findSome? (firstUse name)
  | .equality _ _ a b | .singletonTest _ _ _ _ a b | .write _ _ a b | .index _ _ a b
  | .elemAt _ a b | .arith _ _ a b | .comma _ a b | .inKeys _ a b =>
    (firstUse name a).orElse fun _ => firstUse name b
  | _ => none

/-- A conditional's arm starts where the condition answered: each immutable
source binding the arm reads before any branch of its own holds what the
producer claims that read at, which the edge from the condition checks as it
checks a statement entry's claims (a slice by the test, a field slice, a
present key); the others, the condition's own refinement. A binding at a
scheme row keeps it: no test narrows a scheme, and a call reads it at the
instance it names, not the binding. -/
private def armContext (fc : SourceClaims.Function) (scope : List ScopeBinding)
    (Γ : List (Ty Nat)) (arm : Fragment.Expr) : Compiler (List (Ty Nat)) := do
  let G := SourceTypes.graph (← table)
  scope.zipIdx.foldlM (fun Δ (b,i) => do
    match b.storage, firstUse b.source.name arm with
    | .value, some p =>
      if b.source.name == "" || isSnapshot b.source.name then return Δ
      if (Γ[i]?.bind (ProgramCertificates.schemeOf G ·)).isSome then return Δ
      match fc.exprs.lookup p with
      | some _ => return Δ.set i (← claimAt fc p)
      | none => return Δ
    | _, _ => return Δ) Γ

/-- The fresh array an array pattern's rest collects from the array at slot
`obj` of `A`: the positions from `start` on, read into a store. They are a
fixed list of reads where `A` is one tuple of required positions, whose
length is exact (`listT`); an array of any other length has a slice of
unknown length for its rest, which no list of reads is. The array is claimed
at the rest's span, like an array literal. The store's term, the store's
type and the array's claimed type. -/
private def restArray (fc : SourceClaims.Function) (A : Ty Nat) (obj start : Nat) (restPos : Span) :
    Compiler (Tm × Ty Nat × Ty Nat) := do
  let G := SourceTypes.graph (← table)
  let some S := storeOf G A | throw "an array rest needs one array contract: over a union of arrays of different lengths its rest is a slice of a length known only at run time"
  let [.list T []] := PositiveRules.expand G S | throw restOfUnknownLength
  if !T.optional.isEmpty || T.rest.isSome then throw restOfUnknownLength
  let C ← claimAt fc restPos
  let some Sr := storeOf (SourceTypes.graph (← table)) C | throw "an array rest needs an array claim"
  let reads ← (List.range (T.required.length - start)).mapM fun j => do
    return Tm.elemAt (.readAt SourceTypes.storeField (.var obj)) (← indexTerm (start + j))
  let _ ← arrayObject Sr
  return (.arrLit reads, Sr, C)

/-- A slice rest's collection: the call of its `%RestFrom:k%`, `k` the
rest's index, on the array at slot `obj`, after the pattern's reads and
defaults (`Fragment.restFromName`). The array is claimed at the rest's span
with the call's instance. -/
private def sliceCall (scope : List ScopeBinding) (obj k : Nat) : Except String Tm := do
  let some (i, _) := resolve scope (Fragment.restFromName k)
    | throw "internal extraction error: a slice rest without its intrinsic"
  return Tm.call (.var i) [.var obj]

/-- What a literal position of an array reads, by the array's contract: a
required position reads at its type, an optional or rest position at its type
or `undefined`, and a position no contract names is refused. A union of
array contracts reads at the union of their positions. -/
private def positionRead (G : PositiveGraphs.NormalGraph Nat) (A : Ty Nat) (i : Nat) :
    Compiler (Ty Nat) := do
  -- The index is a literal of the read, typed at its singleton; the producer
  -- finds that singleton among the request's types.
  let label ← lower (SourceTypes.use (.numLit (bitsOfNat i)))
  modify fun s => { s with hints := label :: s.hints }
  let alts ← (PositiveRules.expand G A).mapM fun c => do
    let store ← match c with
      | .refs fs [] vs _ _ _ => match fs.lookup SourceTypes.storeField <|> vs.lookup SourceTypes.storeField with
        | some S => pure S
        | none => throw "an array pattern requires an array contract"
      | _ => throw "an array pattern requires an array contract"
    (PositiveRules.expand G store).mapM fun c => do
      let .list T [] := c | throw "an array pattern requires an array contract"
      match T.required[i]?, ProgramTyping.positionTy T i with
      | some E, _ => pure E
      | none, some E => pure (E ++ [3])
      | none, none => throw s!"position {i} is outside the array's contract"
  pure alts.flatten.flatten.eraseDups

/-- An operand of a split comparison: a slot, the field read from it, and
the source expression. -/
private abbrev SplitOperand := (Nat × Option PropKey) × Fragment.Expr

/-- A strict comparison of two operands neither of which is a singleton, both
read without effect (a name, or a field of a name), one of them claimed at a
union of singletons, dispatches as the tag tests it amounts to: the split
operand, the other operand, and the split operand's singletons. An immutable
name is split first, as before; otherwise a field read. -/
private def equalitySplit (fc : SourceClaims.Function) (scope : List ScopeBinding) (Γ : List (Ty Nat))
    (l r : Fragment.Expr) :
    Compiler (Option (SplitOperand × SplitOperand × List Tag)) := do
  let G := SourceTypes.graph (← table)
  let operand : Fragment.Expr → Option (Nat × Option PropKey)
    | .var _ name => (valueSlot scope name).map (·, none)
    | .read _ f (.var _ name) => (valueSlot scope name).map (·, some f)
    | _ => none
  let singletons := fun (C : Ty Nat) =>
    if C.isEmpty then none else C.mapM fun a => singletonTag G [a]
  let attempt := fun (s o : Fragment.Expr) (field : Bool) => do
    let some sop := operand s | return none
    let some oop := operand o | return none
    let C ← match sop with
      | (k, none) => if field then pure none else pure Γ[k]?
      | (_, some _) => if field then (some <$> exprType fc s) else pure none
    match C.bind singletons with
    | some tags => return some ((sop, s), (oop, o), tags)
    | none => return none
  for (s, o, field) in [(r, l, false), (l, r, false), (r, l, true), (l, r, true)] do
    if let some x ← attempt s o field then return some x
  return none

/-- A strict comparison of an immutable name with an operand that is not read
without effect (a call, say) claimed at a union of singletons: the operand is
evaluated once, into a slot of its own, and split there; the name, which no
effect changes, is the other operand. -/
private def savedSplit (fc : SourceClaims.Function) (scope : List ScopeBinding)
    (l r : Fragment.Expr) : Compiler (Option (Nat × Fragment.Expr × Fragment.Expr × List Tag)) := do
  let G := SourceTypes.graph (← table)
  let attempt := fun (n e : Fragment.Expr) => do
    let .var _ name := n | return none
    let some k := valueSlot scope name | return none
    match e with
    | .var .. | .lit .. | .read _ _ (.var ..) => return none
    | _ =>
      let C ← exprType fc e
      if C.isEmpty then return none
      match C.mapM fun a => singletonTag G [a] with
      | some tags => return some (k, n, e, tags)
      | none => return none
  if let some x ← attempt l r then return some x
  attempt r l


/-- Where `continue` and `break` go, with the lexical scope at each
destination: the nearest enclosing loop's next iteration and its end, if there
is a loop, and the end of each enclosing labeled block, innermost first. An
end is `none` where it is the function's. -/
private structure Finalizer where
  /-- The `finally` block, and the `try` it belongs to. -/
  stmts : List Fragment.Stmt
  pos : Span
  /-- The lexical context of the `try`, which the block runs in: its scope,
  handler and jump targets. -/
  scope : List ScopeBinding
  handler : Option (Target × Nat)
  loop : Option ((Target × List ScopeBinding) × Option (Target × List ScopeBinding))
  labels : List (String × Option (Target × List ScopeBinding))
  loopDepth : Nat
  labelDepths : List (String × Nat)

private structure LoopTargets where
  loop : Option ((Target × List ScopeBinding) × Option (Target × List ScopeBinding)) := none
  labels : List (String × Option (Target × List ScopeBinding)) := []
  /-- The `finally` blocks of the `try` statements around this point,
  innermost first: a `return` runs each of them before it returns. -/
  finalizers : List Finalizer := []
  /-- How many of those were around the nearest loop, and around each labeled
  block: a jump to one of them past a `finally` is refused. -/
  loopDepth : Nat := 0
  labelDepths : List (String × Nat) := []

/-- Whether a statement list never completes normally: it ends in a jump, a
`return` or a `throw`, or in a statement all of whose ways on do. An
unlabeled block is its statements; a labeled one may be left by a `break`. -/
private partial def abrupt (ss : List Fragment.Stmt) : Bool :=
  match ss.getLast? with
  | some (.ret ..) | some (.throw ..) | some (.brk ..) | some (.cont ..) => true
  | some (.ite _ _ t (some e)) => abrupt t && abrupt e
  | some (.block _ none b) => abrupt b
  | some (.tryStmt _ b h f) =>
    (f.map abrupt).getD false || (abrupt b && (h.map (abrupt ·.2)).getD true)
  | some (.closing _ _ b) => abrupt b
  | _ => false

/-- Entering a loop: its targets, behind as many `finally` blocks as now. -/
private def LoopTargets.enterLoop (t : LoopTargets)
    (l : (Target × List ScopeBinding) × Option (Target × List ScopeBinding)) : LoopTargets :=
  { t with loop := some l, loopDepth := t.finalizers.length }

/-- Entering a labeled block, likewise. -/
private def LoopTargets.enterLabel (t : LoopTargets) (label : String)
    (done : Option (Target × List ScopeBinding)) : LoopTargets :=
  { t with labels := (label, done) :: t.labels,
           labelDepths := (label, t.finalizers.length) :: t.labelDepths }

/-- Compile with `h` as the handler of every node emitted. -/
private def withHandler (h : Option (Target × Nat)) (act : Compiler α) : Compiler α := do
  let saved := (← get).handler
  modify fun s => { s with handler := h }
  let r ← act
  modify fun s => { s with handler := saved }
  return r

/-- A jump from `scope` to a target over `targetScope`: the target's slots,
read through its own mapping, found in `scope` by descriptor, else by name
(an anonymous slot has no name of its own to be found by). -/
private def jumpTo (scope : List ScopeBinding) (target : Target) (targetScope : List ScopeBinding) :
    Compiler Target := do
  let slots ← targetScope.mapM fun b =>
    match (sources scope).idxOf? b.source, (names scope).idxOf? b.source.name with
    | some i, _ | none, some i => pure i
    | none, none => throw s!"internal extraction error: lost binding '{b.source.name}'"
  return ⟨target.label, some ((target.mapping.getD (List.range targetScope.length)).map
    fun i => slots[i]?.getD 0)⟩

/-- The entry of the first statement a list runs: a block has none of its
own, so it is its first statement's, or, empty, the next one's. -/
private partial def firstEntry : List Fragment.Stmt → Option Nat
  | [] => none
  | .block _ _ inner :: rest => (firstEntry inner).orElse fun _ => firstEntry rest
  | s :: _ => some s.pos.1

/-- The same continuation with slot `k` of its scope and context removed:
what follows a pattern no longer holds the value it destructured. -/
private def dropSlot (k : Nat) (after : List ScopeBinding → List (Ty Nat) → Compiler Target)
    (scope : List ScopeBinding) (Γ : List (Ty Nat)) : Compiler Target := do
  let next ← after (scope.eraseIdx k) (Γ.eraseIdx k)
  pure ⟨next.label, some ((next.mapping.getD (List.range (Γ.length-1))).map
    (fun j => if j < k then j else j+1))⟩

private def traversalBudget : List Fragment.Stmt → Nat
  | [] => 1
  | .brk .. :: rest | .cont .. :: rest | .ret .. :: rest | .constants .. :: rest | .mutables .. :: rest | .destructure .. :: rest | .effect .. :: rest => 1 + traversalBudget rest
  | .loop _ _ loopBody update :: rest =>
      1 + traversalBudget loopBody + traversalBudget update + traversalBudget rest
  | .forOf _ _ _ _ _ inner :: rest | .block _ _ inner :: rest =>
      1 + traversalBudget inner + traversalBudget rest
  | .throw .. :: rest => 1 + traversalBudget rest
  -- A `finally` block is compiled on each way out, at most as deep as the
  -- body and handler around the `return` that runs it.
  | .tryStmt _ b none none :: rest => 1 + traversalBudget b + traversalBudget rest
  | .tryStmt _ b (some (_, c)) none :: rest =>
      1 + traversalBudget b + traversalBudget c + traversalBudget rest
  | .tryStmt _ b none (some f) :: rest =>
      2 + traversalBudget b + 3 * traversalBudget f + traversalBudget rest
  | .tryStmt _ b (some (_, c)) (some f) :: rest =>
      2 + traversalBudget b + traversalBudget c + 3 * traversalBudget f + traversalBudget rest
  -- The close is compiled after a `break`, inside the `try` that discards
  -- its throws on a throw, and before each `return`.
  | .closing _ c b :: rest =>
      3 + traversalBudget b + 3 * (2 + traversalBudget c) + traversalBudget rest
  | .ite _ _ thn none :: rest => 2 + traversalBudget thn + traversalBudget rest
  | .ite _ _ thn (some els) :: rest =>
      1 + traversalBudget thn + traversalBudget els + traversalBudget rest
termination_by stmts => sizeOf stmts


/-- A source-level refusal from a pure pass, in the compiler. -/
private def liftSource (x : Except String α) : Compiler α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-- A lambda whose body is statements, read as an expression for a closure
whose code is a term (`Fragment.Expr.termBody`). `why` names that closure. -/
private def termLambda (why : String) : Fragment.Expr → Compiler Fragment.Expr
  | .lambda p receiver tps ps defaults rest ret b => do
    return .lambda p receiver tps ps defaults rest ret (← liftSource (b.termBody why ret))
  | e => pure e

/-- `if (x.f !== c) return x.f;`, the arm one `return` of the tested read:
the scope with the read saved, at the slice of its type the test's arm
admits, its context, the read, the test over the saved value, the returned
read and the `return`'s span. The saved read can stand for the returned one:
between the two nothing runs (the other operand is a literal, a name or a
field read), so both read the same value. Only a tag test, which refines the
saved slot on its edge, and a slice within the returned read's own claim. -/
private def guardedReturn (fc : SourceClaims.Function) (scope : List ScopeBinding)
    (Γ : List (Ty Nat)) (cond : Fragment.Expr) (thn : List Fragment.Stmt) (loopTargets : LoopTargets) :
    Compiler (Option (List ScopeBinding × List (Ty Nat) × Fragment.Expr × Fragment.Expr ×
      Fragment.Expr × Span)) := do
  let some (snapshot, read, tested) := readGuard scope cond | return none
  let [.ret rp e@(.read _ fld (.var _ name))] := thn | return none
  if !loopTargets.finalizers.isEmpty || readSnapshot name fld != some snapshot then return none
  let B ← exprType fc read
  let K := B :: Γ
  let probe := held ⟨snapshot, some read.span⟩ :: scope
  let G := SourceTypes.graph (← table)
  let some (0, tag, equal) := conditionTag G probe K tested | return none
  let slice := BranchRefinement.tagSlice G B tag equal
  let T ← table
  if sameMeaning T slice B || !within T slice (← exprType fc e) then return none
  let ds := { held ⟨snapshot, some read.span⟩ with fixed := some slice } :: scope
  return some (ds, K, read, tested, e, rp)

mutual
/-- One graph a closure's code runs, at one of its signatures: its statements
compiled as a function body is (`body`), from an entry whose context is exactly
the frame the signature describes — the receiver, the parameters, then the
captures — into a program of its own. The unit's program and its state resume
afterwards. A parameter the body assigns is a private cell, allocated at entry
as a function's is. -/
private partial def codeGraph (fc : SourceClaims.Function) (pos : Span) (receiver : ScopeBinding)
    (params : List ScopeBinding) (paramTypes : List (Ty Nat)) (captures : List ScopeBinding)
    (Cs : List (Ty Nat)) (Rt R : Ty Nat) (stmts : List Fragment.Stmt) :
    Compiler (Program × Nat × List (PointClaim Nat) × CodeSource) := do
  let saved ← get
  set { saved with program := [], claims := [], sourceMap := [], assertions := [], cuts := [], handler := none }
  let paramScope ← (params.zip paramTypes).mapM fun (b, contract) => do
    if stmts.any (assignsStmt b.source.name) then
      let reference ← lower (do return [← CellClaims.reference [(valueField, contract)]])
      pure { b with storage := .cell contract reference }
    else pure b
  let bodyScope := receiver :: paramScope ++ captures
  let inputs := Rt :: paramTypes ++ Cs
  let fullScope := receiver :: params ++ captures
  let mut first ← body (traversalBudget stmts) fc R bodyScope stmts none {}
  -- Each assigned parameter gets one fresh private cell at entry, in place of
  -- its slot; the caller still supplies the value.
  for (b,i) in bodyScope.zipIdx.reverse do
    if let .cell _ reference := b.storage then
      if i == 0 || i > params.length then continue
      let Γ := (bodyScope.zip inputs).zipIdx.map fun (entry : (ScopeBinding × Ty Nat) × Nat) =>
        let ((binding,A),j) := entry
        if j < i then match binding.storage with
          | .cell _ ref => if j == 0 || j > params.length then A else ref | .value => A
        else A
      let mapping := (List.range fullScope.length).map fun j => if j == i then 0 else j+1
      first ← emitAt pos (.makeAt .absent [valueField] [.var i])
        (.bind ⟨first.label,some mapping⟩) Γ reference "parameter-allocation"
        (scope := fullScope)
  let entry ← emitAt pos .nul (.effect first) inputs [0] "closure-entry" (scope := fullScope)
  let st ← get
  let result := (st.program, entry.label, st.claims,
    ({ sourceMap := st.sourceMap, assertions := st.assertions, cuts := st.cuts } : CodeSource))
  set { st with program := saved.program, claims := saved.claims, sourceMap := saved.sourceMap, assertions := saved.assertions, cuts := saved.cuts, handler := saved.handler }
  return result

/-- A closure whose code is a term: a generic closure's, whose certificate is
universal over its binders, one collecting a rest array or binding rest
positions, one with a parameter default. Its body is checked once per
signature it offers, as an expression. -/
private partial def closureTerm (fc : SourceClaims.Function) (scope : List ScopeBinding)
    (Γ : List (Ty Nat)) (e : Fragment.Expr) : Compiler DirectProof.Plan := do
  let A ← closureType fc e
  let G := SourceTypes.graph (← table)
  match e with
  | .lambda pos receiverAnnot typeParams params defaults rest ret body => do
    let paramNames := params.map Prod.fst
    -- An ordinary function names its receiver slot `this`: its body and any
    -- arrow inside it resolve `this` to that slot, the arrow as a capture.
    -- An arrow's slot is anonymous, so its `this` resolves outward.
    let receiverName := if receiverAnnot.isSome then "this" else ""
    -- The receiver the source states, `top` for an arrow, which never reads
    -- its own, and for an ordinary function that states none.
    -- A quantified closure takes each arrow's receiver from its checked
    -- instantiation; only a ground annotation is lowered here.
    let Rsource ← match receiverAnnot with
      | some annot =>
        if GenericSource.mentionsParam annot || !typeParams.isEmpty then
          pure [← lower (SourceTypes.use .top)]
        else lower (Fragment.callableType annot)
      | none => pure [← lower (SourceTypes.use .top)]
    if !distinct paramNames || paramNames.any (fun name => name == "" || name == "undefined" || (names scope).contains name) then
      throw "shadowing or duplicate closure parameter is outside the fragment"
    -- A rest parameter whose contract is a mutable `T[]` collects any number
    -- of actuals: the closure has variadic code, and its body finds the store
    -- the call collected in slot 0, above the fixed parameters. The body's
    -- first step wraps the store into the array the parameter names.
    if let some (restName, restJson) := (if rest then params.getLast? else none) then
      if let some elementJson := Fragment.arrayElement restJson (readonly := true) then
        let fixedParams := params.dropLast
        let compileRestBody (claims : SourceClaims.Function) (Rt : Ty Nat) (fixed : List (Ty Nat))
            (restTy S R : Ty Nat) (initialized : List (Ty Nat)) : Compiler DirectProof.Plan := do
          -- The frame: the collected store, the receiver, which an arrow
          -- never reads, then the fixed parameters.
          let frame := S :: Rt :: fixed ++ Γ
          let frameScope := held ⟨"", some pos⟩ :: held ⟨receiverName, some pos⟩ ::
            (fixedParams.map fun (name,_) => held ⟨if defaults.isEmpty then name else "", some pos⟩) ++ scope
          let proto ← prototypeSlot frameScope
          let O ← arrayObject S
          let wrap := DirectProof.cast frame restTy (DirectProof.node frame (arrayTerm proto) O .alloc
            [DirectProof.var frame 0 S, DirectProof.var frame proto [SourceTypes.arrayProtoLabel]])
          let mut ds := held ⟨if defaults.isEmpty then restName else "", some pos⟩ :: frameScope
          let mut H := restTy :: frame
          let mut prologue : List (List (Ty Nat) × DirectProof.Plan) := [(frame, wrap)]
          let order ← match Fragment.parameterOrder params defaults with
            | .ok order => pure order
            | .error reason => throw (locatedRefusal (← table) pos .bindingAnnotation reason)
          for i in order do
            if i == fixedParams.length then
              ds := ds.set (prologue.length - 1) (held ⟨restName, some pos⟩)
            else
              let some (name, _) := fixedParams[i]? | throw "invalid parameter schedule"
              match defaults.lookup i with
              | none => ds := ds.set (prologue.length + 2 + i) (held ⟨name, some pos⟩)
              | some d =>
                let some B := initialized[i]? | throw "missing initialized rest-prefix contract"
                let dp ← closureExpr claims ds H d
                let value ← defaultValuePlan (SourceTypes.graph (← table)) H (prologue.length + 2 + i)
                  B (DirectProof.cast H B dp)
                prologue := prologue ++ [(H, value)]
                H := B :: H
                ds := held ⟨name, some pos⟩ :: ds
          let previous := (← get).resultOverride
          modify fun st => {st with resultOverride := some (body.span, R)}
          let b ← closureExpr claims ds H body
          modify fun st => {st with resultOverride := previous}
          let annotation := DirectProof.cast H R b
          obligation pos annotation.goal (some annotation) "closure-result" ds
          return prologue.foldr (fun (K, value) acc => DirectProof.letE K value acc) annotation
        let polymorphic := !typeParams.isEmpty ||
          (params.map Prod.snd ++ ret.toList).any GenericSource.mentionsParam
        if polymorphic then
          let some overlays := fc.arrowClaims.lookup pos
            | throw "quantified rest checking requires the scheme evidence path"
          let [.arrs [] signatures] := PositiveRules.expand G A
            | throw "quantified rest claims must name variadic signatures"
          if signatures.isEmpty || signatures.length != overlays.length then
            throw "per-signature claims do not match the quantified rest signatures"
          let mut bodies := []
          let mut arrays := []
          let mut term := none
          for ((Rt, Ds, _, R), overlay) in signatures.zip overlays do
            if Ds.length != fixedParams.length then throw "variadic fixed-prefix arity differs from source"
            let some initialized := overlay.initializedParams
              | throw "missing instantiated parameter annotations"
            let some restTy := initialized.getLast? | throw "missing instantiated rest annotation"
            if initialized.length != params.length then throw "instantiated rest parameter count differs from source"
            let some S := storeOf (SourceTypes.graph (← table)) restTy
              | throw "a rest parameter needs an array contract"
            let b ← compileRestBody (fc.withOverlay overlay) Rt Ds restTy S R initialized
            if let some existing := term then
              if existing != b.term then throw "a rest body lowers differently under one of its instantiations"
            else term := some b.term
            bodies := bodies ++ [b]
            arrays := arrays ++ [S]
          let some t := term | throw "quantified rest has no instantiation"
          return DirectProof.node Γ (.make (.variadic fixedParams.length t) .nul) A
            (.funRest arrays) bodies
        let initialized ← fixedParams.mapM fun p => lower (Fragment.callableType p.2)
        let fixed := initialized.zipIdx.map fun (B, i) =>
          if (defaults.lookup i).isSome then (B ++ [3]).eraseDups.mergeSort (· ≤ ·) else B
        let E ← lower (Fragment.callableType elementJson)
        let restTy ← lower (Fragment.translate restJson)
        let some ret := ret
          | throw (locatedRefusal (← table) pos .bindingAnnotation
              "a closure collecting a rest array needs its result annotation")
        let R ← lower (Fragment.callableType ret)
        let rest ← lower (SourceTypes.use (.pack ⟨[], [], some E, false⟩ []))
        let own ← lower (SourceTypes.use (.arrs [] [(Rsource, fixed, [rest], R)]))
        let some S := storeOf (SourceTypes.graph (← table)) restTy
          | throw "a rest parameter needs an array contract"
        modify fun st => {st with hints := own :: restTy ++ S ++ st.hints}
        let b ← compileRestBody fc Rsource fixed restTy S R initialized
        return DirectProof.node Γ (.make (.variadic fixed.length b.term) .nul) [own]
          (.funRest [S]) [b]
    -- A rest parameter stands for the required positions of its tuple
    -- contract: the signature has one position per element, and the body sees
    -- the array this closure allocates from them, as the call allocates one at
    -- run time. Its own slots are anonymous, like a defaulted parameter's.
    let restElements : List Json ← if rest then
        match params.getLast? with
        | some (_, ty) => match Fragment.tupleRequired ty with
          | .ok es => pure es
          | .error reason => throw (locatedRefusal (← table) pos .bindingAnnotation reason)
        | none => throw "a rest parameter needs a parameter"
      else pure []
    let fixedParams := if rest then params.dropLast else params
    let restName := if rest then (params.getLast?.map Prod.fst).getD "" else ""
    -- With defaults, no parameter name is initially available. Raw argument
    -- slots are not initialized source bindings: names become visible only
    -- after initialization. Literal forward-capturing closures use the checked
    -- dependency schedule below; potentially effectful defaults keep order.
    let defaulted := defaults.map Prod.fst
    if rest && (defaulted.contains (params.length - 1) || !typeParams.isEmpty) then
      throw "a rest parameter is neither defaulted nor quantified"
    -- The frame: the receiver, which an arrow never reads (a source `this`
    -- in an arrow is a capture), then the parameters, then the captures.
    let inner := held ⟨receiverName, some pos⟩ :: ((fixedParams.map fun (name,_) =>
      held ⟨if defaults.isEmpty then name else "", some pos⟩) ++
      restElements.map (fun _ => held ⟨"", some pos⟩)) ++ scope
    -- A closure with one set of interior claims per arrow: a compiled scheme
    -- elimination, whose claims are already substituted for each checked
    -- instantiation, or an overloaded closure, whose producer states what its
    -- body claims under each advertised signature. The body is lowered at each
    -- arrow's own types rather than re-cast from a single claim that no
    -- polymorphic or overloaded body can carry. For a scheme the universal
    -- introduction gate ran before this point, so these derivations are its
    -- consequences, never its justification.
    -- A compiled scheme has no ground annotation to lower: its arrows are the
    -- checked instantiations, and each carries its own substituted claims. An
    -- overloaded closure does have one, so it takes the ordinary path below
    -- and uses its per-arrow claims there.
    let compileBody (fc : SourceClaims.Function) (result : Option (Ty Nat))
        (H : List (Ty Nat)) (initialized : Option (List (Ty Nat)) := none) : Compiler DirectProof.Plan := do
      let previousResult := (← get).resultOverride
      modify fun st => { st with resultOverride := result.map (body.span, ·) }
      let mut ds := inner
      let mut ctx := H
      let mut prologue : List (List (Ty Nat) × DirectProof.Plan) := []
      let order ← match Fragment.parameterOrder fixedParams defaults with
        | .ok order => pure order
        | .error reason => throw (locatedRefusal (← table) pos .bindingAnnotation reason)
      for i in order do
        let some (name, sourceType) := fixedParams[i]? | throw "invalid parameter schedule"
        match defaults.lookup i with
        | none =>
          ds := ds.set (prologue.length + 1 + i) (held ⟨name,some pos⟩)
        | some d =>
          let B ← match initialized with
            | some ps => match ps[i]? with
              | some B => pure B
              | none => throw "missing instantiated parameter annotation"
            | none => lower (Fragment.callableType sourceType)
          let dp ← closureExpr fc ds ctx d
          let value ← defaultValuePlan G ctx (prologue.length + 1 + i) B (DirectProof.cast ctx B dp)
          prologue := prologue ++ [(ctx,value)]
          ctx := B :: ctx
          ds := held ⟨name,some pos⟩ :: ds
      -- The rest array is allocated last, after every earlier parameter is
      -- initialized: one store holding the surplus arguments, then the object
      -- that holds the store, which is what a fresh array is here.
      if rest then
        let restTy ← match params.getLast? with
          | some (_, ty) => lower (Fragment.translate ty)
          | none => throw "a rest parameter needs a parameter"
        -- The annotation may have grown the table, so the graph is read again.
        let some S := storeOf (SourceTypes.graph (← table)) restTy
          | throw "a rest parameter needs an array contract"
        let elements ← restElements.mapM fun ty => lower (Fragment.callableType ty)
        let slots := elements.zipIdx.map fun (E,j) =>
          DirectProof.var ctx (prologue.length + 1 + fixedParams.length + j) E
        let store := DirectProof.node ctx (.arrLit (slots.map (·.term))) S .arrLit slots
        prologue := prologue ++ [(ctx,store)]
        ctx := S :: ctx
        ds := held ⟨"",some pos⟩ :: ds
        let proto ← prototypeSlot ds
        let O ← arrayObject S
        let object := DirectProof.cast ctx restTy (DirectProof.node ctx (arrayTerm proto) O .alloc
          [DirectProof.var ctx 0 S, DirectProof.var ctx proto [SourceTypes.arrayProtoLabel]])
        prologue := prologue ++ [(ctx,object)]
        ctx := restTy :: ctx
        ds := held ⟨restName,some pos⟩ :: ds
      let b ← closureExpr fc ds ctx body
      modify fun st => { st with resultOverride := previousResult }
      pure (prologue.foldr (fun (K,value) acc => DirectProof.letE K value acc) b)
    let polymorphic := !typeParams.isEmpty ||
      (params.map Prod.snd ++ ret.toList).any GenericSource.mentionsParam
    if let some overlays := (if polymorphic then fc.arrowClaims.lookup pos else none) then
      let [.arrs L []] := PositiveRules.expand G A | throw "per-arrow claims must name source arrows"
      if L.isEmpty then throw "per-arrow claims name no arrow"
      if overlays.length != L.length then
        throw "per-arrow interior claims do not match the claimed arrows"
      let mut bodies := []
      let mut term := none
      for ((Rt,Di,Ri),overlay) in L.zip overlays do
        if Di.length != paramNames.length then
          throw "an arrow's arity differs from its closure"
        let bi ← compileBody (fc.withOverlay overlay) none (Rt :: Di ++ Γ) overlay.initializedParams
        if let some existing := term then
          if existing != bi.term then throw "a scheme body lowers differently under one of its instantiations"
        else term := some bi.term
        bodies := bodies ++ [DirectProof.cast (Rt :: Di ++ Γ) Ri bi]
      let some t := term | throw "per-arrow claims name no arrow"
      pure (DirectProof.node Γ (.make (.closure paramNames.length t) .nul) A .funE bodies)
    else do
      if !typeParams.isEmpty then
        throw "quantified closure checking requires the scheme evidence path"
      if !defaults.isEmpty && (params.map Prod.snd ++ ret.toList).any GenericSource.mentionsParam then
        throw "a defaulted parameter under a scheme binder is outside the fragment"
      -- A variadic signature is checked at its fixed row: calls through it
      -- pass further actuals, which the code discards (`offerRows`).
      let [.arrs L S] := PositiveRules.expand G A | throw "closure claim must name a source arrow"
      let L := ProgramTyping.offerRows L S
      -- A closure annotated with an enclosing scheme's binder has no ground
      -- annotation to lower. Scheme introduction required its claim to be
      -- exactly that annotation, and the compiled overlay is the claim under
      -- the checked substitution, so the one compiled arrow supplies its types.
      -- A closure without a result annotation has none to lower (`R` is
      -- none): its claimed arrows propose the result, and each is checked.
      let (Ds, R) ← if (params.map Prod.snd ++ ret.toList).any GenericSource.mentionsParam then
          match L with
          | [(_, Di, Ri)] => pure (Di, some Ri)
          | _ => throw "a closure annotated with a scheme binder must carry one substituted arrow"
        else do
          pure (← fixedParams.mapM (fun p => lower (Fragment.callableType p.2)) >>= fun fixed => do
              return fixed ++ (← restElements.mapM fun ty => lower (Fragment.callableType ty)),
            ← ret.mapM fun ret => lower (Fragment.callableType ret))
      -- The advertised domain at a defaulted position also admits `undefined`:
      -- a call may omit it, and the default is what replaces the value bound
      -- there. The body still reads the declared type.
      let Ds := Ds.zipIdx.map fun (D,i) =>
        if defaulted.contains i then ((D ++ [3]).mergeSort (· ≤ ·)).eraseDups else D
      -- A claim may offer more parameters than the closure takes: calls
      -- discard the actuals past them. The ones it takes are the source's.
      let T ← table
      if L.isEmpty || !L.all (fun (_,Di,_) => Ds.length ≤ Di.length &&
          ((Di.take Ds.length).zip Ds).all (fun (D,A) => within T D A)) then
        throw "closure signature claim is outside the source annotation"
      -- An ordinary function may be claimed at fewer receivers than it
      -- states, never at more: its body reads the one it is given.
      let anyReceiver := Rsource == [← lower (SourceTypes.use .top)]
      if !anyReceiver && !L.all (fun (Rt,_,_) => Rt.all Rsource.contains) then
        throw (locatedRefusal (← table) pos .bindingAnnotation
          "closure receiver claim is outside the source annotation")
      -- One prologue binding per defaulted parameter, in the checked schedule,
      -- so reads use initialized values and effects retain source order.
      -- An overloaded closure states what its body claims under each of its
      -- signatures: one body, a separate obligation at each arrow, and the
      -- same lowered term for all of them.
      let overlays := (fc.arrowClaims.lookup pos).getD []
      if !overlays.isEmpty && overlays.length != L.length then
        throw "per-arrow interior claims do not match the claimed arrows"
      -- The annotation's own derivation is at the receiver the source
      -- states: top for an arrow, which never reads it. Without an
      -- annotation there is no such derivation: the claimed arrows are all
      -- the closure promises, and each has its own below.
      let annotation ← R.mapM fun R => do
        let b ← compileBody fc none (Rsource :: Ds ++ Γ)
        let annotation := DirectProof.cast (Rsource :: Ds ++ Γ) R b
        obligation pos annotation.goal (some annotation) "closure-result" inner
        pure annotation
      let bodies ← L.zipIdx.mapM fun ((Rt,Di,Ri),i) => do
        let row := match overlays[i]? with
          | some o => fc.withOverlay o
          | none => fc
        match annotation with
        | some annotation =>
          if some (Rt,Di,Ri) == R.map (Rsource,Ds,·) && overlays.isEmpty then return annotation
        | none => pure ()
        -- Each signature's derivation is about the same body at that
        -- signature's result, which a block body cannot read from its one
        -- enclosing annotation. Without an annotation the block's result is
        -- the arrow's.
        let plan ← compileBody row (if overlays.isEmpty && R.isSome then none else some Ri)
          (Rt :: Di.take Ds.length ++ Γ)
        return DirectProof.cast (Rt :: Di.take Ds.length ++ Γ) Ri plan
      -- One body, one lowered term: every signature's derivation is about
      -- the same closure. A claim that changes the lowering is refused here
      -- rather than failing as an unexplained search.
      let terms := (annotation.toList ++ bodies).map (·.goal.term)
      let some t := terms.head? | throw "closure claim must name a source arrow"
      if terms.any (· != t) then
        throw "an overloaded closure's body lowers differently under one of its signatures"
      pure (DirectProof.node Γ (.make (.closure Ds.length t) .nul) A .funE bodies)
  | _ => throw "internal extraction error: a closure's code is a lambda's"

/-- The graph of a closure whose body is an expression, `x => e`: the nodes
of `return e`, compiled as that statement's are, entered from the frame the
signature describes. -/
private partial def exprCode (fc : SourceClaims.Function) (pos : Span) (receiver : ScopeBinding)
    (params : List ScopeBinding) (paramTypes : List (Ty Nat)) (captures : List ScopeBinding)
    (Cs : List (Ty Nat)) (Rt R : Ty Nat) (e : Fragment.Expr) :
    Compiler (Program × Nat × List (PointClaim Nat) × CodeSource) := do
  let saved ← get
  set { saved with program := [], claims := [], sourceMap := [], assertions := [], cuts := [], handler := none }
  let bodyScope := receiver :: params ++ captures
  let inputs := Rt :: paramTypes ++ Cs
  -- The expression's nodes, as a `return e` statement's, ending in the
  -- return of its value.
  let A ← exprType fc e
  let done ← emitAt e.span (.var 0) .ret (A::inputs) R "return-contract"
    (scope := held ⟨"",some e.span⟩ :: bodyScope)
  let ret ← compileExpr fc bodyScope inputs e done
  let st ← get
  let result := (st.program, ret.label, st.claims,
    ({ sourceMap := st.sourceMap, assertions := st.assertions, cuts := st.cuts } : CodeSource))
  set { st with program := saved.program, claims := saved.claims, sourceMap := saved.sourceMap, assertions := saved.assertions, cuts := saved.cuts, handler := saved.handler }
  return result

/-- **A closure whose body is a graph.** Its code is the graph its statements
compile to (`CallCode.graph`), checked at each signature the closure's claim
offers from that signature's frame, the captures at their types here: one
code request per signature, whose certificate the unit's code table records.
The captures are the named bindings in scope; a closure reads nothing else.
The closure's value is the allocation of that code with them
(`Rule.funGraph`). -/
private partial def graphClosure (fc : SourceClaims.Function) (scope : List ScopeBinding)
    (Γ : List (Ty Nat)) (pos : Span) (receiverAnnot : Option Json) (params : List (String × Json))
    (body : Fragment.Expr) (A : Ty Nat) : Compiler DirectProof.Plan := do
  let G := SourceTypes.graph (← table)
  let paramNames := params.map Prod.fst
  if !distinct paramNames || paramNames.any (fun name => name == "" || name == "undefined" || (names scope).contains name) then
    throw "shadowing or duplicate closure parameter is outside the fragment"
  -- An ordinary function's receiver is `this` in its body; an arrow's is
  -- anonymous, so its `this` is the one it captures.
  let receiverName := if receiverAnnot.isSome then "this" else ""
  let top ← lower (SourceTypes.use .top)
  let Rsource ← match receiverAnnot with
    | some annot => lower (Fragment.callableType annot)
    | none => pure [top]
  -- A generic closure's claim is a scheme row: its code is checked at the
  -- scheme's signatures, over its binders' rows.
  let (L, S) ← match ProgramCertificates.schemeOf G A with
    | some (_, s) => pure (s.signatures, s.variadic)
    | none => match PositiveRules.expand G A with
      | [.arrs L S] => pure (L, S)
      | _ => throw "closure claim must name a source arrow"
  let rows := ProgramTyping.offerRows L S
  let Ds ← params.mapM fun p => lower (Fragment.callableType p.2)
  -- A claim may offer more parameters than the closure takes: calls discard
  -- the actuals past them. The ones it takes are the source's.
  let T ← table
  if rows.isEmpty || !rows.all (fun (_,Di,_) => Ds.length ≤ Di.length &&
      ((Di.take Ds.length).zip Ds).all (fun (D,B) => within T D B)) then
    throw "closure signature claim is outside the source annotation"
  -- An ordinary function may be claimed at fewer receivers than it states,
  -- never at more: its body reads the one it is given.
  if Rsource != [top] && !rows.all (fun (Rt,_,_) => Rt.all Rsource.contains) then
    throw (locatedRefusal (← table) pos .bindingAnnotation
      "closure receiver claim is outside the source annotation")
  let overlays := (fc.arrowClaims.lookup pos).getD []
  if !overlays.isEmpty && overlays.length != rows.length then
    throw "per-arrow interior claims do not match the claimed arrows"
  -- The captures: the named bindings in scope the body reads (a class's
  -- method binding, `C.m`, which `super.m(...)` reads, included), and the
  -- prototypes a literal or a primitive's member reads through. A read
  -- snapshot is an observation of this point, not a binding the body reads:
  -- no source read names one.
  let reads := body.freeNames
  let caps := scope.zipIdx.filter fun (b, _) =>
    b.source.name != "" &&
      (reads.contains b.source.name || SourceTypes.prototypeNames.contains b.source.name)
  let Cs ← caps.mapM fun (_, i) => match Γ[i]? with
    | some C => pure C
    | none => throw "internal closure slot mismatch"
  -- A captured receiver keeps its type here: no statement claim names `this`.
  let captures : List ScopeBinding := (caps.zip Cs).map fun ((b, _), C) =>
    if b.source.name == "this" then { b with fixed := some C } else b
  let paramScope : List ScopeBinding := paramNames.map fun name => held ⟨name, some pos⟩
  let arity := params.length
  let mut code : Option (Program × Nat) := none
  for ((Rt, Di, Ri), i) in rows.zipIdx do
    let row := match overlays[i]? with
      | some o => fc.withOverlay o
      | none => fc
    let receiver : ScopeBinding := { source := ⟨receiverName, some pos⟩, fixed := some Rt }
    let (P, start, claims, source) ← match body with
      | .block _ stmts => codeGraph row pos receiver paramScope (Di.take arity) captures Cs Rt Ri stmts
      | e => exprCode row pos receiver paramScope (Di.take arity) captures Cs Rt Ri e
    match code with
    | some c =>
      if c != (P, start) then
        throw "a closure's body lowers differently under one of its signatures"
    | none => code := some (P, start)
    let entry : CodeEntry Nat := ⟨arity, P.map (·.expression), P.map fun n => (n.continuation, n.handler),
      start, Cs, (Rt, Di, Ri)⟩
    modify fun st => { st with codes := st.codes ++ [⟨entry, claims⟩], codeSources := st.codeSources ++ [source] }
  let some (P, start) := code | throw "closure claim must name a source arrow"
  let term := Tm.make (.graph arity (P.map (·.expression)) (P.map fun n => (n.continuation, n.handler))
    start (caps.map fun (_, i) => .var i)) .nul
  pure (DirectProof.node Γ term A .funGraph
    ((caps.zip Cs).map fun ((_, i), C) => DirectProof.var Γ i C))

/-- Build compositional proofs for lambda bodies and source ternaries without
losing their individual claims. Requirements use the lexical context at the occurrence; synthetic let
slots are introduced only after the operand supplying their type is checked. -/
private partial def closureExpr (fc : SourceClaims.Function) (scope : List ScopeBinding) (Γ : List (Ty Nat))
    (e : Fragment.Expr) : Compiler DirectProof.Plan := do
  -- `(a && b) && c` is `a && (b && c)`, and `||` likewise: JavaScript
  -- evaluates the operands in the same order and yields the same value either
  -- way, and read so, `c` sees what `a` and `b` answered. The inner operator
  -- is typed at the whole's claim, which covers every value it yields.
  if let .logical p andOp (.logical _ andOp' l1 l2) right := e then
    if andOp' == andOp then
      return ← closureExpr fc scope Γ (.logical p andOp l1 (.logical p andOp l2 right))
  let A ← closureType fc e
  let G := SourceTypes.graph (← table)
  if let some asserted := fc.exprCurrent.lookup e.span then
    for (fld, R) in asserted do
      match e with
      | .var _ name => observed scope Γ (snapshotName name (← stringKey fld)) ⟨"",some e.span⟩ e.span A fld R
      | _ => persistentObservation ⟨"",some e.span⟩ e.span A fld R
  let p ← match e with
  | .equality .. => throw "internal unresolved equality"
  | .block .. => throw "internal extraction error: statements outside a closure body"
  | .var _ name =>
    match resolve scope name with
    | some (i, .value) => pure (DirectProof.var Γ i A)
    | some (i, .cell contract reference) =>
      if let some saved := (names scope).idxOf? (localSnapshotName name) then
        let some R := Γ[saved]? | throw "internal saved-local slot mismatch"
        pure (DirectProof.var Γ saved R)
      else
        pure (DirectProof.node Γ (.readAt valueField (.var i)) contract .read [DirectProof.var Γ i reference])
    | none => throw s!"unbound or uninitialized closure variable '{name}'"
  | .nullishAssign pos name namePos rhs =>
    -- The administrative assignment shares the source result claim: either
    -- chosen value must establish it. No synthetic producer fact is added.
    closureExpr fc scope Γ (.coalesce pos (.var namePos name) (.assign pos name namePos rhs))
  | .assign _ name _ rhs => do
    let some (i, .cell contract reference) := resolve scope name
      | throw s!"assignment to '{name}', which is not a mutable local"
    let a ← closureExpr fc scope Γ rhs
    let C := a.type
    let H := C::Γ
    let term := Tm.writeAt valueField (.var (i+1)) (.var 0)
    let write := DirectProof.node H term [0] .write
      [DirectProof.var H (i+1) reference, DirectProof.cast H contract (DirectProof.var H 0 C)]
    let done := DirectProof.letE H write (DirectProof.var ([0]::H) 1 C)
    pure (DirectProof.letE Γ a done)
  | .lit _ v => do
    let t ← SourceTypes.value v
    let (B,r) ← match t with
      | .nul => pure ([0],ProgramCertificates.Rule.nul)
      | .undef => pure ([3],ProgramCertificates.Rule.undef)
      | .tru => pure ([1],ProgramCertificates.Rule.truLit)
      | .fls => pure ([2],ProgramCertificates.Rule.flsLit)
      -- A number has no fixed row: its singleton is interned like any other
      -- clause the program mentions.
      | .num b => do pure ([← lower (SourceTypes.use (.numLit b))],
          ProgramCertificates.Rule.numLit)
      | .str s => do pure ([← lower (SourceTypes.use (.strLit s))],
          ProgramCertificates.Rule.strLit)
      | _ => throw "unsupported closure literal"
    pure (DirectProof.node Γ t B r)
  | .shapeTest p tag equal e => do
    let operand ← closureExpr fc scope Γ e
    inOperand p tag operand.type
    let result ← tagTestPlan G tag (operand.type::Γ) 0 equal A
    pure (DirectProof.letE Γ operand result)
  | .singletonTest _ tag equal testLeft left right => do
    let leftSpan := left.span
    let left ← closureExpr fc scope Γ left
    let right ← closureExpr fc (held ⟨"",some leftSpan⟩ :: scope) (left.type::Γ) right
    let H := right.type::left.type::Γ
    let result ← tagTestPlan G tag H (if testLeft then 1 else 0) equal A
    pure (DirectProof.letE Γ left (DirectProof.letE (left.type::Γ) right result))
  | .logical _ andOp left right => do
    let l ← closureExpr fc scope Γ left
    if BranchRefinement.onlyBoolean G l.type then
      -- A Boolean's falsy value is `false` and its truthy one `true`, so the
      -- short-circuit arm is that constant, and the operator is a condition.
      let constant := fun (_ : List ScopeBinding) H => pure
        (if andOp then DirectProof.node H .fls [2] .flsLit
         else DirectProof.node H .tru [1] .truLit)
      let rhs := fun ds types => closureExpr fc ds types right
      conditionalPlan scope Γ A left l
        (if andOp then rhs else constant) (if andOp then constant else rhs)
    else
      -- `a && b` is `let x = a in (x ? b : x)`, and `a || b` is
      -- `let x = a in (x ? x : b)`, on `x`'s truthiness: the right operand
      -- runs where the left is truthy (`&&`) or falsy (`||`), and sees it so.
      let K := l.type :: Γ
      let H := (BranchRefinement.tagSlice G l.type .truthy andOp) :: Γ
      let r ← closureExpr fc (savedOperandScope scope left) H right
      let own := DirectProof.var K 0 A
      pure (DirectProof.letE Γ l
        (← selectPlan G K 0 A .truthy (if andOp then r else own) (if andOp then own else r)))
  | .coalesce _ left right => do
    let l ← closureExpr fc scope Γ left
    let K := l.type :: Γ
    let H := (BranchRefinement.tagSlice G l.type .isNullish true) :: Γ
    let r ← closureExpr fc (savedOperandScope scope left) H right
    pure (DirectProof.letE Γ l (← selectPlan G K 0 A .isNullish r (DirectProof.var K 0 A)))
  | .optional _ mark receiver body => do
    -- `r?.b` is `let x = r in (x == null ? undefined : b)`, with `b` reading
    -- the saved receiver `x` by `chainName`, where it is not nullish: the
    -- shape `??` has with its arms exchanged.
    let r ← closureExpr fc scope Γ receiver
    let K := r.type :: Γ
    let H := (BranchRefinement.tagSlice G r.type .isNullish false) :: Γ
    let b ← closureExpr fc (held ⟨Fragment.chainName,some mark⟩ :: scope) H body
    pure (DirectProof.letE Γ r (← selectPlan G K 0 A .isNullish (DirectProof.node K .undef [3] .undef) b))
  | .not _ a => do
    let a ← closureExpr fc scope Γ a
    if BranchRefinement.onlyBoolean G a.type then
      pure (DirectProof.ifE G Γ A a
        (DirectProof.node Γ .fls [2] .flsLit) (DirectProof.node Γ .tru [1] .truLit))
    else
      -- `!x` of a value that is not a Boolean negates its truthiness.
      let K := a.type :: Γ
      pure (DirectProof.letE Γ a (← selectPlan G K 0 A .truthy
        (DirectProof.node K .fls [2] .flsLit) (DirectProof.node K .tru [1] .truLit)))
  | .cast _ annot a => do
    -- The value is the operand's; the claim at the cast follows from the
    -- operand's, and an annotation is one more type the operand must meet.
    let B ← exprType fc a
    let p ← closureExpr fc scope Γ a
    if let some ty := annot then
      let T ← lower (Fragment.translate ty)
      let check := DirectProof.var (B::Γ) 0 T
      obligation e.span check.goal (some check) "cast-annotation" (held ⟨"",some a.span⟩ :: scope)
    pure (DirectProof.cast Γ A p)
  | .alloc _ ns es => do
    if es.length != ns.length then throw "allocation initializer count mismatch"
    let ps ← es.mapM fun a => closureExpr fc scope Γ a
    -- A record naming exactly the literal's keys; a key bound, if claimed,
    -- admits every one of them, as the fresh object's own keys are exactly
    -- those. Such a bound is what lets the literal meet a dictionary or an
    -- optional field it leaves out (`CoversKeys`, `CoversOptional`).
    let [.refs B [] [] [] [] ks] := PositiveRules.expand G A
      | throw "allocation claim must name a record contract"
    if B.length != ns.length then throw "allocation claim names different fields"
    if !ks.all (fun K => ns.all (fun n => K.admits n)) then
      throw "an allocation's key bound must admit every key it allocates"
    let B ← ns.mapM fun name => do
      let some D := B.lookup name | throw "allocation claim names different fields"
      pure (name,D)
    let Ref ← lower (SourceTypes.use (.refs B [] [] [] [] ks))
    -- The calculus evaluates these initializers from left to right.
    let casts := (ps.zip (B.map Prod.snd)).map fun (p,D) => DirectProof.cast Γ D p
    pure (DirectProof.node Γ (.makeAt .absent ns (ps.map (·.term))) [Ref] .alloc casts)
  | .build _ ns es => do
    -- A chain of merges from a fresh accumulator: the fields before the
    -- first spread allocated together, each spread copied onto what is
    -- built so far as soon as its operand is evaluated, and each later run
    -- of fields allocated, then copied on too. One nested term evaluates the
    -- parts in source order.
    let merge (a b : DirectProof.Plan) : Compiler DirectProof.Plan := do
      let R ← mergeType a.type b.type
      pure (DirectProof.node Γ (.merge [] a.term b.term) R .merge [a, b])
    let claimed ← claimedFields A
    let group (fields : List (String × DirectProof.Plan)) : Compiler DirectProof.Plan := do
      let fields := fields.map fun (k, p) => (k, match claimed.lookup k with
        | some D => DirectProof.cast Γ D p
        | none => p)
      let T ← groupType (fields.map Prod.fst) (fields.map (·.2.type))
      pure (DirectProof.node Γ (.makeAt .absent (fields.map (.str ·.1)) (fields.map (·.2.term))) T .alloc
        (fields.map Prod.snd))
    let mut acc : Option DirectProof.Plan := none
    let mut fields : List (String × DirectProof.Plan) := []
    for (n, a) in ns.zip es do
      let p ← closureExpr fc scope Γ a
      match n with
      | some k => fields := fields ++ [(k, p)]
      | none =>
        let g ← group fields
        let base ← match acc with
          | none => pure g
          | some x => if fields.isEmpty then pure x else merge x g
        fields := []
        acc := some (← merge base p)
    let some x := acc | throw "internal: an object literal with spreads has none"
    let result ← if fields.isEmpty then pure x else merge x (← group fields)
    pure (DirectProof.cast Γ A result)
  | .read _ fld a => do
    let receiver := a
    let a ← throughBound Γ (← closureExpr fc scope Γ a)
    let snapshot := match receiver with
      | .var _ name => (readSnapshot name fld).bind (names scope).idxOf?
      | _ => none
    if let some i := snapshot then
      let some R := Γ[i]? | throw "internal saved-read slot mismatch"
      pure (DirectProof.var Γ i R)
    else
      let K := a.type :: Γ
      let arms ← primitiveArms (held ⟨"",some receiver.span⟩ :: scope) K a.type fld
      -- An array's `length` is its store's, read as a number, as the graph
      -- reads it.
      if arms.isEmpty && fld == "length" && (storeOf G a.type).isSome then
        let store ← readCell G Γ SourceTypes.storeField a
        let N : Ty Nat := [← lower (SourceTypes.use .num)]
        pure (DirectProof.node Γ (.lenOf store.term) N .len [store])
      else if arms.isEmpty then readCell G Γ fld a
      else pure (DirectProof.letE Γ a (← memberReadPlan G K 0 fld A arms))
  | .index _ (some fld) receiver key => do
    -- The receiver, then the key, then the read: the key's own claim was
    -- resolved to the field, and is checked here like any operand's.
    let r ← throughBound Γ (← closureExpr fc scope Γ receiver)
    let k ← closureExpr fc (held ⟨"",some receiver.span⟩ :: scope) (r.type::Γ) key
    let H := k.type::r.type::Γ
    let arms ← primitiveArms (held ⟨"",some key.span⟩ :: held ⟨"",some receiver.span⟩ :: scope) H r.type fld
    let read ← if arms.isEmpty then readCell G H fld (DirectProof.var H 1 r.type)
      else memberReadPlan G H 1 fld A arms
    pure (DirectProof.letE Γ r (DirectProof.letE (r.type::Γ) k read))
  | .index _ none receiver key => do
    let r ← closureExpr fc scope Γ receiver
    let k ← closureExpr fc (held ⟨"",some receiver.span⟩ :: scope) (r.type::Γ) key
    let G := SourceTypes.graph (← table)
    let [.dict _ [] _ ix [] [] [] _] := PositiveRules.expand G r.type
      | throw "a dynamic index requires a dictionary receiver"
    -- The key's clause names the keys it reaches: a string any string key, a
    -- number a canonical numeric one, a symbol a symbol key. An index over
    -- as many keys reads it.
    let [c] := PositiveRules.expand G k.type
      | throw "a dynamic dictionary key must be a string, a number or a symbol"
    let some KK := [IndexKeys.strings, .numeric, .symbols].find? (PositiveNormalization.keyClause · == c)
      | throw "a dynamic dictionary key must be a string, a number or a symbol"
    let some (K, E) := (ix.find? (·.1 == KK)).orElse fun _ => ix.find? (fun (K, _) => KK.within K)
      | throw "no index of the dictionary constrains the dynamic key's keys"
    let H := k.type::r.type::Γ
    let read := DirectProof.node H (.indexAt (.var 1) (.var 0)) (E ++ [3])
      (.indexDict K KK E [3]) [DirectProof.var H 1 r.type, DirectProof.var H 0 k.type]
    pure (DirectProof.letE Γ r (DirectProof.letE (r.type::Γ) k read))
  | .indexWrite _ (some fld) receiver key rhs => do
    let B ← exprType fc receiver
    let r ← closureExpr fc scope Γ receiver
    let k ← closureExpr fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key
    let a ← closureExpr fc (held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope) (k.type::B::Γ) rhs
    let H := a.type::k.type::B::Γ
    let write ← writeCell G H fld B a.type 2
    let done := DirectProof.letE H write (DirectProof.var ([0]::H) 1 a.type)
    pure (DirectProof.letE Γ r (DirectProof.letE (B::Γ) k (DirectProof.letE (k.type::B::Γ) a done)))
  | .indexWrite _ none .. => throw "internal unresolved computed key"
  | .arith _ op l r => do
    -- The rule checks the operands pair by pair; the result is the family of
    -- its kind, whatever its value.
    let a ← closureExpr fc scope Γ l
    let b ← closureExpr fc (held ⟨"",some l.span⟩ :: scope) (a.type::Γ) r
    let H := a.type::Γ
    let N ← operatorResult op a.type b.type
    pure (DirectProof.letE Γ a
      (DirectProof.node H (.arith op (.var 0) b.term) N .arith [DirectProof.var H 0 a.type, b]))
  | .unary _ .typeof a => do
    -- `typeof a`: the operand once, then one selection per answer
    -- (`typeofTerm`), each arm the answer's string.
    let p ← closureExpr fc scope Γ a
    let K := p.type :: Γ
    let answer := fun (s : String) => do
      let B := [← lower (SourceTypes.use (.strLit s))]
      pure (DirectProof.node K (.str s) B .strLit)
    let chain ← typeofAnswers.foldrM (fun (tag, s) rest => do
      selectPlan G K 0 A tag (DirectProof.cast K A (← answer s)) rest)
      (DirectProof.cast K A (← answer "function"))
    pure (DirectProof.letE Γ p chain)
  | .unary pos op a => do
    let p ← closureExpr fc scope Γ a
    let (arith, c, C, rule) ← unaryOperation pos op p.type
    let H := p.type::Γ
    let N ← operatorResult arith p.type p.type
    pure (DirectProof.letE Γ p
      (DirectProof.node H (.arith arith (.var 0) c) N .arith
        [DirectProof.var H 0 p.type, DirectProof.node H c C rule]))
  | .inKeys p key o => do
    -- The key, then the object, then one selection per singleton of the key.
    let k ← closureExpr fc scope Γ key
    let r ← closureExpr fc (held ⟨"",some key.span⟩ :: scope) (k.type::Γ) o
    inOperand p (.hasKey (.str "")) r.type
    let keys ← inKeyList p k.type
    let H := r.type::k.type::Γ
    let test := fun (s : String) => tagTestPlan G (.hasKey (.str s)) H 0 true A
    let chain ← match keys.reverse with
      | [] => throw "internal: an `in` key without singletons"
      | last :: earlier => do
        earlier.reverse.foldrM (fun s rest => do selectPlan G H 1 A (.strEq s) (← test s) rest) (← test last)
    pure (DirectProof.letE Γ k (DirectProof.letE (k.type::Γ) r chain))
  | .comma _ l r => do
    -- The left operand is bound and never read; the claim at the comma
    -- follows from the right operand's.
    let a ← closureExpr fc scope Γ l
    let b ← closureExpr fc (held ⟨"",some l.span⟩ :: scope) (a.type::Γ) r
    pure (DirectProof.letE Γ a (DirectProof.cast (a.type::Γ) A b))
  | .update .. => throw "compound assignment inside a closed expression is outside the fragment"
  | .arrayLit _ elems => do
    -- The elements, in order, fill a fresh store, and the array object holds
    -- it with the prototype from its slot, then reads as the claimed array.
    let some S := storeOf G A | throw "an array literal needs an array claim"
    let [.list T []] := PositiveRules.expand G S | throw "an array literal needs one tuple contract"
    let proto ← prototypeSlot scope
    let some P := Γ[proto]? | throw "internal prototype slot mismatch"
    let ps ← elems.mapM fun a => closureExpr fc scope Γ a
    let casts ← ps.zipIdx.mapM fun (p, i) => do
      let some D := ProgramTyping.positionTy T i | throw "an array literal has more elements than its claim"
      pure (DirectProof.cast Γ D p)
    let store := DirectProof.node Γ (.arrLit (ps.map (·.term))) S .arrLit casts
    let O ← arrayObject S
    let object := DirectProof.node Γ (.makeAt .absent [SourceTypes.storeField, SourceTypes.protoField]
      [store.term, .var proto]) O .alloc [store, DirectProof.var Γ proto P]
    pure (DirectProof.cast Γ A object)
  | .elemAt _ receiver key => do
    -- The receiver, then the key, both saved; the element is read from the
    -- receiver's store at the key's one index, or a string's code unit at
    -- the key's number.
    let r ← closureExpr fc scope Γ receiver
    let k ← closureExpr fc (held ⟨"",some receiver.span⟩ :: scope) (r.type::Γ) key
    let H := k.type::r.type::Γ
    if decide (Answers G r.type .isStr true) then
      let T : Ty Nat := [← lower (SourceTypes.use .str)]
      let read := DirectProof.node H (.elemAt (.var 1) (.var 0)) (T ++ [3]) (.elemStr T [3])
        [DirectProof.var H 1 r.type, DirectProof.var H 0 k.type]
      return DirectProof.letE Γ r (DirectProof.letE (r.type::Γ) k (DirectProof.cast H A read))
    let index ← arrayKeyTerm k.type
    let .num b := index | throw "internal array index term"
    let read ← elemReadPlan G H (DirectProof.var H 1 r.type) b
    pure (DirectProof.letE Γ r (DirectProof.letE (r.type::Γ) k (DirectProof.cast H A read)))
  | .elemWrite .. | .arrayAssign .. => throw "array writes inside a closed expression are outside the fragment"
  | .logicalAssign pos .nullish (.var np name) rhs =>
    closureExpr fc scope Γ (.nullishAssign pos name np rhs)
  | .logicalAssign .. => throw "logical assignment inside a closed expression is outside the fragment"
  | .bindWithReceiver _ f receiver args => do
    -- `o.m.bind(o)` of a method member of `o`: the member read from the
    -- object, bound to that same object, is JavaScript's bound function
    -- calling what `o.m` held with `o` (`bindMember`), however it is later
    -- called. The object, then the member, are each read once; the second
    -- read of `o`, the receiver, has no effect.
    if let (.read _ fld o@(.var _ x), .var _ y, []) := (f, receiver, args) then
      if x == y && (ProgramTyping.memberOf G (← exprType fc o) fld).isSome then
        let r ← closureExpr fc scope Γ o
        let _ ← closureExpr fc scope Γ receiver
        let K := r.type :: Γ
        let ds := held ⟨"",some o.span⟩ :: scope
        let M ← exprType fc f
        let method := DirectProof.node K (memberHead G r.type fld (.var 0)) M (.bindMember []) []
        obligation f.span method.goal (some method) "expression-claim" ds
        return DirectProof.letE Γ r
          (DirectProof.node K (memberHead G r.type fld (.var 0)) A (.bindMember []) [])
    -- The target, the receiver and the prefix, each evaluated once and saved,
    -- then a forwarding descriptor holding the saved values: invoking it
    -- ignores its own receiver and calls the target with the saved one and the
    -- prefix before the new actuals (`CallCode.bound`).
    let callee ← closureExpr fc scope Γ f
    let receiverPlan ← closureExpr fc (held ⟨"",some f.span⟩ :: scope) (callee.type::Γ) receiver
    let startScope := held ⟨"",some receiver.span⟩::held ⟨"",some f.span⟩ :: scope
    let (plans,K,_) ← args.attach.foldlM (fun (ps,H,ds) ⟨arg,_⟩ => do
      let p ← closureExpr fc ds H arg
      pure (ps ++ [p],p.type::H,held ⟨"",some arg.span⟩ :: ds))
      ([callee,receiverPlan],receiverPlan.type::callee.type::Γ,startScope)
    let G := SourceTypes.graph (← table)
    let n := args.length
    let boundTypes := (plans.drop 2).map (·.type)
    -- A fixed signature of the target leaves a fixed signature; a variadic one
    -- with an element rest leaves the positions the prefix did not take, then
    -- its rest, the prefix's positions past the fixed ones at the element.
    let (Rt, prefixTys, own, rule) ← match PositiveRules.expand G A with
      | [.arrs [(Rb,Ds,_)] []] => do
        let L ← match PositiveRules.expand G callee.type with
          | [.arrs L _] | [.callable _ _ L _] => pure L
          | _ => throw "bind target requires a single callable contract"
        let (Rt,domains,result) ← selectSignature G L (boundTypes ++ Ds) receiverPlan.type
        if domains.length < n then throw "bind prefix exceeds the target's parameters"
        let own ← lower (SourceTypes.use (.arrs [(Rb, domains.drop n, result)] []))
        pure (Rt, domains.take n, own, ProgramCertificates.Rule.bindE)
      | [.arrs [] [(Rb,_,_,_)]] => do
        let sigs := ProgramTyping.restSigs G callee.type
        let some (Rt, Ps, E, R) := (sigs.find? fun (Rt,_,_,_) => receiverPlan.type.all Rt.contains) <|> sigs.head?
          | throw "a variadic bound function needs a variadic target"
        let some El := PositiveRules.restElem G E
          | throw "a variadic bound function needs an element rest"
        let own ← lower (SourceTypes.use (.arrs [] [(Rb, Ps.drop n, E, R)]))
        pure (Rt, Ps.take n ++ List.replicate (n - Ps.length) El, own, ProgramCertificates.Rule.bindRestE)
      | _ => throw "bound function claim requires one free signature"
    -- The descriptor stores the slots as they are, so each is re-bound at the
    -- contract the selected signature gives it: the receiver, then the prefix.
    let receiverCopy := DirectProof.cast K Rt (DirectProof.var K n receiverPlan.type)
    let (copies, H) ← (List.range n).foldlM (fun (cs, H) i => do
      let some D := prefixTys[i]? | throw "internal bind prefix mismatch"
      let some B := boundTypes[i]? | throw "internal bind prefix mismatch"
      let c := DirectProof.cast H D (DirectProof.var H (n - 1 - i + cs.length) B)
      pure (cs ++ [c], D :: H))
      ([receiverCopy], Rt :: K)
    let bound := DirectProof.node H
      (.makeAt (.bound (.var (2*n+2)) (.var n) ((List.range n).map fun i => .var (n-1-i))) [] [])
      [own] rule []
    pure (saveOperands (plans ++ copies) (DirectProof.cast H A bound))
  | .applyWithReceiver _ f receiver list => do
    -- The target, the receiver and the list, saved in order. A null or
    -- undefined list gives no actuals; reading an array's elements is an array
    -- operation, which a closed expression does not have.
    let callee ← closureExpr fc scope Γ f
    let K := callee.type :: Γ
    let receiverPlan ← closureExpr fc (held ⟨"",some f.span⟩ :: scope) K receiver
    let H := receiverPlan.type :: K
    let ds := held ⟨"",some receiver.span⟩::held ⟨"",some f.span⟩ :: scope
    let (saved, J, dsJ) ← match list with
      | none => pure ([], H, ds)
      | some xs => do
        let lp ← closureExpr fc ds H xs
        if !nullishList G lp.type then
          throw "an array argument list inside a closed expression is outside the fragment"
        pure ([lp], lp.type :: H, held ⟨"",some xs.span⟩ :: ds)
    let m := saved.length
    let L ← match PositiveRules.expand G callee.type with
      | [.arrs L _] | [.callable _ _ L _] => pure L
      | _ => throw ".apply target requires a single callable contract"
    let (Rt,Ds,R) ← selectSignature G L [] receiverPlan.type
    let receiverCheck := DirectProof.cast J Rt (DirectProof.var J m receiverPlan.type)
    obligation receiver.span receiverCheck.goal (some receiverCheck) "method-receiver" dsJ
    let rule := match PositiveRules.expand G callee.type with
      | [.callable ..] => ProgramCertificates.Rule.callCallable
      | _ => .app
    let call := DirectProof.node J (.invoke (.var (m+1)) (.var m) []) R rule
      (DirectProof.var J (m+1) callee.type :: receiverCheck :: omittedPremises J Ds 0)
    pure (saveOperands ([callee, receiverPlan] ++ saved) call)
  | .callWithReceiver _ f receiver args => do
    let callee ← closureExpr fc scope Γ f
    let K := callee.type :: Γ
    let receiverPlan ← closureExpr fc (held ⟨"",some f.span⟩ :: scope) K receiver
    let H := receiverPlan.type :: K
    let ds := held ⟨"",some receiver.span⟩::held ⟨"",some f.span⟩ :: scope
    let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr fc ds H a
    let L ← match PositiveRules.expand G callee.type with
      | [.arrs L _] | [.callable _ _ L _] => pure L
      | _ => throw ".call target requires a single callable contract"
    let (Rt,Ds,R) ← selectSignature G L (actuals.map (·.type)) receiverPlan.type
    let rule := match PositiveRules.expand G callee.type with
      | [.callable ..] => ProgramCertificates.Rule.callCallable
      | _ => .app
    -- `.call` passes its first argument as the receiver.
    let receiverCheck := DirectProof.cast H Rt (DirectProof.var H 0 receiverPlan.type)
    obligation receiver.span receiverCheck.goal (some receiverCheck) "method-receiver" ds
    let call := DirectProof.node H (.invoke (.var 1) (.var 0) (actuals.map (·.term))) R rule
      (DirectProof.var H 1 callee.type
        :: receiverCheck
        :: ((actuals.zip Ds).map fun (a,D) => DirectProof.cast H D a)
          ++ omittedPremises H Ds actuals.length)
    pure (DirectProof.letE Γ callee (DirectProof.letE K receiverPlan call))
  | .invoke _ callee args spreads typeArgs => do
    -- The object, then a computed key, then the method read from the object,
    -- each saved; the actuals; the saved method invoked with the saved object.
    -- A method the object does not hold, such as an array's, is read from its
    -- prototype (`readCell`, `readProto`) at the member's scheme, and the claim
    -- at the call's instance is below it. An element as the method, or a
    -- spread's store, stays outside a closed expression.
    if !spreads.isEmpty then throw "a spread argument inside a closed expression is outside the fragment"
    let (o, fld, key) ← match callee with
      | .read _ fld o => pure (o, fld, none)
      | .index _ (some fld) o key => pure (o, fld, some key)
      | _ => throw "array operations inside a closed expression are outside the fragment"
    let r ← closureExpr fc scope Γ o
    let K₀ := r.type :: Γ
    let ds₀ := held ⟨"",some o.span⟩ :: scope
    let (saved, K, ds) ← match key with
      | none => pure ([r], K₀, ds₀)
      | some key => do
        let k ← closureExpr fc ds₀ K₀ key
        pure ([r,k], k.type :: K₀, held ⟨"",some key.span⟩ :: ds₀)
    let ri := saved.length - 1
    let M ← exprType fc callee
    explicitInstance e.span r.type M fld typeArgs
    let arms ← primitiveArms ds K r.type fld
    let method ← if (ProgramTyping.memberOf G r.type fld).isSome then
        pure (DirectProof.node K (memberHead G r.type fld (.var ri)) M (.bindMember []) [])
      else if !arms.isEmpty then memberReadPlan G K ri fld M arms
      else DirectProof.cast K M <$> readCell G K fld (DirectProof.var K ri r.type)
    obligation callee.span method.goal (some method) "expression-claim" ds
    let H := M :: K
    let dsH := held ⟨"",some callee.span⟩ :: ds
    let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr fc dsH H a
    let fixedFits := match PositiveRules.expand G M with
      | [.arrs L _] | [.callable _ _ L _] => L.any fun p => args.length ≤ p.2.1.length
      | _ => false
    let term := Tm.invoke (.var 0) (.var (ri+1)) (actuals.map (·.term))
    let call ← match PositiveRules.expand G M, ProgramTyping.restSigs G M with
      | _, sigs@(_ :: _) =>
        -- A variadic method: the fixed actuals at its parameters, trailing
        -- ones omitted as `undefined`, every further actual at its position
        -- in the rest.
        if fixedFits then throw "a call both a fixed and a variadic signature take is outside the fragment"
        let some (Rt, Ps, E, R) := (sigs.find? fun (Rt,_,_,_) => r.type.all Rt.contains) <|> sigs.head?
          | throw "internal variadic signature"
        let receiver := DirectProof.cast H Rt (DirectProof.var H (ri+1) r.type)
        obligation o.span receiver.goal (some receiver) "method-receiver" dsH
        let k := min actuals.length Ps.length
        let extra := actuals.drop k
        let positions ← extra.zipIdx.mapM fun (_, i) => match restPosition G E i with
          | some D => pure D
          | none => throw "an actual past the rest's positions"
        pure (DirectProof.node H term R
          (.callRest k (Ps.length - k) (extra.map fun _ => false) E)
          (DirectProof.var H 0 M :: receiver ::
            ((actuals.take k).zip Ps).map (fun (a,D) => DirectProof.cast H D a)
            ++ omittedPremises H Ps k ++ (extra.zip positions).map fun (a,D) => DirectProof.cast H D a))
      | [.arrs L _], [] | [.callable _ _ L _], [] =>
        let (Rt,Ds,R) ← selectSignature G L (actuals.map (·.type)) r.type
        let receiver := DirectProof.cast H Rt (DirectProof.var H (ri+1) r.type)
        obligation o.span receiver.goal (some receiver) "method-receiver" dsH
        let rule := match PositiveRules.expand G M with
          | [.callable ..] => ProgramCertificates.Rule.callCallable
          | _ => .app
        pure (DirectProof.node H term R rule
          (DirectProof.var H 0 M :: receiver
            :: ((actuals.zip Ds).map fun (a,D) => DirectProof.cast H D a)
              ++ omittedPremises H Ds actuals.length))
      | _, _ => throw "a method call's target requires one callable contract"
    pure (saveOperands (saved ++ [method]) call)
  | .call _ f args spreads _ => do
    -- Reading a spread operand's elements is an array operation, which a
    -- closed expression does not have.
    if !spreads.isEmpty then throw "a spread argument inside a closed expression is outside the fragment"
    let callee ← closureExpr fc scope Γ f
    -- A variadic signature serves a call no fixed arrow takes by arity: its
    -- fixed parameters, trailing ones omitted as `undefined`, then every
    -- further actual at its position in the rest.
    let fixedFits := match PositiveRules.expand G callee.type with
      | [.arrs L _] | [.callable _ _ L _] => L.any fun p => args.length ≤ p.2.1.length
      | _ => false
    match PositiveRules.expand G callee.type, ProgramTyping.restSigs G callee.type with
    | _, (Rt, Ps, E, R) :: _ =>
      if fixedFits then throw "a call both a fixed and a variadic signature take is outside the fragment"
      let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr fc scope Γ a
      let k := min actuals.length Ps.length
      let extra := actuals.drop k
      let positions ← extra.zipIdx.mapM fun (_, i) => match restPosition G E i with
        | some D => pure D
        | none => throw "an actual past the rest's positions"
      pure (DirectProof.node Γ (.call callee.term (actuals.map (·.term))) R
        (.callRest k (Ps.length - k) (extra.map fun _ => false) E)
        (callee :: plainReceiver Γ Rt :: ((actuals.take k).zip Ps).map (fun (a,D) => DirectProof.cast Γ D a)
          ++ omittedPremises Γ Ps k ++ (extra.zip positions).map fun (a,D) => DirectProof.cast Γ D a))
    | [.arrs L _], [] | [.callable _ _ L _], [] =>
      let rule := match PositiveRules.expand G callee.type with
        | [.callable ..] => ProgramCertificates.Rule.callCallable
        | _ => .app
      let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr fc scope Γ a
      let (Rt,Ds,R) ← selectSignature G L (actuals.map (·.type))
      -- A plain call passes `undefined`: a signature that needs a receiver
      -- is a located obligation, apart from the call's own typing.
      if !admitsUndefined G Rt then
        let plan := plainReceiver Γ Rt
        obligation f.span plan.goal (some plan) "method-receiver" scope
      pure (DirectProof.node Γ (.call callee.term (actuals.map (·.term))) R rule
        (callee :: plainReceiver Γ Rt :: ((actuals.zip Ds).map fun (a,D) => DirectProof.cast Γ D a)
          ++ omittedPremises Γ Ds actuals.length))
    | _, _ =>
      if callee.type.length ≤ 1 then throw "callee must name a source arrow"
      -- Save callee first, then each actual, before splitting its immutable slot.
      let (_,_,actuals) ← args.attach.foldlM (fun (ctx,sc,ps) ⟨a,_⟩ => do
        let p ← closureExpr fc sc ctx a
        pure (p.type::ctx,held ⟨"",some a.span⟩::sc,ps ++ [p]))
        (callee.type::Γ,held ⟨"",some f.span⟩ :: scope,[])
      let As := actuals.map (·.type)
      let alternatives ← callee.type.mapM fun label => do
        let [.arrs L _] := PositiveRules.expand G [label]
          | throw "every callee alternative must name a source arrow"
        let (Rt,Ds,R) ← selectSignature G L As
        pure (label,Rt,Ds,R)
      let R := (alternatives.flatMap fun (_,_,_,R) => R).eraseDups
      let n := As.length
      let H := As.reverse ++ callee.type::Γ
      let term := Tm.call (.var n) ((List.range n).map fun i => .var (n-1-i))
      let children := alternatives.map fun (label,Rt,Ds,result) =>
        let branch := As.reverse ++ [label]::Γ
        DirectProof.cast branch R (DirectProof.node branch term result .app
          (DirectProof.var branch n [label] :: plainReceiver branch Rt ::
            ((As.zip Ds).zipIdx.map fun ((A,D),i) =>
              DirectProof.cast branch D (DirectProof.var branch (n-1-i) A))
            ++ omittedPremises branch Ds n))
      pure (saveOperands (callee::actuals)
        (DirectProof.node H term R (.unionVar n) children))
  | .write _ fld receiver rhs => do
    let B ← exprType fc receiver
    let r ← closureExpr fc scope Γ receiver
    let a ← closureExpr fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) rhs
    let C := a.type
    let H := C::B::Γ
    let write ← writeCell G H fld B C 1
    let done := DirectProof.letE H write (DirectProof.var ([0]::H) 1 C)
    pure (DirectProof.letE Γ r (DirectProof.letE (B::Γ) a done))
  | .done _ => pure (DirectProof.node Γ .nul [0] .nul)
  | .seqBody _ init body => do
    let a ← closureExpr fc scope Γ init
    let b ← closureExpr fc (held ⟨"",some init.span⟩ :: scope) (a.type::Γ) body
    pure (DirectProof.letE Γ a b)
  | .letBody pos name annot init body => do
    if name == "undefined" then throw "shadowing undefined is outside the fragment"
    if name != "" && (names scope).contains name then
      throw "duplicate or shadowing closure local"
    let H ← closureEnv fc pos.1 scope Γ
    for (B,i) in H.zipIdx do
      obligation pos ⟨Γ,.var i,B⟩ (some (DirectProof.var Γ i B)) "closure-entry" scope
    let I ← exprType fc init
    let B ← match annot with
      | some ty => lower (Fragment.translate ty)
      | none => pure I
    let a ← closureExpr fc scope H init
    let annotation := DirectProof.cast H B a
    obligation init.span annotation.goal (some annotation) "binding-annotation" scope
    let b ← closureExpr fc (held ⟨name,some init.span⟩::scope) (I::H) body
    pure (DirectProof.letE H a b)
  | .destructBody pos target init body => do
    -- One entry, as a `letBody`: the initializer once, held anonymously, then
    -- the pattern's bindings over it (`closureDestructure`), then the body.
    let H ← closureEnv fc pos.1 scope Γ
    for (B,i) in H.zipIdx do
      obligation pos ⟨Γ,.var i,B⟩ (some (DirectProof.var Γ i B)) "closure-entry" scope
    let a ← closureExpr fc scope H init
    let b ← closureDestructure fc pos target (held ⟨"",some init.span⟩::scope) (a.type::H) 0
      fun scope K => closureExpr fc scope K body
    pure (DirectProof.letE H a b)
  | .ifBody pos result cond thn els => do
    let H ← if result.isSome then closureEnv fc pos.1 scope Γ else pure Γ
    if result.isSome then
      for (B,i) in H.zipIdx do
        obligation pos ⟨Γ,.var i,B⟩ (some (DirectProof.var Γ i B)) "closure-entry" scope
    if let some (snapshot, read, tested) := readGuard scope cond then
      if readOnly thn && readOnly els then
        let saved ← closureExpr fc scope H read
        let ds := held ⟨snapshot,some read.span⟩ :: scope
        let K := saved.type :: H
        let c ← closureExpr fc ds K cond
        let body ← conditionalPlan ds K A tested c
          (fun names types => closureExpr fc names types thn)
          (fun names types => closureExpr fc names types els)
        pure (DirectProof.letE H saved body)
      else
        let c ← closureExpr fc scope H cond
        conditionalPlan scope H A cond c
          (fun names types => closureExpr fc names types thn)
          (fun names types => closureExpr fc names types els)
    else
      let c ← closureExpr fc scope H cond
      conditionalPlan scope H A cond c
        (fun names types => closureExpr fc names types thn)
        (fun names types => closureExpr fc names types els)
  | .throwBody _ e => do
    -- `throw e`: the operand at its own claim, then a throw at every type.
    let a ← closureExpr fc scope Γ e
    pure (DirectProof.node Γ (.throw a.term) A .throw [a])
  | .atEnv pos body => do
    let H ← closureEnv fc pos.1 scope Γ
    for (B,i) in H.zipIdx do
      obligation pos ⟨Γ,.var i,B⟩ (some (DirectProof.var Γ i B)) "closure-entry" scope
    closureExpr fc scope H body
  | .withValue pos fn initial functionType bagType => do
    -- The function's code is a term: its allocation carries the bag.
    let fn' ← termLambda "a function initializing a callable object" fn
    let f ← closureTerm fc scope Γ fn'
    let fplan := DirectProof.cast Γ (← closureType fc fn') f
    obligation fn.span fplan.goal (some fplan) "expression-claim" scope
    let property ← closureExpr fc scope Γ initial
    let F ← lower (Fragment.translate functionType)
    let PRef ← lower (Fragment.translate bagType)
    let G := SourceTypes.graph (← table)
    let [.arrs L _] := PositiveRules.expand G F | throw "initializer requires a free function annotation"
    let [.refs P [] []] := PositiveRules.expand G PRef
      | throw "initializer requires an invariant record annotation"
    -- A variadic arrow becomes a callable object with its own variadic
    -- signatures; the function annotation is reached by the cast below.
    if let .make (.variadic arity body) .nul := f.term then
      let some (own, arrays, bodies) := restCreation f
        | throw "initializer requires a checked arrow body"
      let [.arrs [] S] := PositiveRules.expand G own
        | throw "initializer requires a variadic signature"
      let some values := allocationChildren property
        | throw "initializer requires a fresh object literal"
      let .alloc _ ns _ := initial | throw "initializer requires a fresh object literal"
      if values.length != P.length then throw "initializer literal does not match its annotation"
      let P ← ns.mapM fun name => do
        let some D := P.lookup name | throw s!"initializer field '{repr name}' is absent from its annotation"
        pure (name,D)
      let fp := DirectProof.cast Γ F f
      let pp := DirectProof.cast Γ PRef property
      obligation fn.span fp.goal (some fp) "callable-function-annotation" scope
      obligation initial.span pp.goal (some pp) "callable-field-annotation" scope
      let C ← lower (SourceTypes.use (.callable P [] [] S))
      modify fun st => {st with hints := C :: st.hints}
      let casts := (values.zip (P.map Prod.snd)).map fun (v,D) => DirectProof.cast Γ D v
      return DirectProof.node Γ
        (.makeAt (.variadic arity body) (P.map Prod.fst) (values.map (·.term))) [C]
        (.makeCallableRest arrays) (casts ++ bodies)
    let .make (.closure arity body) .nul := f.term | throw "initializer requires a fresh arrow"
    let some bodies := creationChildren f | throw "initializer requires a checked arrow body"
    let some values := allocationChildren property
      | throw "initializer requires a fresh object literal"
    let .alloc _ ns _ := initial | throw "initializer requires a fresh object literal"
    if values.length != P.length then throw "initializer literal does not match its annotation"
    -- Initializers stay in source order. An annotation may list the same fields
    -- in another order; pairing by position would silently rename their values.
    let P ← ns.mapM fun name => do
      let some D := P.lookup name | throw s!"initializer field '{repr name}' is absent from its annotation"
      pure (name,D)
    let fp := DirectProof.cast Γ F f
    let pp := DirectProof.cast Γ PRef property
    obligation fn.span fp.goal (some fp) "callable-function-annotation" scope
    obligation initial.span pp.goal (some pp) "callable-field-annotation" scope
    let C ← lower (SourceTypes.use (.callable P [] L []))
    let casts := (values.zip (P.map Prod.snd)).map fun (v,D) => DirectProof.cast Γ D v
    pure (DirectProof.node Γ
      (.makeAt (.closure arity body) (P.map Prod.fst) (values.map (·.term))) [C] .makeCallable
      (casts ++ bodies))
  | .ctor pos lam => do
    -- A class value: its constructor's body once per construct signature, with
    -- `undefined` in the receiver slot `new` passes, then the parameters.
    let .lambda _ none [] params [] false (some ret) body := lam
      | throw "a class value is a constructor lambda with plain parameters"
    -- Construct code is a term: the constructor's statements are read as one
    -- expression, falling through into the instance.
    let body ← liftSource (body.termBody "a class constructor" (some ret) true)
    let paramNames := params.map Prod.fst
    if !distinct paramNames || paramNames.any (fun name => name == "" || name == "undefined" || (names scope).contains name) then
      throw "shadowing or duplicate constructor parameter is outside the fragment"
    let [.ctors L] := PositiveRules.expand G A | throw "a class value's claim must name construct signatures"
    let Ds ← params.mapM fun p => lower (Fragment.callableType p.2)
    let R ← lower (Fragment.callableType ret)
    -- A claim may offer more parameters than the constructor takes: `new`
    -- discards the actuals past them (`ctorE` types the body at the first
    -- `arity`). The ones it takes are the source's.
    let T ← table
    if L.isEmpty || !L.all (fun (Di,_) => Ds.length ≤ Di.length &&
        ((Di.take Ds.length).zip Ds).all (fun (D,B) => within T D B)) then
      throw "construct signature claim is outside the source annotation"
    let inner := held ⟨"", some pos⟩ :: (params.map fun (name,_) => held ⟨name, some pos⟩) ++ scope
    let b ← closureExpr fc inner ([3] :: Ds ++ Γ) body
    let annotation := DirectProof.cast ([3] :: Ds ++ Γ) R b
    obligation pos annotation.goal (some annotation) "closure-result" inner
    let bodies ← L.mapM fun (Di, Ri) => do
      let Di := Di.take Ds.length
      if (Di, Ri) == (Ds, R) then pure annotation else do
        let plan ← closureExpr fc inner ([3] :: Di ++ Γ) body
        if plan.term != b.term then
          throw "a class body lowers differently under one of its construct signatures"
        pure (DirectProof.cast ([3] :: Di ++ Γ) Ri plan)
    pure (DirectProof.node Γ (.make (.closure Ds.length b.term .construct) .nul) A (.ctorE [3]) bodies)
  | .construct _ f args _ => do
    let callee ← closureExpr fc scope Γ f
    let [.ctors L] := PositiveRules.expand G callee.type
      | throw "`new` needs a value with construct signatures"
    let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr fc scope Γ a
    -- As for a call: a signature declaring exactly the actuals written, or a
    -- longer one whose remaining positions admit `undefined`.
    let (_, Ds, R) ← selectSignature G (L.map fun (Ds, R) => ([3], Ds, R)) (actuals.map (·.type))
    pure (DirectProof.node Γ (.construct callee.term (actuals.map (·.term))) R .construct
      (callee :: ((actuals.zip Ds).map fun (a,D) => DirectProof.cast Γ D a)
        ++ omittedPremises Γ Ds actuals.length))
  | .lambda pos receiverAnnot typeParams params defaults rest ret (.block bpos stmts) => do
    -- A body of statements is a graph, as a function body is, unless the
    -- closure's code must be a term: a generic closure's the scheme path
    -- compiles, or one collecting a rest array or binding rest positions,
    -- whose code allocates the array itself. A generic closure claimed at a
    -- scheme row is graph code checked at the row's signatures, its binders
    -- the row's (`HasTy.funScheme`).
    let schemeRow := (ProgramCertificates.schemeOf G A).isSome
    let polymorphic := (!typeParams.isEmpty && !schemeRow) ||
      (params.map Prod.snd ++ ret.toList).any GenericSource.mentionsParam
    if !polymorphic && !rest && defaults.isEmpty then
      graphClosure fc scope Γ pos receiverAnnot params (.block bpos stmts) A
    else
      let why := if polymorphic then "a generic closure's body" else "the body of a closure with a rest parameter"
      return ← closureExpr fc scope Γ
        (← termLambda why (.lambda pos receiverAnnot typeParams params defaults rest ret (.block bpos stmts)))
  | .lambda pos receiverAnnot typeParams params [] false ret body =>
    -- An expression body, `x => e`, is the graph `return e`, unless the
    -- closure's code must be a term (a generic closure's). A body already in
    -- the term forms statements are read into (`Fragment.Expr.termBody`) is
    -- term code: no source lambda has one, only an internal construction.
    let termForm := match body with
      | .atEnv .. | .letBody .. | .seqBody .. | .ifBody .. | .throwBody .. | .destructBody .. | .done .. => true
      | _ => false
    if !termForm && (typeParams.isEmpty || (ProgramCertificates.schemeOf G A).isSome) &&
        !(params.map Prod.snd ++ ret.toList).any GenericSource.mentionsParam then
      graphClosure fc scope Γ pos receiverAnnot params body A
    else closureTerm fc scope Γ e
  | .lambda .. => closureTerm fc scope Γ e
  let plan := DirectProof.cast Γ A p
  obligation e.span plan.goal (some plan) "expression-claim" scope
  -- Validate the supplied claim, but do not discard a stronger saved-read
  -- derivation needed for the enclosing return contract. atEnv is a no-op.
  match e with
  | .read _ fld (.var _ name) =>
    if (readSnapshot name fld).any (names scope).contains then return p else return plan
  | .var _ name =>
    if (names scope).contains (localSnapshotName name) then return p else return plan
  | .atEnv .. => return p
  | _ => return plan




/-- Binds `target` to the value `v` reads under `H`, `default_` replacing it
where it is undefined: the read is held in a slot of its own, then, with a
default, the value `selectPlan` chooses on the `undefined` tag (the read's
labels told apart clause by clause, `byClause`), in another. A name binds the
last; a nested pattern destructures it (`closureDestructure`). `k` compiles
what follows under the extended scope and context. -/
private partial def closureBind (fc : SourceClaims.Function) (pos : Span)
    (target : Fragment.Pattern Fragment.Expr) (v : DirectProof.Plan)
    (default_ : Option Fragment.Expr) (scope : List ScopeBinding) (H : List (Ty Nat))
    (k : List ScopeBinding → List (Ty Nat) → Compiler DirectProof.Plan) : Compiler DirectProof.Plan := do
  let G := SourceTypes.graph (← table)
  let (name, at_) := match target with
    | .name n p => (n, p)
    | .object p _ _ | .array p _ _ => ("", p)
  if name == "undefined" then throw "shadowing undefined is outside the fragment"
  if name != "" && (names scope).contains name then
    throw s!"duplicate or shadowing local declaration '{name}'"
  let bound := held ⟨name,some pos⟩
  let finish (scope : List ScopeBinding) (K : List (Ty Nat)) : Compiler DirectProof.Plan :=
    match target with
    | .name .. => k scope K
    | _ => closureDestructure fc pos target scope K 0 k
  match default_ with
  | none => pure (DirectProof.letE H v (← finish (bound::scope) (v.type::H)))
  | some d =>
    let R ← byClause v.type
    let K := R :: H
    let raw := held ⟨"",some at_⟩ :: scope
    let dp ← closureExpr fc raw K d
    let T := (BranchRefinement.tagSlice G R .isUndef false ++ dp.type).eraseDups
    let chosen ← selectPlan G K 0 T .isUndef dp (DirectProof.var K 0 T)
    let rest ← finish (bound::raw) (T::K)
    pure (DirectProof.letE H (DirectProof.cast H R v) (DirectProof.letE K chosen rest))

/-- The bindings an object or array pattern yields over the value in slot
`obj`, left to right, as the graph lowering's `destructureAt`: a property's
field as `readCell` reads it, an element's position as `elemReadPlan` does,
and a rest the fresh array of the positions after the elements where the
value is one tuple of required positions, claimed at the rest's span. -/
private partial def closureDestructure (fc : SourceClaims.Function) (pos : Span)
    (target : Fragment.Pattern Fragment.Expr) (scope : List ScopeBinding) (H : List (Ty Nat)) (obj : Nat)
    (k : List ScopeBinding → List (Ty Nat) → Compiler DirectProof.Plan) : Compiler DirectProof.Plan := do
  let G := SourceTypes.graph (← table)
  let some A := H[obj]? | throw "internal pattern slot mismatch"
  let rec elems (scope : List ScopeBinding) (H : List (Ty Nat)) (obj : Nat)
      (read : List (Ty Nat) → Nat → Nat × Fragment.Pattern Fragment.Expr × Option Fragment.Expr →
        Compiler DirectProof.Plan)
      (last : List ScopeBinding → List (Ty Nat) → Nat → Compiler DirectProof.Plan) :
      List (Nat × Fragment.Pattern Fragment.Expr × Option Fragment.Expr) → Compiler DirectProof.Plan
    | [] => last scope H obj
    | e :: more => do
      let v ← read H obj e
      closureBind fc pos e.2.1 v e.2.2 scope H fun scope' H' =>
        elems scope' H' (obj + (H'.length - H.length)) read last more
  match target with
  | .name .. => throw "internal: a name is bound, not destructured"
  | .object _ props rest =>
    elems scope H obj (fun H obj (i, _, _) => do
        let some (fld, _, _) := props[i]? | throw "internal pattern property"
        noMethodRead G A fld
        readCell G H fld (DirectProof.var H obj A))
      (fun scope H obj => match rest with
        | none => k scope H
        | some (restPos, t) => do
          -- The source's other own enumerable properties, copied onto a
          -- fresh object: a merge dropping the keys the properties name.
          let drop := props.map fun (fld, _, _) => PropKey.str fld
          let E ← groupType [] []
          let empty := DirectProof.node H (.makeAt .absent [] []) E .alloc []
          let R ← mergeType E A drop
          let C ← claimAt fc restPos
          let copy := DirectProof.node H (.merge drop empty.term (.var obj)) R .merge
            [empty, DirectProof.var H obj A]
          closureBind fc pos t (DirectProof.cast H C copy) none scope H k)
      (props.zipIdx.map fun ((_, t, d), i) => (i, t, d))
  | .array _ positions rest =>
    elems scope H obj (fun H obj (i, _, _) => elemReadPlan G H (DirectProof.var H obj A) (bitsOfNat i))
      (fun scope H obj => match rest with
        | none => k scope H
        | some (start, restPos, slice, t) => do
          if slice then
            throw s!"unsupported source expression at [{restPos.1},{restPos.2}): a slice rest in a closure's directly checked body is outside the fragment: its `%RestFrom%` call is graph code"
          let some S := storeOf G A | throw "an array rest needs one array contract: over a union of arrays of different lengths its rest is a slice of a length known only at run time"
          let [.list T []] := PositiveRules.expand G S | throw restOfUnknownLength
          if !T.optional.isEmpty || T.rest.isSome then throw restOfUnknownLength
          let C ← claimAt fc restPos
          let some Sr := storeOf (SourceTypes.graph (← table)) C | throw "an array rest needs an array claim"
          let [.list Tr []] := PositiveRules.expand (SourceTypes.graph (← table)) Sr
            | throw "an array rest needs an array claim"
          let reads ← (List.range (T.required.length - start)).mapM fun j => do
            let p ← elemReadPlan G H (DirectProof.var H obj A) (bitsOfNat (start + j))
            let some D := ProgramTyping.positionTy Tr j | throw "an array rest has more positions than its claim"
            pure (DirectProof.cast H D p)
          let store := DirectProof.node H (.arrLit (reads.map (·.term))) Sr .arrLit reads
          let proto ← prototypeSlot scope
          let some P := H[proto]? | throw "internal prototype slot mismatch"
          let O ← arrayObject Sr
          let object := DirectProof.node H (.makeAt .absent [SourceTypes.storeField, SourceTypes.protoField]
            [store.term, .var proto]) O .alloc [store, DirectProof.var H proto P]
          closureBind fc pos t (DirectProof.cast H C object) none scope H k)
      positions
/-- Each expression leaves its result in slot zero and preserves the original
slots after it. Anonymous temporary slots cannot be named by source identifiers.
Mappings discard only the temporaries introduced by this expression. -/
private partial def compileExpr (fc : SourceClaims.Function) (scope : List ScopeBinding) (Γ : List (Ty Nat))
    (e : Fragment.Expr) (next : Target) : Compiler Target := do
  let A ← exprType fc e
  let next ← match fc.exprCurrent.lookup e.span with
    | none => pure next
    | some asserted =>
      -- An observation the cell's contract implies holds wherever the cell
      -- is read: a located inclusion (`persistentObservation`), as at a
      -- closure's entry, which knows nothing of the heap. Any other is a fact
      -- of this point, which every edge into it must establish.
      let T ← table
      let clauses := PositiveRules.expand (SourceTypes.graph T) A
      let invariant := fun (fld : PropKey) => do
        if clauses.isEmpty then none
        let ws ← clauses.mapM fun (c : PositiveNormalization.Clause (Ty Nat)) => match c with
          | PositiveNormalization.Clause.refs W [] [] [] [] [] => W.lookup fld
          | _ => none
        some ws.flatten.eraseDups
      let (uniform, pointwise) := asserted.partition fun (fld, R) =>
        (invariant fld).any (within T · R)
      for (fld, R) in uniform do persistentObservation ⟨"",some e.span⟩ e.span A fld R
      let facts ← pointwise.mapM fun (fld, R) => do return (⟨0,← contents R,fld⟩ : HeapFacts.Fact)
      checkpoint e.span (A::Γ) facts next (scope := held ⟨"",some e.span⟩ :: scope)
  match he : e with
  | .equality .. => throw "internal unresolved equality"
  | .block .. => throw "internal extraction error: statements outside a closure body"
  | .var _ name =>
    match resolve scope name with
    | some (i, .value) => emitAt e.span (.var i) (.bind next) Γ A (scope := scope)
    -- A source read of a mutable local returns the cell's contents; the
    -- identity in the slot is never the value of a source expression.
    | some (i, .cell ..) => emitAt e.span (.readAt valueField (.var i)) (.bind next) Γ A (scope := scope)
    | none => throw s!"unbound or uninitialized source variable '{name}'"
  | .nullishAssign pos name namePos rhs => do
    let some (i, .cell ..) := resolve scope name
      | throw s!"assignment to '{name}', which is not a mutable local"
    let left := Fragment.Expr.var namePos name
    let B ← exprType fc left
    let C ← exprType fc rhs
    let G := SourceTypes.graph (← table)
    -- A merge has no unique predecessor from which to propagate knowledge.
    -- Both arms must establish this candidate postcondition independently.
    let next ← match HeapKnowledge.atoms G A with
      | some atoms =>
        checkpoint pos (A::Γ) [⟨i+1,atoms,valueField⟩] next (scope := held ⟨"",some pos⟩ :: scope)
      | none => pure next
    let present := BranchRefinement.tagSlice G B .isNullish false
    let absent := BranchRefinement.tagSlice G B .isNullish true
    let saved := held ⟨"",some namePos⟩ :: scope
    -- The tag witness is the saved read. On the present arm it is also the
    -- result, and its read link justifies the unchanged cell's current type.
    let no ← emitAt pos (.var 0) (.effect next) (present::Γ) A (scope := saved)
    let effects := held ⟨"",some rhs.span⟩ :: saved
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun j => if j == 0 then 0 else j+2))⟩
    let result ← emitAt pos (.var 0) (.bind drop) (C::absent::Γ) A (scope := effects)
    let write ← emitAt pos (.writeAt valueField (.var (i+2)) (.var 0)) (.effect result)
      (C::absent::Γ) [0] "storage-contract" (scope := effects)
    let yes ← compileExpr fc saved (absent::Γ) rhs write
    -- tagBind introduces a refined copy; discard the older saved read.
    let adapt := fun (t : Target) =>
      ⟨t.label, some ((t.mapping.getD (List.range (Γ.length+1))).map
        (fun j => if j == 0 then 0 else j+1))⟩
    let dispatch ← emitAt namePos (.var 0) (.tagBind .isNullish (adapt yes) (adapt no))
      (B::Γ) B "nullish-assignment-dispatch" (scope := saved)
    let dispatch ← match fc.exprCurrent.lookup namePos with
      | none => pure dispatch
      | some asserted =>
        let facts ← asserted.mapM fun (fld, R) => do return (⟨0,← contents R,fld⟩ : HeapFacts.Fact)
        checkpoint namePos (B::Γ) facts dispatch (scope := saved)
    emitAt namePos (.readAt valueField (.var i)) (.bind dispatch) Γ B (scope := scope)
  | .assign _ name _ rhs =>
    let some (i, .cell ..) := resolve scope name
      | throw s!"assignment to '{name}', which is not a mutable local"
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun j => if j == 0 then 0 else j+1))⟩
    -- As for a cell write: JavaScript's assignment yields the value written,
    -- the calculus's write yields null, so the value is saved and returned.
    -- The write itself is the storage-contract check: it types only when the
    -- value meets the contract the cell was declared with.
    let effects := held ⟨"",some rhs.span⟩ :: scope
    let result ← emitAt e.span (.var 0) (.bind drop) (C::Γ) A (scope := effects)
    let write ← emitAt e.span (.writeAt valueField (.var (i+1)) (.var 0)) (.effect result) (C::Γ) [0]
      "storage-contract" (scope := effects)
    compileExpr fc scope Γ rhs write
  | .arrayAssign _ targets rest rhs =>
    -- The right side is held for the whole assignment, below the reads of
    -- its positions; its value is the expression's.
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun j => if j == 0 then 0 else j+1))⟩
    let effects := held ⟨"",some rhs.span⟩ :: scope
    let result ← emitAt e.span (.var 0) (.bind drop) (C::Γ) A (scope := effects)
    let writes ← arrayAssigns fc e.span C rest result effects (C::Γ) 0 targets
    compileExpr fc scope Γ rhs writes
  | .lit _ v => emitAt e.span (← SourceTypes.value v) (.bind next) Γ A (scope := scope)
  | .read _ fld a =>
    let B ← exprType fc a
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    -- An array's `length` is its store's, read as a number; a primitive's
    -- member is read by its shape (`dispatchTerm`).
    let object := if fld == "length" && (storeOf (SourceTypes.graph (← table)) B).isSome
      then Tm.lenOf (.readAt SourceTypes.storeField (.var 0)) else .readAt fld (.var 0)
    let arms ← primitiveArms (held ⟨"",some a.span⟩ :: scope) (B::Γ) B fld
    let node ← emitAt e.span (dispatchTerm arms fld 0 object) (.bind drop) (B::Γ) A
      (scope := held ⟨"",some a.span⟩ :: scope)
    compileExpr fc scope Γ a node
  | .not _ a =>
    let B ← exprType fc a
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    -- A value that is not a Boolean is negated by its truthiness.
    let tested := if BranchRefinement.onlyBoolean (SourceTypes.graph (← table)) B then Tm.var 0
      else .test .truthy (.var 0)
    let node ← emitAt e.span (.ite tested .fls .tru) (.bind drop) (B::Γ) A
      (scope := held ⟨"",some a.span⟩ :: scope)
    compileExpr fc scope Γ a node
  | .cast _ annot a =>
    -- The operand's value, retyped at the cast's own claim: the node proves
    -- the claim from the operand, and an annotation is one more type the
    -- operand must meet. Nothing here decides the assertion is true.
    let B ← exprType fc a
    if let some ty := annot then
      let T ← lower (Fragment.translate ty)
      let check := DirectProof.var (B::Γ) 0 T
      obligation e.span check.goal (some check) "cast-annotation" (held ⟨"",some a.span⟩ :: scope)
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let node ← emitAt e.span (.var 0) (.bind drop) (B::Γ) A "cast" (scope := held ⟨"",some a.span⟩ :: scope)
    compileExpr fc scope Γ a node
  | .alloc _ ns operands =>
    let As ← operands.mapM (exprType fc)
    let n := As.length
    let temporaries := (operands.map fun a => held ⟨"",some a.span⟩).reverse
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+n))⟩
    let make ← emitAt e.span (.makeAt .absent ns ((List.range n).map fun i => .var (n-1-i)))
      (.bind drop) (As.reverse ++ Γ) A (scope := temporaries ++ scope)
    operands.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) =>
      compileExpr fc
        ((operands.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++ scope)
        ((As.take i).reverse ++ Γ) arg next) make
  | .build _ ns operands =>
    -- The parts in source order, each operand into a slot of its own, and
    -- each merge a node of its own right after its spread's operand, so the
    -- copy reads the source before any later part runs; then the result,
    -- at the literal's claim. Forward, the context the chain runs in: the
    -- slots pushed so far, the newest first, with the accumulator's.
    let mut steps : List (Option Fragment.Expr × Tm × Ty Nat × List (Ty Nat) × List ScopeBinding) := []
    let mut temps : List (Ty Nat) := []
    let mut tscope : List ScopeBinding := []
    let mut acc : Option Nat := none
    let mut group : List (String × Nat) := []
    let at_ (a : Nat) (c : Nat) : Tm := .var (c - 1 - a)
    let mark := held ⟨"",some e.span⟩
    -- A field is allocated at the type the literal's claim states for it,
    -- which its slot's value is coerced to, else at its own claim's.
    let claimed ← claimedFields A
    let fieldType (k : String) (T : Ty Nat) : Ty Nat := (claimed.lookup k).getD T
    for (n, a) in ns.zip operands do
      if n.isNone then
        -- Close the fields before the spread: allocate them, and copy them
        -- onto the accumulator when there is one.
        if acc.isNone || !group.isEmpty then
          let T ← groupType (group.map Prod.fst)
            (group.map fun (k, i) => fieldType k temps[temps.length - 1 - i]!)
          let term := Tm.makeAt .absent (group.map (.str ·.1)) (group.map fun (_, i) => at_ i temps.length)
          steps := steps ++ [(none, term, T, temps, tscope)]
          temps := T :: temps; tscope := mark :: tscope
          match acc with
          | none => acc := some (temps.length - 1)
          | some x =>
            let R ← mergeType temps[temps.length - 1 - x]! T
            steps := steps ++ [(none, .merge [] (at_ x temps.length) (.var 0), R, temps, tscope)]
            temps := R :: temps; tscope := mark :: tscope
            acc := some (temps.length - 1)
          group := []
      let B ← exprType fc a
      steps := steps ++ [(some a, .nul, B, temps, tscope)]
      temps := B :: temps; tscope := held ⟨"",some a.span⟩ :: tscope
      match n with
      | some k => group := group ++ [(k, temps.length - 1)]
      | none =>
        let some x := acc | throw "internal: a spread without an accumulator"
        let R ← mergeType temps[temps.length - 1 - x]! B
        steps := steps ++ [(none, .merge [] (at_ x temps.length) (.var 0), R, temps, tscope)]
        temps := R :: temps; tscope := mark :: tscope
        acc := some (temps.length - 1)
    if !group.isEmpty then
      let some x := acc | throw "internal: an object literal with spreads has none"
      let T ← groupType (group.map Prod.fst)
        (group.map fun (k, i) => fieldType k temps[temps.length - 1 - i]!)
      let term := Tm.makeAt .absent (group.map (.str ·.1)) (group.map fun (_, i) => at_ i temps.length)
      steps := steps ++ [(none, term, T, temps, tscope)]
      temps := T :: temps; tscope := mark :: tscope
      let R ← mergeType temps[temps.length - 1 - x]! T
      steps := steps ++ [(none, .merge [] (at_ x temps.length) (.var 0), R, temps, tscope)]
      temps := R :: temps; tscope := mark :: tscope
    -- The result, the newest slot, at the literal's claim.
    let k := temps.length
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+k))⟩
    let final ← emitAt e.span (.var 0) (.bind drop) (temps ++ Γ) A (scope := tscope ++ scope)
    -- Backward, each step continues to the one after it.
    steps.reverse.foldlM (fun next (operand, term, T, before, bscope) =>
      match operand with
      | some a => compileExpr fc (bscope ++ scope) (before ++ Γ) a next
      | none => emitAt e.span term (.bind next) (before ++ Γ) T (scope := bscope ++ scope)) final
  | .atEnv .. | .letBody .. | .destructBody .. | .ifBody _ (some _) .. | .done .. | .seqBody .. | .throwBody .. =>
    throw "statement environment wrapper is only supported inside a closure"
  | .ifBody _ none cond thn els =>
    -- A source ternary branches in the graph like an `if` statement, so an
    -- effect in its condition or an arm is a node with its own knowledge;
    -- each arm is compiled under the condition's refinement of its context
    -- and joins the continuation with its own claim.
    let G := SourceTypes.graph (← table)
    let yes ← compileExpr fc scope (← armContext fc scope (conditionContext G scope Γ cond true) thn) thn next
    let no ← compileExpr fc scope (← armContext fc scope (conditionContext G scope Γ cond false) els) els next
    compileCondition fc scope Γ cond yes no
  | .bindWithReceiver .. | .withValue .. | .lambda .. | .ctor .. | .coalesce .. | .optional .. | .logical .. =>
    let t ← closureExpr fc scope Γ e
    emitAt e.span t.term (.bind next) Γ A (scope := scope)
  | .construct _ callee args _ =>
    -- `new`: the callee, then each actual, saved in order; then the construct
    -- step on the saved slots, as an allocation does with its initializers.
    let operands := callee :: args
    let As ← operands.mapM (exprType fc)
    let n := As.length
    let temporaries := (operands.map fun a => held ⟨"",some a.span⟩).reverse
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+n))⟩
    let construct ← emitAt e.span (.construct (.var (n-1)) ((List.range (n-1)).map fun i => .var (n-2-i)))
      (.bind drop) (As.reverse ++ Γ) A (scope := temporaries ++ scope)
    operands.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) =>
      compileExpr fc
        ((operands.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++ scope)
        ((As.take i).reverse ++ Γ) arg next) construct
  | .shapeTest p tag equal operand =>
    let B ← exprType fc operand
    inOperand p tag B
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let test ← emitAt e.span (tagTestTerm tag equal 0) (.bind drop) (B::Γ) A
      (scope := held ⟨"",some operand.span⟩ :: scope)
    compileExpr fc scope Γ operand test
  | .singletonTest _ tag equal testLeft left right =>
    let B ← exprType fc left
    let C ← exprType fc right
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let test ← emitAt e.span (tagTestTerm tag equal (if testLeft then 1 else 0)) (.bind drop) (C::B::Γ) A
      (scope := held ⟨"",some right.span⟩::held ⟨"",some left.span⟩ :: scope)
    let right ← compileExpr fc (held ⟨"",some left.span⟩ :: scope) (B::Γ) right test
    compileExpr fc scope Γ left right
  | .applyWithReceiver _ callee receiver list =>
    -- Function.prototype.apply: the target, the receiver and the list are
    -- saved in order; then the list's length and each index are read in order
    -- (CreateListFromArrayLike), and the target is invoked with the receiver
    -- and those elements. A missing, null or undefined list gives none. The
    -- list is never iterated: this is not the spread operation.
    let B ← exprType fc callee
    let R₀ ← exprType fc receiver
    let listTy ← list.mapM (exprType fc)
    let G := SourceTypes.graph (← table)
    -- A tuple of required positions is read index by index. An array of any
    -- length goes to a signature that takes only a rest: its store's positions
    -- are the actuals, `undefined` at a hole, as `CreateListFromArrayLike`
    -- reads them; nothing here iterates.
    let (elements, dynamic) : List (Ty Nat) × Bool ← match listTy with
      | none => pure ([], false)
      | some T =>
        if nullishList G T then pure ([], false) else
        let some S := storeOf G T
          | throw (locatedRefusal (← table) e.span .bindingAnnotation
              ".apply needs an array list, or a null or undefined one")
        match PositiveRules.expand G S with
        | [.list Tp []] =>
          if Tp.optional.isEmpty && Tp.rest.isNone then pure (Tp.required, false)
          else if Tp.required.isEmpty && Tp.optional.isEmpty &&
              (ProgramTyping.restSigs G B).any (fun (_, Ps, _, _) => Ps.isEmpty) then
            pure ([], true)
          else throw (locatedRefusal (← table) e.span .bindingAnnotation
            ".apply with a list of unknown length needs a target taking only a rest parameter")
        | _ => throw (locatedRefusal (← table) e.span .bindingAnnotation
            ".apply needs an array list, or a null or undefined one")
    let reads := match listTy with
      | some T => !nullishList G T
      | none => false
    let k := elements.length
    let saved := (listTy.toList.reverse) ++ [R₀, B]
    let s := saved.length
    let N : Ty Nat := [← lower (SourceTypes.use .num)]
    -- Slots above the saved operands: the length, then each element read.
    let prepared := if reads then elements.reverse ++ [N] else []
    let p := prepared.length
    let anonymous := held ⟨"",some e.span⟩
    let operandScope := (list.toList.map fun a => held ⟨"",some a.span⟩) ++
      [held ⟨"",some receiver.span⟩, held ⟨"",some callee.span⟩]
    let callEnv := prepared ++ saved ++ Γ
    let callScope := List.replicate p anonymous ++ operandScope ++ scope
    let Rt ← if dynamic then
        let sigs := (ProgramTyping.restSigs G B).filter fun (_, Ps, _, _) => Ps.isEmpty
        match (sigs.find? fun (Rt,_,_,_) => R₀.all Rt.contains) <|> sigs.head? with
        | some (Rt,_,_,_) => pure Rt
        | none => throw ".apply target requires a rest signature"
      else do
        let L ← match PositiveRules.expand G B with
          | [.arrs L _] | [.callable _ _ L _] => pure L
          | _ => throw ".apply target requires a single callable contract"
        let (Rt,_,_) ← selectSignature G L elements R₀
        pure Rt
    let receiverIndex := p + s - 2
    let receiverCheck := DirectProof.cast callEnv Rt (DirectProof.var callEnv receiverIndex R₀)
    obligation receiver.span receiverCheck.goal (some receiverCheck) "method-receiver" callScope
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+p+s))⟩
    -- The list is the slot below the length.
    let actuals := if dynamic then [Tm.spread (.readAt SourceTypes.storeField (.var 1))]
      else (List.range k).map fun j => Tm.var (k-1-j)
    let call ← emitAt e.span (.invoke (.var (p+s-1)) (.var receiverIndex) actuals) (.bind drop)
      callEnv A (scope := callScope)
    -- The reads run in position order, after the length, so they are emitted
    -- from the last back. The list is the slot just below the length.
    let afterLength ← (List.range k).reverse.foldlM (fun next j => do
      let some E := elements[j]? | throw "an element has no contract"
      let index ← indexTerm j
      let env := (elements.take j).reverse ++ N :: saved ++ Γ
      emitAt e.span (.elemAt (.readAt SourceTypes.storeField (.var (j+1))) index) (.bind next)
        env E "apply-element"
        (scope := List.replicate (j+1) anonymous ++ operandScope ++ scope)) call
    let prepare ← if reads then
        emitAt e.span (.lenOf (.readAt SourceTypes.storeField (.var 0))) (.bind afterLength)
          (saved ++ Γ) N "apply-length" (scope := operandScope ++ scope)
      else pure call
    let afterList ← match list with
      | none => pure prepare
      | some xs => compileExpr fc (operandScope.drop 1 ++ scope) (saved.drop 1 ++ Γ) xs prepare
    let afterReceiver ← compileExpr fc (held ⟨"",some callee.span⟩ :: scope) (B::Γ) receiver afterList
    compileExpr fc scope Γ callee afterReceiver
  | .call _ callee args _ _ | .callWithReceiver _ callee _ args | .invoke _ callee args _ _ =>
    let operands := match e with
      | .callWithReceiver _ _ receiver _ => receiver :: args
      | _ => args
    let spreads := match e with
      | .call _ _ _ s _ | .invoke _ _ _ s _ => s
      | _ => []
    -- A method call saves the object, a computed key, then the method read
    -- from it; the method is the callee and the object the receiver. The
    -- saved slots sit where a plain call's one callee slot does.
    let method : Option (Fragment.Expr × Option Fragment.Expr × (Tm → Tm)) ← match e with
      | .invoke _ (.read _ fld o) _ _ typeArgs => do
        let O ← exprType fc o
        explicitInstance e.span O (← exprType fc callee) fld typeArgs
        let G := SourceTypes.graph (← table)
        pure (some (o, none, memberHead G O fld))
      | .invoke _ (.index _ (some fld) o key) _ _ typeArgs => do
        let O ← exprType fc o
        explicitInstance e.span O (← exprType fc callee) fld typeArgs
        let G := SourceTypes.graph (← table)
        pure (some (o, some key, memberHead G O fld))
      | .invoke _ (.elemAt _ o key) _ _ typeArgs => do
        if !typeArgs.isEmpty then
          throw (locatedRefusal (← table) e.span .schemeElimination
            ("explicit type arguments on an element call are outside the fragment: an element that " ++
              "is a generic closure is claimed at a quantified callable, which the claim format does not encode"))
        let K ← exprType fc key
        let index ← arrayKeyTerm K
        pure (some (o, some key, fun obj => .elemAt (.readAt SourceTypes.storeField obj) index))
      | .invoke .. => throw "a method call's target must name a field or an element"
      | _ => pure none
    let B ← exprType fc callee
    -- A method of an object of a union whose alternatives read different
    -- members, `x.toString()` on `string | number`, is read and called in
    -- one step dispatched on the object (`dispatchCallTerm`), after the
    -- actuals: so no actual may run code.
    let dispatch : Option PropKey ← match e, method, callee with
      | .invoke _ _ _ [] _, some (o, none, _), .read _ fld _ => do
        let O ← exprType fc o
        let plain : Fragment.Expr → Bool := fun a => match a with
          | .var .. | .lit .. => true
          | _ => false
        let G := SourceTypes.graph (← table)
        pure (if O.length > 1 && B.length > 1 && args.all plain
            && (ProgramTyping.restSigs G B).isEmpty then some fld else none)
      | _, _, _ => pure none
    let headTys : List (Ty Nat) ← match method, dispatch with
      | none, _ => pure [B]
      | some (o, _, _), some _ => do pure [← exprType fc o]
      | some (o, key, _), none => do
        let O ← exprType fc o
        let keyTy ← key.mapM (exprType fc)
        pure (B :: keyTy.toList ++ [O])
    let headScope := match method, dispatch with
      | none, _ => [held ⟨"",some callee.span⟩]
      | some (o, _, _), some _ => [held ⟨"",some o.span⟩]
      | some (o, key, _), none => held ⟨"",some callee.span⟩ ::
          (key.map fun k => held ⟨"",some k.span⟩).toList ++ [held ⟨"",some o.span⟩]
    let h := headTys.length
    -- Into a variadic callee a spread may be anywhere among the actuals past
    -- the fixed ones. The call reads a spread once every actual is evaluated;
    -- a spread followed by an actual that runs code is therefore copied where
    -- it is written, `[...xs]`, and the call spreads the copy, which nothing
    -- else can reach. Into fixed parameters each spread stands for a tuple's
    -- required positions, read once every actual is evaluated: no actual
    -- after the first spread may run code.
    let variadic := !(ProgramTyping.restSigs (SourceTypes.graph (← table)) B).isEmpty
    let runsCode : Fragment.Expr → Bool := fun a => match a with
      | .var .. | .lit .. => false
      | _ => true
    let copied := if variadic then spreads.filter fun i => (args.drop (i + 1)).any runsCode
      else []
    let spread := !variadic && !spreads.isEmpty
    let spreadOrder := spreads.eraseDups.mergeSort (· ≤ ·)
    if spread then
      let first := spreadOrder.headD args.length
      if (args.drop (first + 1)).any runsCode then
        throw (locatedRefusal (← table) e.span .bindingAnnotation
          "a spread into fixed parameters followed by an actual that runs code is outside the fragment")
    let As₀ ← operands.mapM (exprType fc)
    -- A dense tuple keeps its exact positions when copied. Other arrays use
    -- the existing unbounded copy rule, whose result may have holes.
    let copyTypes ← copied.mapM fun i => do
      let G := SourceTypes.graph (← table)
      let some original := As₀[i]? | throw "a spread argument needs an operand"
      if let some S := storeOf G original then
        if let [.list T []] := PositiveRules.expand G S then
          if T.optional.isEmpty && T.rest.isNone then
            return (i, S)
      let some (_, _, P, _) := (ProgramTyping.restSigs G B).head? | throw "a spread needs a variadic callee"
      let some E := PositiveRules.restElem G P
        | throw "a spread into a rest needs an element rest"
      if !E.contains 3 then
        throw (locatedRefusal (← table) e.span .bindingAnnotation
          "a spread copied before a later actual runs needs a rest element type that admits `undefined`")
      let C ← lower (SourceTypes.use (.list ⟨[], [], some E, false⟩ []))
      modify fun st => {st with hints := C :: st.hints}
      pure (i, [C])
    let As := As₀.zipIdx.map fun (A, i) =>
      (copyTypes.lookup i).getD A
    let n := As.length
    -- A spread stands for the required positions of its operand's tuple
    -- contract. Those elements are read here, after every other argument has
    -- been evaluated, which is where a call reads them; the operand is a name,
    -- so nothing is evaluated twice. No iterator of the source's own can be
    -- installed in this fragment, so the array's positions are what a spread
    -- yields (DESIGN.md, "Trust surface").
    let spreadElements : List (Nat × List (Ty Nat)) ← if !spread then pure [] else
      spreadOrder.mapM fun i => do
        let some arrayTy := As[i]? | throw "a spread argument needs an operand"
        let G := SourceTypes.graph (← table)
        let some S := storeOf G arrayTy | throw "a spread argument needs a tuple contract"
        match PositiveRules.expand G S with
        | [.list T []] =>
          if !T.optional.isEmpty || T.rest.isSome then
            throw "a spread argument needs a tuple contract of required positions"
          pure (i, T.required)
        | _ => throw "a spread argument needs a tuple contract of required positions"
    let elements := spreadElements.flatMap (·.2)
    -- Each element's operand and its position in that operand's tuple.
    let sources : List (Nat × Nat) :=
      spreadElements.flatMap fun (i, Es) => (List.range Es.length).map (i, ·)
    let k := elements.length
    let anonymous := held ⟨"",some e.span⟩
    let temporaries := (operands.map fun a => held ⟨"",some a.span⟩).reverse ++ headScope
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+n+h+k))⟩
    -- An actual sits above the elements a spread reads; a receiver, which is
    -- an operand and not an actual, sits below them all.
    -- A spread into fixed parameters is its elements, in order, where it is
    -- written.
    let actuals := ((List.range args.length).foldl (fun (g, out) i =>
        let v := Tm.var (k + args.length - 1 - i)
        match spreadElements.lookup i with
        | some Es => (g + Es.length, out ++ (List.range Es.length).map fun j => Tm.var (k-1-(g+j)))
        | none =>
          (g, out ++ [if copied.contains i then .spread v
            else if spreads.contains i && variadic then .spread (.readAt SourceTypes.storeField v)
            else v])) (0, ([] : List Tm))).2
    let callEnv := elements.reverse ++ As.reverse ++ headTys ++ Γ
    let G := SourceTypes.graph (← table)
    let callScope := (List.replicate k anonymous) ++ temporaries ++ scope
    -- The alternatives' members, as the callee's claim names them, are the
    -- types the dispatched call is typed at.
    if dispatch.isSome then modify fun st => {st with hints := B ++ st.hints}
    let dispatchArms ← match dispatch, headTys.getLast? with
      | some fld, some O => primitiveArms callScope callEnv O fld
      | _, _ => pure []
    -- `.call` passes its first operand as the receiver; a plain call passes
    -- `undefined`.
    let callTerm := match e, dispatch, headTys.getLast? with
      | .callWithReceiver .., _, _ => Tm.invoke (.var (k+n)) (.var (k+n-1)) actuals
      | .invoke .., some fld, some O => dispatchCallTerm G O dispatchArms fld (k+n) actuals
      | .invoke .., _, _ => Tm.invoke (.var (k+n)) (.var (k+n+h-1)) actuals
      | _, _, _ => Tm.call (.var (k+n)) actuals
    -- The receiver the call passes, the `.call` operand or `undefined`, is
    -- checked where the call is made at the selected signature's receiver:
    -- a located obligation, apart from the call's own typing.
    -- The receiver's selected contract: a fixed signature taking these
    -- actuals, or the variadic signature the call uses.
    let receiverOf (Rr : Ty Nat) (actualTys : List (Ty Nat)) : Option (Ty Nat) :=
      if variadic then
        let sigs := ProgramTyping.restSigs G B
        ((sigs.find? fun (Rt,_,_,_) => Rr.all Rt.contains) <|> sigs.head?).map (·.1)
      else if spread then none
      else match PositiveRules.expand G B with
        | [.arrs L _] | [.callable _ _ L _] =>
          match selectSignature G L actualTys Rr with
          | .ok (Rt,_,_) => some Rt
          | .error _ => none
        | _ => none
    match e, method with
    | .callWithReceiver _ _ r _, _ =>
      if let some R₀ := As.head? then
        if let some Rt := receiverOf R₀ (As.drop 1) then
          let plan := DirectProof.cast callEnv Rt (DirectProof.var callEnv (k+n-1) R₀)
          obligation r.span plan.goal (some plan) "method-receiver" callScope
    | .invoke .., some (o, _, _) =>
      if let some O := headTys.getLast? then
        if let some Rt := receiverOf O As then
          let plan := DirectProof.cast callEnv Rt (DirectProof.var callEnv (k+n+h-1) O)
          obligation o.span plan.goal (some plan) "method-receiver" callScope
    | _, _ =>
      if let some Rt := receiverOf [3] As then
        if !admitsUndefined G Rt then
          let plan := DirectProof.cast callEnv Rt (DirectProof.node callEnv .undef [3] .undef)
          obligation callee.span plan.goal (some plan) "method-receiver" callScope
    let call ← emitAt e.span callTerm (.bind drop) callEnv A
      (scope := (List.replicate k anonymous) ++ temporaries ++ scope)
    -- The reads run in position order, so they are emitted from the last back.
    let reads ← (List.range k).reverse.foldlM (fun next g => do
      let some E := elements[g]? | throw "a spread element has no contract"
      let some (i, j) := sources[g]? | throw "a spread element has no operand"
      let index ← indexTerm j
      let env := (elements.take g).reverse ++ As.reverse ++ headTys ++ Γ
      emitAt e.span (.elemAt (.readAt SourceTypes.storeField (.var (g + n - 1 - i))) index)
        (.bind next) env E "spread-element"
        (scope := (List.replicate g anonymous) ++ temporaries ++ scope)) call
    let right ← operands.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) => do
      let sc := (operands.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++
        headScope ++ scope
      let ctx := (As.take i).reverse ++ headTys ++ Γ
      if copied.contains i then
        -- The copy takes the operand's slot: the continuation sees the copied
        -- store where it would have seen the array.
        let some A := As₀[i]? | throw "a spread argument needs an operand"
        let m := (next.mapping.getD (List.range (ctx.length + 1))).map fun j =>
          if j == 0 then 0 else j + 1
        let some C := As[i]? | throw "a spread argument needs an operand"
        let inits ← match PositiveRules.expand (SourceTypes.graph (← table)) C with
          | [.list T []] =>
            if T.optional.isEmpty && T.rest.isNone then
              (List.range T.required.length).mapM fun j => do
                return Tm.elemAt (.readAt SourceTypes.storeField (.var 0)) (← indexTerm j)
            else pure [.spread (.readAt SourceTypes.storeField (.var 0))]
          | _ => throw "a spread copy needs an array store contract"
        let copy ← emitAt arg.span (.arrLit inits)
          (.bind ⟨next.label, some m⟩) (A :: ctx) C "spread-copy"
          (scope := held ⟨"",some arg.span⟩ :: sc)
        compileExpr fc sc ctx arg ⟨copy.label, none⟩
      else compileExpr fc sc ctx arg next) reads
    match method, dispatch with
    | none, _ => compileExpr fc scope Γ callee right
    | some (o, _, _), some _ => compileExpr fc scope Γ o right
    | some (o, key, readTerm), none =>
      -- The method is read from the saved object, below any saved key; a
      -- primitive's, by its shape (`dispatchTerm`).
      let saved := headTys.drop 1
      let objSlot := saved.length - 1
      let arms ← match callee, headTys.getLast? with
        | .read _ fld _, some O | .index _ (some fld) _ _, some O =>
          do pure (fld, ← primitiveArms (headScope.drop 1 ++ scope) (saved ++ Γ) O fld)
        | _, _ => pure ("", [])
      let term := if arms.2.isEmpty then readTerm (.var objSlot)
        else dispatchTerm arms.2 arms.1 objSlot (.readAt arms.1 (.var objSlot))
      let read ← emitAt callee.span term (.bind ⟨right.label, none⟩)
        (saved ++ Γ) B (scope := headScope.drop 1 ++ scope)
      let afterObject ← match key with
        | none => pure read
        | some key => do
          let some O := headTys.getLast? | throw "internal method call slots"
          compileExpr fc (held ⟨"",some o.span⟩ :: scope) (O::Γ) key read
      compileExpr fc scope Γ o afterObject
  | .arrayLit _ elems =>
    -- The elements, in order, then the store they fill, then the array
    -- object holding it: two nodes, so the allocation's slots are variables.
    let G := SourceTypes.graph (← table)
    let some S := storeOf G A | throw "an array literal needs an array claim"
    let As ← elems.mapM (exprType fc)
    let n := As.length
    let temporaries := (elems.map fun a => held ⟨"",some a.span⟩).reverse
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+n+1))⟩
    let makeScope := held ⟨"",some e.span⟩ :: temporaries ++ scope
    let proto ← prototypeSlot makeScope
    let O ← arrayObject S
    let [.list T []] := PositiveRules.expand G S | throw "an array literal needs one tuple contract"
    -- Both nodes' derivations are known: the object holding the store and
    -- the prototype, and the store of the elements at their positions.
    let H := S :: As.reverse ++ Γ
    let some P := H[proto]? | throw "internal prototype slot mismatch"
    let make ← emitPlanned e.span (DirectProof.node H (arrayTerm proto) O .alloc
        [DirectProof.var H 0 S, DirectProof.var H proto P]) (.bind drop) H A (scope := makeScope)
    let K := As.reverse ++ Γ
    let casts ← (List.range n).mapM fun i => do
      let some D := ProgramTyping.positionTy T i | throw "an array literal has more elements than its claim"
      let some Ai := As[i]? | throw "internal element slot mismatch"
      pure (DirectProof.cast K D (DirectProof.var K (n-1-i) Ai))
    let store ← emitPlanned e.span (DirectProof.node K (.arrLit ((List.range n).map fun i => .var (n-1-i))) S
        .arrLit casts) (.bind make) K S (scope := temporaries ++ scope)
    elems.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) =>
      compileExpr fc
        ((elems.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++ scope)
        ((As.take i).reverse ++ Γ) arg next) store
  | .elemAt _ receiver key =>
    let B ← exprType fc receiver
    let K ← exprType fc key
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    -- A string's code unit at the key's number; an array's element at its
    -- one index, from its store.
    let G := SourceTypes.graph (← table)
    let node ← if decide (Answers G B .isStr true) then
        emitAt e.span (Tm.elemAt (.var 1) (.var 0)) (.bind drop) (K::B::Γ) A (scope := temporaries)
      else do
        let index ← arrayKeyTerm K
        let .num b := index | throw "internal extraction error: an array key is a number"
        -- Planned where the receiver's contract names its store; otherwise
        -- the choice is open, and the node is searched.
        let plan? ← tryCatch (some <$> elemReadPlan G (K::B::Γ) (DirectProof.var (K::B::Γ) 1 B) b)
          (fun _ => pure none)
        match plan? with
        | some plan => emitPlanned e.span plan (.bind drop) (K::B::Γ) A (scope := temporaries)
        | none =>
          let term := Tm.elemAt (.readAt SourceTypes.storeField (.var 1)) index
          emitAt e.span term (.bind drop) (K::B::Γ) A (scope := temporaries)
    let right ← compileExpr fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key node
    compileExpr fc scope Γ receiver right
  | .elemWrite _ receiver key rhs =>
    -- The store is read, the element set, and the store written back: one
    -- write, so every alias sees the contract kept.
    let B ← exprType fc receiver
    let K ← exprType fc key
    let index ← arrayKeyTerm K
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+3))⟩
    let effects := held ⟨"",some rhs.span⟩::held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    let result ← emitAt e.span (.var 0) (.bind drop) (C::K::B::Γ) A (scope := effects)
    let write ← emitAt e.span (.writeAt SourceTypes.storeField (.var 2)
        (.setElem (.readAt SourceTypes.storeField (.var 2)) index (.var 0)))
      (.effect result) (C::K::B::Γ) [0] (scope := effects)
    let right ← compileExpr fc (held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope) (K::B::Γ) rhs write
    let middle ← compileExpr fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key right
    compileExpr fc scope Γ receiver middle
  | .index _ (some fld) receiver key =>
    let B ← exprType fc receiver
    let K ← exprType fc key
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    let arms ← primitiveArms temporaries (K::B::Γ) B fld
    let node ← emitAt e.span (dispatchTerm arms fld 1 (.readAt fld (.var 1))) (.bind drop) (K::B::Γ) A
      (scope := temporaries)
    let right ← compileExpr fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key node
    compileExpr fc scope Γ receiver right
  | .index _ none receiver key =>
    let B ← exprType fc receiver
    let K ← exprType fc key
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    -- A key of string or number singletons reads, per singleton, the member
    -- its key names, as a literal key does (`keyedReadTerm`); any other key
    -- reads through an index.
    let G := SourceTypes.graph (← table)
    let term ← match keySingletons G K with
      | some keys => do
        let reads ← keys.mapM fun (tag, fld) => do
          let arms ← primitiveArms temporaries (K::B::Γ) B fld
          pure (tag, dispatchTerm arms fld 1 (.readAt fld (.var 1)))
        pure (keyedReadTerm reads 0)
      | none => pure (.indexAt (.var 1) (.var 0))
    let node ← emitAt e.span term (.bind drop) (K::B::Γ) A
      (scope := temporaries)
    let right ← compileExpr fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key node
    compileExpr fc scope Γ receiver right
  | .indexWrite _ (some fld) receiver key rhs =>
    let B ← exprType fc receiver
    let K ← exprType fc key
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+3))⟩
    let effects := held ⟨"",some rhs.span⟩::held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    let result ← emitAt e.span (.var 0) (.bind drop) (C::K::B::Γ) A (scope := effects)
    let write ← emitAt e.span (.writeAt fld (.var 2) (.var 0)) (.effect result) (C::K::B::Γ) [0]
      (scope := effects)
    let right ← compileExpr fc (held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope) (K::B::Γ) rhs write
    let middle ← compileExpr fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key right
    compileExpr fc scope Γ receiver middle
  | .arith _ op l r =>
    let B ← exprType fc l
    let C ← exprType fc r
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some r.span⟩::held ⟨"",some l.span⟩ :: scope
    let node ← emitAt e.span (.arith op (.var 1) (.var 0)) (.bind drop) (C::B::Γ) A (scope := temporaries)
    let right ← compileExpr fc (held ⟨"",some l.span⟩ :: scope) (B::Γ) r node
    compileExpr fc scope Γ l right
  | .inKeys p key o =>
    -- The key, then the object, then the test of the key's singleton.
    let B ← exprType fc key
    let C ← exprType fc o
    inOperand p (.hasKey (.str "")) C
    let keys ← inKeyList p B
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some o.span⟩::held ⟨"",some key.span⟩ :: scope
    let node ← emitAt e.span (inKeysTerm keys 1 0) (.bind drop) (C::B::Γ) A (scope := temporaries)
    let right ← compileExpr fc (held ⟨"",some key.span⟩ :: scope) (B::Γ) o node
    compileExpr fc scope Γ key right
  | .comma _ l r =>
    -- The left operand, held and never read, then the right one, whose value
    -- the comma's claim is proved from.
    let B ← exprType fc l
    let C ← exprType fc r
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some r.span⟩::held ⟨"",some l.span⟩ :: scope
    let node ← emitAt e.span (.var 0) (.bind drop) (C::B::Γ) A "comma" (scope := temporaries)
    let right ← compileExpr fc (held ⟨"",some l.span⟩ :: scope) (B::Γ) r node
    compileExpr fc scope Γ l right
  | .unary _ .typeof a =>
    -- The operand, then its `typeof`, one tag test per answer.
    let B ← exprType fc a
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let node ← emitAt e.span (typeofTerm 0) (.bind drop) (B::Γ) A
      (scope := held ⟨"",some a.span⟩ :: scope)
    compileExpr fc scope Γ a node
  | .unary pos op a =>
    -- The operand, then the constant of its family, then the operator.
    let B ← exprType fc a
    let (arith, c, C, _) ← unaryOperation pos op B
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some e.span⟩::held ⟨"",some a.span⟩ :: scope
    let node ← emitAt e.span (.arith arith (.var 1) (.var 0)) (.bind drop) (C::B::Γ) A (scope := temporaries)
    let constant ← emitAt e.span c (.bind node) (B::Γ) C (scope := held ⟨"",some a.span⟩ :: scope)
    compileExpr fc scope Γ a constant
  | .update _ op target rhs post =>
    -- The target's parts are evaluated once and its value read at the
    -- storage contract, never at a claim; then the right side, the
    -- operation, the write back at the contract, and the old or new value.
    let G := SourceTypes.graph (← table)
    -- The field's contract, of the one record the target's object is: its
    -- views, methods and key bounds say nothing of the field.
    let fieldType := fun (B : Ty Nat) (fld : PropKey) => do
      match PositiveRules.expand G B with
      | [.refs fs [] _ _ _ _] =>
        let some T := fs.lookup fld
          | throw (locatedRefusal (← table) e.span .storageWrite
              s!"update of a field '{fld}' the contract does not name as a writable location")
        pure T
      | _ => throw (locatedRefusal (← table) e.span .storageWrite "a compound assignment needs one cell contract")
    let (parts, T, readTerm, receiverSlot, fld) ← match target with
      | .var _ name =>
        let some (i, .cell contract _) := resolve scope name
          | throw s!"assignment to '{name}', which is not a mutable local"
        pure (([] : List Fragment.Expr), contract, Tm.readAt valueField (.var i), i+3, valueField)
      | .read _ fld receiver =>
        let B ← exprType fc receiver
        let T ← fieldType B fld
        pure ([receiver], T, Tm.readAt fld (.var 0), 3, fld)
      | .index _ (some fld) receiver key =>
        let B ← exprType fc receiver
        let T ← fieldType B fld
        pure ([receiver, key], T, Tm.readAt fld (.var 1), 4, fld)
      | _ => throw "only field and local assignments are supported"
    let types ← parts.mapM (exprType fc)
    let heldParts := (parts.map fun p => held ⟨"",some p.span⟩).reverse
    let K := types.reverse ++ Γ
    -- The operation's value is a string for `+` with a string operand, else
    -- of the target contract's numeric family, and an increment adds that
    -- family's one.
    let targetClauses := PositiveRules.expand (SourceTypes.graph (← table)) T
    -- `x++` converts its operand to a number, where `x + 1` would
    -- concatenate a string: an increment is this addition only on a target of
    -- one numeric family.
    if rhs.isNone && (targetClauses.isEmpty ||
        !(targetClauses.all ProgramTyping.numberClause || targetClauses.all ProgramTyping.bigintClause)) then
      throw s!"unsupported source expression at [{e.span.1},{e.span.2}): an increment needs a target of one numeric family, number or bigint"
    let (one, oneClause) : Tm × PositiveNormalization.Clause (List Nat) :=
      if !targetClauses.isEmpty && targetClauses.all ProgramTyping.bigintClause
      then (.bigint 1, .bigintLit 1) else (.num (1.0 : Float).toBits, .numLit (1.0 : Float).toBits)
    let C ← match rhs with
      | some r => exprType fc r
      | none => do pure [← lower (SourceTypes.use oneClause)]
    let N ← operatorResult op T C
    let n := parts.length
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+n+3))⟩
    let after := held ⟨"",some e.span⟩::held ⟨"",some e.span⟩::held ⟨"",some e.span⟩ :: heldParts ++ scope
    let result ← emitAt e.span (.var (if post then 2 else 0)) (.bind drop) (N::C::T::K) A (scope := after)
    let write ← emitAt e.span (.writeAt fld (.var receiverSlot) (.var 0)) (.effect result) (N::C::T::K) [0]
      "storage-contract" (scope := after)
    let combine ← emitAt e.span (.arith op (.var 1) (.var 0)) (.bind write) (C::T::K) N
      (scope := after.drop 1)
    let delta ← match rhs with
      | some r => compileExpr fc (after.drop 2) (T::K) r combine
      | none => emitAt e.span one (.bind combine) (T::K) C (scope := after.drop 2)
    let read ← emitAt e.span readTerm (.bind delta) K T (scope := heldParts ++ scope)
    parts.attach.zipIdx.reverse.foldlM (fun next (⟨part,_⟩,i) =>
      compileExpr fc ((parts.take i |>.map fun p => held ⟨"",some p.span⟩).reverse ++ scope)
        ((types.take i).reverse ++ Γ) part next) read
  | .logicalAssign pos .nullish (.var np name) rhs =>
    compileExpr fc scope Γ (.nullishAssign pos name np rhs) next
  | .logicalAssign pos op target rhs =>
    -- The target's parts once, its value read at the storage contract, the
    -- test on that value, and the right side written only on the writing
    -- arm; the other arm's value is the one read.
    let G := SourceTypes.graph (← table)
    let fieldType := fun (B : Ty Nat) (fld : PropKey) => do
      match PositiveRules.expand G B with
      | [.refs fs [] _ _ _ _] =>
        let some T := fs.lookup fld
          | throw (locatedRefusal (← table) pos .storageWrite
              s!"update of a field '{fld}' the contract does not name as a writable location")
        pure T
      | _ => throw (locatedRefusal (← table) pos .storageWrite "a logical assignment needs one cell contract")
    let (parts, T, readTerm, receiverSlot, fld) ← match target with
      | .var _ name =>
        let some (i, .cell contract _) := resolve scope name
          | throw s!"assignment to '{name}', which is not a mutable local"
        pure (([] : List Fragment.Expr), contract, Tm.readAt valueField (.var i), i+2, valueField)
      | .read _ fld receiver =>
        let B ← exprType fc receiver
        let T ← fieldType B fld
        pure ([receiver], T, Tm.readAt fld (.var 0), 2, fld)
      | .index _ (some fld) receiver key =>
        let B ← exprType fc receiver
        let T ← fieldType B fld
        pure ([receiver, key], T, Tm.readAt fld (.var 1), 3, fld)
      | _ => throw "only field and local assignments are supported"
    let types ← parts.mapM (exprType fc)
    let heldParts := (parts.map fun p => held ⟨"",some p.span⟩).reverse
    let K := types.reverse ++ Γ
    let C ← exprType fc rhs
    let n := parts.length
    -- The arms' slices of the read value: the writing arm's and the kept one's.
    if op != .nullish && !decide (Answers G T .isBool true) then
      throw "a logical assignment needs a Boolean target"
    let (writes, keeps) : Ty Nat × Ty Nat := match op with
      | .nullish => (BranchRefinement.tagSlice G T .isNullish true, BranchRefinement.tagSlice G T .isNullish false)
      | .orElse => ([2], [1])
      | .andAlso => ([1], [2])
    let saved := held ⟨"",some pos⟩ :: heldParts ++ scope
    let dropKeep := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun j => if j == 0 then 0 else j+n+1))⟩
    let keep ← emitAt pos (.var 0) (.bind dropKeep) (keeps::K) A (scope := saved)
    let effects := held ⟨"",some rhs.span⟩ :: saved
    let dropWrite := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun j => if j == 0 then 0 else j+n+2))⟩
    let result ← emitAt pos (.var 0) (.bind dropWrite) (C::writes::K) A (scope := effects)
    let write ← emitAt pos (.writeAt fld (.var receiverSlot) (.var 0)) (.effect result)
      (C::writes::K) [0] "storage-contract" (scope := effects)
    let yes ← compileExpr fc saved (writes::K) rhs write
    -- The dispatch introduces a refined copy of the read; discard the older one.
    let adapt := fun (t : Target) =>
      ⟨t.label, some ((t.mapping.getD (List.range (K.length+1))).map
        (fun j => if j == 0 then 0 else j+1))⟩
    let continuation : Continuation := match op with
      | .nullish => .tagBind .isNullish (adapt yes) (adapt keep)
      | .orElse => .branchBind (adapt keep) (adapt yes)
      | .andAlso => .branchBind (adapt yes) (adapt keep)
    let dispatch ← emitAt pos (.var 0) continuation (T::K) T "logical-assignment-dispatch" (scope := saved)
    let read ← emitAt pos readTerm (.bind dispatch) K T (scope := heldParts ++ scope)
    parts.attach.zipIdx.reverse.foldlM (fun next (⟨part,_⟩,i) =>
      compileExpr fc ((parts.take i |>.map fun p => held ⟨"",some p.span⟩).reverse ++ scope)
        ((types.take i).reverse ++ Γ) part next) read
  | .indexWrite _ none .. => throw "internal unresolved computed key"
  | .write _ fld receiver rhs =>
    let B ← exprType fc receiver
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    -- JS assignment returns its evaluated RHS; the calculus write returns null.
    let effects := held ⟨"",some rhs.span⟩::held ⟨"",some receiver.span⟩ :: scope
    let result ← emitAt e.span (.var 0) (.bind drop) (C::B::Γ) A (scope := effects)
    let write ← emitAt e.span (.writeAt fld (.var 1) (.var 0)) (.effect result) (C::B::Γ) [0]
      (scope := effects)
    let right ← compileExpr fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) rhs write
    compileExpr fc scope Γ receiver right

/-- Compile compound conditions as short-circuit edges. The full source
expression still has an independent claimed typing obligation; the runtime
traverses its operands once instead of evaluating it and then replaying it. -/
private partial def compileCondition (fc : SourceClaims.Function) (scope : List ScopeBinding)
    (Γ : List (Ty Nat)) (cond : Fragment.Expr) (yes no : Target) : Compiler Target := do
  let simple := do
    let A ← exprType fc cond
    if let some (snapshot, read, tested) := readGuard scope cond then
      -- Preserve the tested read until tag dispatch, so its heap link can
      -- justify the branch's current-content assertion. The singleton literal
      -- has no effects; every source operand still has its typing obligation.
      let B ← exprType fc read
      let ds := held ⟨snapshot,some read.span⟩ :: scope
      let K := B :: Γ
      let lift := fun (t : Target) =>
        ⟨t.label, some ((t.mapping.getD (List.range scope.length)).map (·+1))⟩
      let node ← emitBranch ds K tested A (lift yes) (lift no)
      let predicate ← compileExpr fc ds K tested node
      compileExpr fc scope Γ read predicate
    else
      let node ← emitBranch scope Γ cond A yes no
      compileExpr fc scope Γ cond node
  -- For each singleton the split operand may be, in order: it is that one,
  -- and the other operand is too (strict equality is transitive where it
  -- holds). After every one failed, the split operand equals none of them
  -- (NaN, which equals nothing), so the operands differ. A test of a field
  -- read reads it again, which nothing between has written, and records its
  -- link, which lets the edge refine the object's arms (`fieldSlice`) and
  -- tells what the field holds.
  let dispatch := fun (p : Span) (scope : List ScopeBinding) (Γ : List (Ty Nat))
      (split other : SplitOperand) (tags : List Tag) (yes no : Target) => do
    let G := SourceTypes.graph (← table)
    let width := scope.length
    let test := fun (Δ : List (Ty Nat)) (op : SplitOperand) (tag : Tag) (y n : Target) =>
      match op with
      | ((k, none), _) =>
        emitAt p (.var k) (.tagBind tag (branchMapping width (some k) y) (branchMapping width (some k) n))
          Δ (Δ[k]?.getD []) "tag-dispatch" (scope := scope)
      | ((k, some f), e) => do
        -- The read is saved and its copy tested, as a guard's saved read is:
        -- the copy states what the value is, and its link what the field holds.
        let R ← exprType fc e
        let drop := fun (t : Target) =>
          (⟨t.label, some ((t.mapping.getD (List.range width)).map (·+2))⟩ : Target)
        let dispatchNode ← emitAt p (.var 0) (.tagBind tag (drop y) (drop n)) (R::Δ) R "tag-dispatch"
          (scope := held ⟨"",some e.span⟩ :: scope)
        emitAt p (.readAt f (.var k)) (.bind dispatchNode) Δ R "tag-dispatch" (scope := scope)
    let refine := fun (Δ : List (Ty Nat)) (op : SplitOperand) (tag : Tag) (q : Bool) =>
      match op.1 with
      | (k, none) => Δ.set k (BranchRefinement.tagSlice G (Δ[k]?.getD []) tag q)
      | (k, some f) => Δ.set k (BranchRefinement.fieldSlice G (Δ[k]?.getD []) f tag q)
    let rec chain : List Tag → List (Ty Nat) → Compiler Target
      | [], _ => pure no
      | tag :: more, Δ => do
        -- Where the other operand cannot be this singleton, its test's true
        -- edge is never taken; it goes where the false one does, so that
        -- no target claims what the split operand holds on that path.
        let possible ← match other with
          | ((k, none), _) => pure !(BranchRefinement.tagSlice G ((refine Δ split tag true)[k]?.getD []) tag true).isEmpty
          | ((_, some _), e) => do
            pure !(BranchRefinement.tagSlice G (← exprType fc e) tag true).isEmpty
        let inner ← test (refine Δ split tag true) other tag (if possible then yes else no) no
        let next ← chain more (refine Δ split tag false)
        test Δ split tag inner next
    chain tags Γ
  match cond with
  | .arith p .eq l r =>
    match ← equalitySplit fc scope Γ l r with
    | some (split, other, tags) =>
      let start ← dispatch p scope Γ split other tags yes no
      -- The comparison itself runs first, as the source has it, with its
      -- obligations; its Boolean is dropped, and the dispatch re-reads the
      -- operands, which nothing between has written.
      let A ← exprType fc cond
      let width := scope.length
      let skip : Target := ⟨start.label, some ((start.mapping.getD (List.range width)).map (·+1))⟩
      let discard ← emitAt p (.var 0) (.effect skip) (A::Γ) A (scope := held ⟨"",some p⟩ :: scope)
      compileExpr fc scope Γ cond discard
    | none =>
      match ← savedSplit fc scope l r with
      | none => simple
      | some (k, name, e, tags) =>
        -- The comparison's own claim is a supplemental obligation; the
        -- operand is evaluated once, into a slot above the scope, and the
        -- name, which no effect changes, is read where it is.
        let _ ← closureExpr fc scope Γ cond
        let C ← exprType fc e
        let lift := fun (t : Target) =>
          ⟨t.label, some ((t.mapping.getD (List.range scope.length)).map (·+1))⟩
        let inner := held ⟨"",some e.span⟩ :: scope
        let start ← dispatch p inner (C::Γ) (((0, none)), e) (((k+1, none)), name) tags (lift yes) (lift no)
        compileExpr fc scope Γ e start
  | .logical _ andOp left right =>
    let _ ← closureExpr fc scope Γ cond
    let H := conditionContext (SourceTypes.graph (← table)) scope Γ left andOp
    let rhs ← compileCondition fc scope H right yes no
    compileCondition fc scope Γ left (if andOp then rhs else yes) (if andOp then no else rhs)
  | .not _ e =>
    let _ ← closureExpr fc scope Γ cond
    compileCondition fc scope Γ e no yes
  | .read p f (.var _ name) =>
    -- The truthiness of a field of an immutable binding's object, where some
    -- arm of it leaves the field optional or unnamed, so that no fact about
    -- what the field holds is claimed (`IteratorResult` on `done`): the read,
    -- then a truthiness dispatch on its value, whose link to the field
    -- refines the object's arms on each edge (`fieldSlice`), as a
    -- discriminated union's are by a singleton test.
    match valueSlot scope name with
    | some k =>
      let G := SourceTypes.graph (← table)
      let T := Γ[k]?.getD []
      let fixes := fun (a : Nat) => (PositiveRules.expand G [a]).all fun c => match c with
        | .refs fs _ vs .. => (fs ++ vs).any (·.1 == f)
        | _ => false
      let refines := [true, false].any fun q =>
        (BranchRefinement.fieldSlice G T f .truthy q).length != T.length
      if refines && !T.all fixes then
        let A ← exprType fc cond
        let width := scope.length
        let drop := fun (t : Target) =>
          (⟨t.label, some ((t.mapping.getD (List.range width)).map (·+2))⟩ : Target)
        let dispatchNode ← emitAt p (.var 0) (.tagBind .truthy (drop yes) (drop no)) (A::Γ) A "tag-dispatch"
          (scope := held ⟨"",some p⟩ :: scope)
        emitAt p (.readAt f (.var k)) (.bind dispatchNode) Γ A "tag-dispatch" (scope := scope)
      else simple
    | none => simple
  | _ => simple
/-- A read that binds: `term`, at type `R` under `Γ`, becomes the binding
`bound` above the scope. One with a default dispatches on the read being
undefined: the default is compiled only on that arm, the defined slice of the
read is the other, and both arms join at a node typed by their union, which
every incoming edge must establish. `next` compiles what follows, given the
type the binding holds. -/
private partial def readWithDefault (fc : SourceClaims.Function) (pos namePos : Span) (term : Tm)
    (R : Ty Nat) (default_ : Option Fragment.Expr) (bound : ScopeBinding)
    (scope : List ScopeBinding) (Γ : List (Ty Nat)) (next : Ty Nat → Compiler Target) :
    Compiler Target := do
  let G := SourceTypes.graph (← table)
  match default_ with
  | none =>
    let next ← next R
    emitAt namePos term (.bind next) Γ R "pattern-read" (some pos.1) (scope := scope)
  | some d =>
    let D ← exprType fc d
    let R ← byClause R
    let present := BranchRefinement.tagSlice G R .isUndef false
    let T := (present ++ D).eraseDups
    let next ← next T
    -- A merge has no unique predecessor: each arm proves the binding's type.
    let join ← emitAt namePos .nul (.effect next) (T::Γ) [0] "pattern-default-join" (some pos.1)
      (scope := bound::scope)
    -- The undefined read is dropped before the default is evaluated; its
    -- value is what the arm binds.
    let fallback ← compileExpr fc scope Γ d join
    let yes : Target := ⟨fallback.label, some ((fallback.mapping.getD (List.range Γ.length)).map (·+1))⟩
    -- tagBind introduces a refined copy; discard the older read.
    let adapt := fun (t : Target) =>
      ⟨t.label, some ((t.mapping.getD (List.range (Γ.length+1))).map
        (fun j => if j == 0 then 0 else j+1))⟩
    let dispatch ← emitAt namePos (.var 0) (.tagBind .isUndef (adapt yes) (adapt join))
      (R::Γ) R "pattern-default-dispatch" (some pos.1) (scope := held ⟨"",some namePos⟩ :: scope)
    emitAt namePos term (.bind dispatch) Γ R "pattern-read" (some pos.1) (scope := scope)

/-- The writes an array assignment performs, left to right, over the right
side held at slot `obj`: each position is read, defaulted, and written to its
mutable local, whose storage contract the write must meet. `after` compiles
what follows, under the environment the reads started from. -/
private partial def arrayAssigns (fc : SourceClaims.Function) (pos : Span) (A : Ty Nat)
    (rest : Option (Span × Bool × Fragment.ArrayElem Fragment.Expr)) (after : Target) :
    List ScopeBinding → List (Ty Nat) → Nat → List (Fragment.ArrayElem Fragment.Expr) → Compiler Target
  | scope, Γ, obj, [] => do
    -- The rest's fresh array, written to its mutable local: a slice's by
    -- its `%RestFrom:k%`, any other's by reads.
    let some (restPos, slice, q) := rest | pure after
    if slice then
      let C ← claimAt fc restPos
      let call ← sliceCall scope obj q.index
      let arrayScope := held ⟨"",some restPos⟩ :: scope
      let some (i, .cell ..) := resolve scope q.name
        | throw s!"assignment to '{q.name}', which is not a mutable local"
      let dropped : Target := ⟨after.label, some ((after.mapping.getD (List.range Γ.length)).map (·+1))⟩
      let write ← emitAt q.namePos (.writeAt valueField (.var (i+1)) (.var 0)) (.effect dropped)
        (C::Γ) [0] "storage-contract" (some pos.1) (scope := arrayScope)
      return ← emitAt restPos call (.bind write) Γ C "pattern-rest" (some pos.1) (scope := scope)
    let (store, Sr, C) ← restArray fc A obj q.index restPos
    let storeScope := held ⟨"",some restPos⟩ :: scope
    let arrayScope := held ⟨"",some restPos⟩ :: storeScope
    let some (i, .cell ..) := resolve scope q.name
      | throw s!"assignment to '{q.name}', which is not a mutable local"
    let dropped : Target := ⟨after.label, some ((after.mapping.getD (List.range Γ.length)).map (·+2))⟩
    let write ← emitAt q.namePos (.writeAt valueField (.var (i+2)) (.var 0)) (.effect dropped)
      (C::Sr::Γ) [0] "storage-contract" (some pos.1) (scope := arrayScope)
    let proto ← prototypeSlot storeScope
    let object ← emitAt restPos (arrayTerm proto) (.bind write) (Sr::Γ) C "pattern-rest" (some pos.1)
      (scope := storeScope)
    emitAt restPos store (.bind object) Γ Sr "pattern-rest" (some pos.1) (scope := scope)
  | scope, Γ, obj, q :: more => do
    let R ← positionRead (SourceTypes.graph (← table)) A q.index
    let bound := held ⟨"",some q.namePos⟩
    let term := Tm.elemAt (.readAt SourceTypes.storeField (.var obj)) (.num (bitsOfNat q.index))
    readWithDefault fc pos q.namePos term R q.default_ bound scope Γ fun T => do
      let some (i, .cell ..) := resolve (bound::scope) q.name
        | throw s!"assignment to '{q.name}', which is not a mutable local"
      let rest ← arrayAssigns fc pos A rest after scope Γ obj more
      let dropped : Target := ⟨rest.label, some ((rest.mapping.getD (List.range Γ.length)).map (·+1))⟩
      emitAt q.namePos (.writeAt valueField (.var i) (.var 0)) (.effect dropped) (T::Γ) [0]
        "storage-contract" (some pos.1) (scope := bound::scope)

/-- Binds `target` to the value `term` reads under `Γ` at `R`, `default_`
replacing it where it is undefined (`readWithDefault`): a name binds it; a
nested pattern holds it in an anonymous slot, destructures it, and drops it.
`after` compiles what follows, given the scope and context with the
pattern's bindings added, innermost first. -/
private partial def bindTarget (fc : SourceClaims.Function) (pos : Span)
    (target : Fragment.Pattern Fragment.Expr) (term : Tm) (R : Ty Nat) (default_ : Option Fragment.Expr)
    (scope : List ScopeBinding) (Γ : List (Ty Nat))
    (after : List ScopeBinding → List (Ty Nat) → Compiler Target) : Compiler Target := do
  match target with
  | .name n namePos =>
    if n == "undefined" then throw "shadowing undefined is outside the fragment"
    if (names scope).contains n then throw s!"duplicate or shadowing local declaration '{n}'"
    let bound := held ⟨n,some pos⟩
    readWithDefault fc pos namePos term R default_ bound scope Γ
      fun T => after (bound::scope) (T::Γ)
  | .object p _ _ | .array p _ _ =>
    let bound := held ⟨"",some p⟩
    readWithDefault fc pos p term R default_ bound scope Γ fun T =>
      destructureAt fc pos target (bound::scope) (T::Γ) 0 fun scope' Γ' =>
        dropSlot (scope'.length - scope.length - 1) after scope' Γ'

/-- The bindings an object or array pattern yields, left to right, over the
value held at slot `obj`. An object pattern's property reads its field as
`readCell` reads it; an array pattern's element reads its position of the
store (`positionRead`): the array's own iterator, stepped, reads the current
length and the next index, and a default runs between two steps as it does
here. A rest collects the positions after the elements into a fresh array,
where the source is a tuple of required positions: that array is a literal of
reads, claimed at the rest's span like an array literal. `after` compiles what
follows, the value's slot still held below the new bindings. -/
private partial def destructureAt (fc : SourceClaims.Function) (pos : Span)
    (target : Fragment.Pattern Fragment.Expr) (scope : List ScopeBinding) (Γ : List (Ty Nat)) (obj : Nat)
    (after : List ScopeBinding → List (Ty Nat) → Compiler Target) : Compiler Target := do
  let some A := Γ[obj]? | throw "internal pattern slot mismatch"
  -- Each element's bindings sit above the ones before it, so the value's slot
  -- moves up by as many as the element bound.
  let rec elems (scope : List ScopeBinding) (Γ : List (Ty Nat)) (obj : Nat)
      (read : Nat → Nat × Fragment.Pattern Fragment.Expr × Option Fragment.Expr → Compiler (Tm × Ty Nat))
      (last : List ScopeBinding → List (Ty Nat) → Nat → Compiler Target) :
      List (Nat × Fragment.Pattern Fragment.Expr × Option Fragment.Expr) → Compiler Target
    | [] => last scope Γ obj
    | e :: more => do
      let (term, R) ← read obj e
      bindTarget fc pos e.2.1 term R e.2.2 scope Γ fun scope' Γ' =>
        elems scope' Γ' (obj + (scope'.length - scope.length)) read last more
  match target with
  | .name .. => throw "internal: a name is bound, not destructured"
  | .object _ props rest =>
    elems scope Γ obj (fun obj (i, _, _) => do
        let some (fld, _, _) := props[i]? | throw "internal pattern property"
        let G := SourceTypes.graph (← table)
        noMethodRead G A fld
        let plan ← readCell G Γ fld (DirectProof.var Γ obj A)
        pure (Tm.readAt fld (.var obj), plan.type))
      (fun scope Γ obj => match rest with
        | none => after scope Γ
        | some (restPos, t) => do
          -- The source's other own enumerable properties, copied onto a
          -- fresh object: a merge dropping the keys the properties name,
          -- bound as the rest's value at its claim.
          let drop := props.map fun (fld, _, _) => PropKey.str fld
          let E ← groupType [] []
          let _ ← mergeType E A drop
          let C ← claimAt fc restPos
          bindTarget fc pos t (.merge drop (.makeAt .absent [] []) (.var obj)) C none scope Γ after)
      (props.zipIdx.map fun ((_, t, d), i) => (i, t, d))
  | .array _ positions rest =>
    elems scope Γ obj (fun obj (i, _, _) => do
        let R ← positionRead (SourceTypes.graph (← table)) A i
        pure (Tm.elemAt (.readAt SourceTypes.storeField (.var obj)) (.num (bitsOfNat i)), R))
      (fun scope Γ obj => match rest with
        | none => after scope Γ
        | some (start, restPos, true, t) => do
          -- A slice: its `%RestFrom:k%` on the array, bound as the rest's value.
          let C ← claimAt fc restPos
          bindTarget fc pos t (← sliceCall scope obj start) C none scope Γ after
        | some (start, restPos, false, t) => do
          let (store, Sr, C) ← restArray fc A obj start restPos
          let storeScope := held ⟨"",some restPos⟩ :: scope
          let proto ← prototypeSlot storeScope
          -- The store, then the array holding it, bound as the rest's value.
          let next ← bindTarget fc pos t (arrayTerm proto) C none storeScope (Sr::Γ)
            fun scope' Γ' => dropSlot (scope'.length - scope.length - 1) after scope' Γ'
          emitAt restPos store (.bind next) Γ Sr "pattern-rest" (some pos.1) (scope := scope))
      positions

/-- The declarators of a `const`, bound left to right under the one entry `Γ`
the producer states for the statement: each initializer is compiled in the
scope the earlier bindings extend, and no cut separates them, because the
producer states none. `after` compiles what follows the whole statement. -/
private partial def constants (fc : SourceClaims.Function) (pos : Span)
    (after : List ScopeBinding → Compiler Target) :
    List ScopeBinding → List (Ty Nat) → List Fragment.Binding → Compiler Target
  | scope, _, [] => after scope
  | scope, Γ, b :: more => do
    if b.name == "undefined" then throw "shadowing undefined is outside the fragment"
    if (names scope).contains b.name then throw s!"duplicate or shadowing local declaration '{b.name}'"
    let A ← exprType fc b.init
    let B ← match b.annot with | none => pure A | some ty => lower (Fragment.translate ty)
    let fresh := match b.init with | .alloc .. | .arrayLit .. => true | _ => false
    let bound : ScopeBinding := { source := ⟨b.name,some pos⟩, fresh := fresh }
    let next ← constants fc pos after (bound::scope) (A::Γ) more
    let annotation ← emitAt b.init.span (.var 0) (.effect next) (A::Γ) B "binding-annotation" (some pos.1)
      (scope := held ⟨b.name,some b.init.span⟩::scope)
    compileExpr fc scope Γ b.init annotation

/-- The declarators of a `let`, each allocating its own private cell, in the
same left-to-right order under the statement's one entry. An unannotated
binding's contract is read at `next`, the entry of the statement that follows
the whole list: the first place every binding of the list stands in scope. -/
private partial def mutables (fc : SourceClaims.Function) (pos : Span) (next : Option Nat)
    (after : List ScopeBinding → Compiler Target) :
    List ScopeBinding → List (Ty Nat) → List Fragment.Binding → Compiler Target
  | scope, _, [] => after scope
  | scope, Γ, b :: more => do
    if b.name == "undefined" then throw "shadowing undefined is outside the fragment"
    if (names scope).contains b.name then throw "shadowing is outside the fragment"
    let A ← exprType fc b.init
    let contract ← match b.annot with
      | some ty => lower (Fragment.translate ty)
      -- An inferred binding still has a stated contract: the type the
      -- producer gives the name where it first stands in scope, before
      -- anything has narrowed it. It is supplied and then checked like a
      -- written one — every assignment against it, the initializer too —
      -- rather than the initializer's own type being taken for it.
      | none =>
        -- Only the next statement in this lexical block sees this binding
        -- immediately after initialization. Searching all environments by
        -- name can pick a different declaration in a sibling block, or a
        -- later narrowing when the producer reorders its entries.
        -- A declaration that ends its block has no statement after it to
        -- read the binding: any contract every write is checked against
        -- serves, and the initializer's claimed type is the one it meets.
        let some start := next | pure A
        let some candidate := (fc.envs.lookup start).bind (·.lookup b.name)
          | throw s!"no claimed storage contract for '{b.name}' at {start}"
        (SourceClaims.resolve (← table).length candidate).mapError fun msg =>
          s!"storage contract for '{b.name}' at {start}: {msg}"
    let reference ← lower (do return [← CellClaims.reference [(valueField, contract)]])
    -- The slot holds the identity of a cell only this lowering allocated.
    -- Storage is decided here, by the declaration, and nowhere else.
    let binding : ScopeBinding := { source := ⟨b.name,some pos⟩, storage := .cell contract reference }
    let binding := { binding with apart := some Γ }
    let continued ← mutables fc pos next after (binding::scope) (reference::Γ) more
    let drop := ⟨continued.label, some ((continued.mapping.getD (List.range (Γ.length+1))).map
      (fun j => if j == 0 then 0 else j+1))⟩
    let allocation ← emitAt b.init.span (.makeAt .absent [valueField] [.var 0]) (.bind drop) (A::Γ) reference
      "binding-allocation" (some pos.1) (scope := held ⟨"",some b.init.span⟩ :: scope)
    -- The initializer meets the storage contract, or the declaration fails
    -- here rather than being admitted at the initializer's narrower type.
    let stored ← emitAt b.init.span (.var 0) (.effect allocation) (A::Γ) contract
      "storage-contract" (some pos.1) (scope := held ⟨"",some b.init.span⟩ :: scope)
    compileExpr fc scope Γ b.init stored

/-- Compile the continuation once, then point both arms at it. Allocation order
is intentionally independent of source order; `start` records the real entry.
Fuel bounds structural traversal, not execution or certificate search. -/
private partial def body : Nat → SourceClaims.Function → Ty Nat → List ScopeBinding → List Fragment.Stmt →
    Option (Target × List ScopeBinding) → LoopTargets → Compiler Target
  | 0, _, _, _, _, _, _ => throw "internal extraction error: exhausted structural traversal"
  | fuel+1, fc, R, scope, stmts, tail, loopTargets => do
    let target ← match stmts with
    | [] => leave fc.namePos R scope tail
    | .brk pos _ :: rest | .cont pos :: rest =>
      if !rest.isEmpty then throw "statements after break or continue are outside the fragment"
      let Γ ← env fc pos.1 scope
      let destination ← match stmts, loopTargets.loop with
        | .brk _ (some l) :: _, _ => match loopTargets.labels.lookup l with
          | some done => pure done
          | none => throw s!"break to '{l}' outside a block of that label"
        | .brk _ none :: _, some (_, done) => pure done
        | .cont _ :: _, some (again, _) => pure (some again)
        | _, _ => throw "break or continue outside a source loop"
      -- The `finally` blocks between the jump and its target, innermost
      -- first: the jump runs each, in its `try`'s context, before it lands,
      -- as a `return` does. One that itself jumps, returns or throws leaves
      -- by its own way instead.
      let depth := match stmts with
        | .brk _ (some l) :: _ => (loopTargets.labelDepths.lookup l).getD 0
        | _ => loopTargets.loopDepth
      let fins := loopTargets.finalizers
      let passed := fins.take (fins.length - depth)
      -- A jump whose entry claims a binding of the empty type is never
      -- reached (every incoming edge proves that claim): it completes the
      -- function instead, which it may claim at any result.
      if Γ.any (·.isEmpty) then
        emitAt pos .undef .ret Γ R "unreachable" (scope := scope)
      else
        -- The outermost passed `finally` completes into the destination;
        -- each inner one into the next outer one's entry.
        let mut after := destination
        for i in (List.range passed.length).reverse do
          let some fin := passed[i]? | throw "internal extraction error: finalizer index"
          let targets : LoopTargets := ⟨fin.loop, fin.labels, fins.drop (i+1), fin.loopDepth, fin.labelDepths⟩
          let entry ← withHandler fin.handler (body fuel fc R fin.scope fin.stmts after targets)
          after := some (entry, fin.scope)
        let next ← match passed, after with
          | _ :: _, some (entry, entryScope) => jumpTo scope entry entryScope
          | _, _ => leave fc.namePos R scope after
        emitAt pos .nul (.effect next) Γ [0] (scope := scope)
    | .ret pos e :: rest =>
      if !rest.isEmpty then throw "statements after return are outside the fragment"
      let Γ ← env fc pos.1 scope
      let A ← exprType fc e
      match loopTargets.finalizers with
      | [] =>
        let done ← emitAt e.span (.var 0) .ret (A::Γ) R "return-contract" (some pos.1)
          (scope := held ⟨"",some e.span⟩ :: scope)
        compileExpr fc scope Γ e done
      | fins =>
        -- The value, held in a slot of its own, passes through every
        -- enclosing `finally`, innermost first, each run in its `try`'s
        -- context; after the outermost, it is returned. A `finally` that
        -- itself returns or throws leaves by its own way instead.
        let retHeld : ScopeBinding := { source := ⟨s!"%return@{pos.1}%", some e.span⟩, fixed := some A }
        let some outermost := fins.getLast? | throw "internal extraction error: no finalizer"
        let Γo ← env fc outermost.pos.1 outermost.scope
        let mut after ← emitAt e.span (.var 0) .ret (A::Γo) R "return-contract" (some pos.1)
          (scope := retHeld :: outermost.scope)
        let mut afterScope := retHeld :: outermost.scope
        for i in (List.range fins.length).reverse do
          let some fin := fins[i]? | throw "internal extraction error: finalizer index"
          let fscope := retHeld :: fin.scope
          let targets : LoopTargets := ⟨fin.loop, fin.labels, fins.drop (i+1), fin.loopDepth, fin.labelDepths⟩
          after ← withHandler fin.handler
            (body fuel fc R fscope fin.stmts (some (after, afterScope)) targets)
          afterScope := fscope
        let first ← jumpTo (retHeld :: scope) after afterScope
        compileExpr fc scope Γ e first
    | .throw pos e :: rest =>
      if !rest.isEmpty then throw "statements after throw are outside the fragment"
      let Γ ← env fc pos.1 scope
      let A ← exprType fc e
      -- `throw` has every type: the node claims the result, and never
      -- produces a value to return.
      let raise ← emitAt e.span (.throw (.var 0)) .ret (A::Γ) R "throw" (some pos.1)
        (scope := held ⟨"",some e.span⟩ :: scope)
      compileExpr fc scope Γ e raise
    | .tryStmt pos tryBody handler finalizer :: rest =>
      let Γ ← env fc pos.1 scope
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail loopTargets
        pure (some (next,scope))
      -- A thrown value is bound at `unknown`: anything may be thrown.
      let top ← lower (SourceTypes.use .top)
      modify fun s => { s with hints := top :: s.hints }
      let outer := (← get).handler
      let n := scope.length
      -- The `finally` block, twice: after a normal completion of the body or
      -- the handler, continuing after the statement; and after a throw out of
      -- either, holding the thrown value, then throwing it again. Each runs in
      -- the `try`'s own context.
      -- The normal way through the `finally` is there only if the body or
      -- the handler can complete.
      let completes := !abrupt tryBody || (handler.map (fun h => !abrupt h.2)).getD false
      let (completed, onThrow) ← match finalizer with
        | none => pure ((continuation, none) :
            Option (Target × List ScopeBinding) × Option (Target × Finalizer))
        | some F =>
          -- Where neither can, no way leads there: a node that loops on
          -- itself stands for it, so nothing is claimed of a completion.
          let normal ← if completes then
              withHandler outer (body fuel fc R scope F continuation loopTargets)
            else do
              let self := (← get).program.length
              let stub ← withHandler none (emitAt pos .nul (.effect ⟨self, some []⟩) [] [0] "unreachable")
              -- Its own predecessor, it states its (empty) knowledge as a cut.
              modify fun s => { s with cuts := stub.label :: s.cuts }
              pure stub
          let thrown : ScopeBinding := { source := ⟨s!"%thrown@{pos.1}%", some pos⟩, fixed := some [top] }
          let tscope := thrown :: scope
          let rethrow ← withHandler outer
            (emitAt pos (.throw (.var 0)) .ret ([top] :: Γ) R "rethrow" (some pos.1) (scope := tscope))
          let entry ← withHandler outer (body fuel fc R tscope F (some (rethrow, tscope)) loopTargets)
          let fin : Finalizer := ⟨F, pos, scope, outer, loopTargets.loop, loopTargets.labels,
            loopTargets.loopDepth, loopTargets.labelDepths⟩
          pure ((some (normal, if completes then scope else []), some (entry, fin)) :
            Option (Target × List ScopeBinding) × Option (Target × Finalizer))
      let inner : LoopTargets := match onThrow with
        | none => loopTargets
        | some (_, fin) => { loopTargets with finalizers := fin :: loopTargets.finalizers }
      -- Where a throw goes from the handler: the `finally`, or else out.
      let afterHandler : Option (Target × Nat) := match onThrow with
        | some (entry, _) => some (entry, n)
        | none => outer
      let bodyHandler ← match handler with
        | none => pure afterHandler
        | some (param, C) =>
          let caught : ScopeBinding ← match param with
            | some (name, namePos) =>
              if name == "undefined" then throw "shadowing undefined is outside the fragment"
              if (names scope).contains name then
                throw s!"duplicate or shadowing local declaration '{name}'"
              pure (held ⟨name, some namePos⟩)
            | none => pure { source := ⟨s!"%caught@{pos.1}%", some pos⟩, fixed := some [top] }
          let entry ← withHandler afterHandler (body fuel fc R (caught :: scope) C completed inner)
          pure (some (entry, n))
      withHandler bodyHandler (body fuel fc R scope tryBody completed inner)
    | .closing pos close inner :: rest =>
      -- The body of a `for...of` over a program's iterable, the last
      -- statement of its loop: the `close` statements (IteratorClose) are a
      -- `finally` that runs on some ways out only. A `break` of the loop runs
      -- them, then leaves it; a `return` runs them as any `finally` block,
      -- its value held (`finalizers`); a throw runs them inside a `try` whose
      -- empty handler discards their own throws, then throws again. A
      -- `continue` and the body's end go to the loop's head, closing
      -- nothing. A jump past the loop to an outer target is a jump past a
      -- `finally` (`loopDepth`).
      let Γ ← env fc pos.1 scope
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail loopTargets
        pure (some (next,scope))
      let some (again, exit) := loopTargets.loop
        | throw "internal extraction error: an iterator's close outside its loop"
      let top ← lower (SourceTypes.use .top)
      modify fun s => { s with hints := top :: s.hints }
      let outer := (← get).handler
      let n := scope.length
      let closed ← withHandler outer (body fuel fc R scope close exit loopTargets)
      let thrown : ScopeBinding := { source := ⟨s!"%thrown@{pos.1}%", some pos⟩, fixed := some [top] }
      let tscope := thrown :: scope
      let rethrow ← withHandler outer
        (emitAt pos (.throw (.var 0)) .ret ([top] :: Γ) R "rethrow" (some pos.1) (scope := tscope))
      -- A throw out of the close itself is dropped, and the first one thrown
      -- again: the handler of the close's nodes discards its value.
      let dropped : ScopeBinding := { source := ⟨s!"%dropped@{pos.1}%", some pos⟩, fixed := some [top] }
      let discard ← withHandler outer
        (emitAt pos .nul (.effect ⟨rethrow.label, some ((List.range tscope.length).map (·+1))⟩)
          ([top] :: [top] :: Γ) [0] "rethrow" (some pos.1) (scope := dropped :: tscope))
      let quiet ← withHandler (some (discard, tscope.length))
        (body fuel fc R tscope close (some (rethrow, tscope)) loopTargets)
      let fin : Finalizer := ⟨close, pos, scope, outer, loopTargets.loop, loopTargets.labels,
        loopTargets.loopDepth, loopTargets.labelDepths⟩
      let targets : LoopTargets := { loopTargets with
        finalizers := fin :: loopTargets.finalizers,
        loop := some (again, some (closed, scope)),
        loopDepth := loopTargets.finalizers.length + 1 }
      withHandler (some (quiet, n)) (body fuel fc R scope inner continuation targets)
    | .constants pos bindings :: rest =>
      let Γ ← env fc pos.1 scope
      constants fc pos (fun scope => body fuel fc R scope rest tail loopTargets) scope Γ bindings
    | .ite pos cond thn els :: rest =>
      let Γ ← env fc pos.1 scope
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail loopTargets
        pure (some (next,scope))
      match ← guardedReturn fc scope Γ cond thn loopTargets with
      | some (ds, K, read, tested, e, rp) =>
        -- `if (x.f !== c) return x.f;`: the tested read, saved, is what the
        -- arm returns. Nothing runs between the two reads, so they read the
        -- same value, and the saved one keeps the test's refinement.
        let Γy ← env fc rp.1 ds
        let p ← closureExpr fc ds Γy e
        let yes ← emitPlanned e.span p .ret Γy R "return-contract" (scope := ds)
        let no ← body fuel fc R scope (els.getD []) continuation loopTargets
        let A ← exprType fc cond
        let lift := fun (t : Target) =>
          (⟨t.label, some ((t.mapping.getD (List.range scope.length)).map (·+1))⟩ : Target)
        let node ← emitBranch ds K tested A yes (lift no)
        let predicate ← compileExpr fc ds K tested node
        compileExpr fc scope Γ read predicate
      | none =>
        let yes ← body fuel fc R scope thn continuation loopTargets
        let no ← body fuel fc R scope (els.getD []) continuation loopTargets
        compileCondition fc scope Γ cond yes no
    | .loop pos cond loopBody update :: rest =>
      let Γ ← env fc pos.1 scope
      -- Reserve a stable label for incoming and back edges. Replace its stub
      -- before returning; the completed program is independently checked.
      let head ← emitAt cond.span .nul .ret Γ [0] (scope := scope)
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail loopTargets
        pure (some (next,scope))
      -- The end of the body and every `continue` run the update, which
      -- returns to the head.
      let again ← if update.isEmpty then pure head else
        body fuel fc R scope update (some (head,scope)) loopTargets
      let yes ← body fuel fc R scope loopBody (some (again,scope))
        (loopTargets.enterLoop ((again,scope), continuation))
      let no ← leave fc.namePos R scope continuation
      let condition ← compileCondition fc scope Γ cond yes no
      modify fun s => { s with program := s.program.set head.label ⟨.nul,.effect condition,none⟩ }
      let facts ← entryFacts fc pos.1 scope
      let links := distinctLinks (SourceTypes.graph (← table)) scope Γ
      if !facts.isEmpty || !links.isEmpty then
        modify fun s => { s with
          assertions := s.assertions ++ [(head.label,⟨facts,[],links⟩)]
          sourceMap := s.sourceMap.set head.label (some ⟨pos,"heap-observation",some pos.1,sources scope⟩) }
      modify fun s => { s with cuts := head.label :: s.cuts }
      pure head
    | .forOf pos name namePos iterate iterable loopBody :: rest =>
      -- The iterable once, then its iteration intrinsic on it (`%Iterate%`
      -- for an array): the step closure, held in a
      -- slot of its own at the claimed type the call's typing checks. At the
      -- head the step yields `{ value }` or `null`; null leaves the loop, and a
      -- record's value binds `name` for one run of the body, whose end and
      -- `continue` return to the head.
      let Γ ← env fc pos.1 scope
      let some (iterateSlot, _) := resolve scope iterate
        | throw "internal extraction error: a for...of loop without its intrinsic"
      let A ← exprType fc iterable
      let N ← exprType fc (.var pos iterate)
      let T ← exprType fc (.var namePos name)
      let G := SourceTypes.graph (← table)
      let [.arrs [(_, [], S)] _] := PositiveRules.expand G N
        | throw (locatedRefusal (← table) pos .bindingAnnotation
            "a for...of step is one call of no parameters")
      let present := BranchRefinement.tagSlice G S .isNul false
      let stepper := { source := ⟨s!"%next@{pos.1}%", some pos⟩, fixed := some N : ScopeBinding }
      let loopScope := stepper :: scope
      let ΓH := N :: Γ
      let head ← emitAt pos .nul .ret ΓH [0] (scope := loopScope)
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail loopTargets
        pure (some (next,scope))
      let elemScope := held ⟨name, some namePos⟩ :: loopScope
      let first ← body fuel fc R elemScope loopBody (some (head,loopScope))
        (loopTargets.enterLoop ((head,loopScope), continuation))
      let exit ← leave fc.namePos R loopScope continuation
      -- `name` takes the value read; the record it was read from is dropped.
      let bindElement := ⟨first.label, some ((first.mapping.getD (List.range elemScope.length)).map
        (fun j => if j == 0 then 0 else j+1))⟩
      let element ← emitAt namePos (.readAt (.str "value") (.var 0)) (.bind bindElement)
        (present::ΓH) T "for-of-element" (scope := held ⟨"",some pos⟩ :: loopScope)
      -- The dispatch binds a refined copy of the step's result; both arms
      -- discard the older one, and leaving discards both.
      let toElement : Target := ⟨element.label, some ((List.range (ΓH.length+1)).map
        (fun j => if j == 0 then 0 else j+1))⟩
      let toExit : Target := ⟨exit.label, some ((exit.mapping.getD (List.range ΓH.length)).map (·+2))⟩
      let stepped := held ⟨"",some pos⟩ :: loopScope
      let dispatch ← emitAt pos (.var 0) (.tagBind .isNul toExit toElement) (S::ΓH) S
        "for-of-dispatch" (scope := stepped)
      let step ← emitAt pos (Tm.call (.var 0) []) (.bind dispatch) ΓH S "for-of-step"
        (scope := loopScope)
      modify fun s => { s with program := s.program.set head.label ⟨.nul,.effect step,none⟩ }
      let facts ← entryFacts fc pos.1 scope
      let links := distinctLinks (SourceTypes.graph (← table)) loopScope ΓH
      if !facts.isEmpty || !links.isEmpty then
        modify fun s => { s with
          assertions := s.assertions ++ [(head.label,⟨facts,[],links⟩)]
          sourceMap := s.sourceMap.set head.label (some ⟨pos,"heap-observation",some pos.1,sources loopScope⟩) }
      modify fun s => { s with cuts := head.label :: s.cuts }
      -- Before the loop: the iterable, then the call making the step closure,
      -- which the head holds in place of the iterable.
      let toHead : Target := ⟨head.label, some (0 :: (List.range Γ.length).map (·+2))⟩
      let start ← emitAt pos (Tm.call (.var (iterateSlot+1)) [.var 0]) (.bind toHead) (A::Γ) N
        "for-of-iterator" (scope := held ⟨"",some iterable.span⟩ :: scope)
      compileExpr fc scope Γ iterable start
    | .mutables pos bindings :: rest =>
      let Γ ← env fc pos.1 scope
      mutables fc pos (firstEntry rest)
        (fun scope => body fuel fc R scope rest tail loopTargets) scope Γ bindings
    | .destructure pos target default_ init :: rest =>
      let Γ ← env fc pos.1 scope
      let A ← exprType fc init
      -- The initializer is held anonymously for the whole statement, below the
      -- bindings it yields, and dropped before the next statement's entry.
      let inner := held ⟨"",some init.span⟩ :: scope
      let after := fun (scope' : List ScopeBinding) (Γ' : List (Ty Nat)) =>
        dropSlot (scope'.length - scope.length - 1)
          (fun scope _ => body fuel fc R scope rest tail loopTargets) scope' Γ'
      let next ← match target, default_ with
        | .object .., none | .array .., none => destructureAt fc pos target inner (A::Γ) 0 after
        | _, _ => bindTarget fc pos target (.var 0) A default_ inner (A::Γ) after
      compileExpr fc scope Γ init next
    | .effect pos e :: rest =>
      let Γ ← env fc pos.1 scope
      let next ← body fuel fc R scope rest tail loopTargets
      let drop := ⟨next.label, some ((next.mapping.getD (List.range Γ.length)).map (·+1))⟩
      compileExpr fc scope Γ e drop
    -- A block's statements run in a scope of their own and continue after it,
    -- where its bindings are gone. A labeled one is where a `break` of its
    -- label goes. It has no entry of its own: its first statement's is.
    | .block _ label inner :: rest =>
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail loopTargets
        pure (some (next,scope))
      let targets := match label with
        | some l => loopTargets.enterLabel l continuation
        | none => loopTargets
      body fuel fc R scope inner continuation targets
    match stmts with
    | [] | .loop .. :: _ | .block .. :: _ => return target
    | st :: _ =>
      let pos := st.pos
      let facts ← entryFacts fc pos.1 scope
      let entry ← checkpoint pos (← env fc pos.1 scope) facts target (some pos.1) scope
      modify fun s => { s with cuts := entry.label :: s.cuts }
      return entry
end

structure SourceRequest extends Request where
  obligations : List ExpressionClaims.Required
  sourceMap : SourceMap := []
  assertions : List (Nat × HeapKnowledge.Knowledge) := []
  /-- Full statement-entry interfaces; absent assertions mean empty knowledge. -/
  cuts : List Nat := []
  /-- Labels the program mentions but no claim does: search hints only. -/
  hints : List Nat := []
  /-- One per code request, in its order. -/
  codeSources : List CodeSource := []
  /-- Plans for nodes the lowering knows how to derive: search hints only. -/
  nodePlans : List DirectProof.Plan := []

def SourceRequest.codeHints (r : SourceRequest) : List RequestJson.CodeHints :=
  r.codeSources.map fun c => ⟨c.sourceMap, c.assertions, c.cuts⟩

/-- Search hints only: the primitives and the labels the request mentions, so
a coercion does not consider every unrelated signature in the table. The
consumer still checks against the complete graph and the exact request. -/
def SourceRequest.searchLabels (r : SourceRequest) : List Nat :=
  let roots := ([0,1,2,3] ++ r.result ++ r.inputs.flatten ++ r.hints ++
    r.claims.flatMap (fun (c : PointClaim Nat) => c.type ++ c.context.flatten) ++
    -- A closure's code is searched with the request's vocabulary: what its
    -- claims mention is part of it (a generic closure's binder rows).
    r.codes.flatMap (fun (q : RequestJson.CodeRequest) => q.claims.flatMap (fun (c : PointClaim Nat) => c.type ++ c.context.flatten)) ++
    r.obligations.flatMap (fun (o : ExpressionClaims.Required) => o.sequent.type ++ o.sequent.context.flatten)).eraseDups
  -- Readonly array coercions depend on the store's element unions two levels
  -- below the object. Close the vocabulary over the finite reachable graph,
  -- stopping at the fixpoint: a step that adds no label changes nothing.
  Id.run do
    let mut known := roots
    for _ in List.range r.types.length do
      -- A meet row's clauses name a type the table may hold as a row of its
      -- own, a bounded binder's bound: a read through the binder is at it.
      let next := (known ++ known.flatMap (fun i =>
        ((r.types[i]?.map RequestJson.Row.union).getD []).flatMap
          (fun c => (RequestJson.clauseTypes c).flatten) ++
        (match (r.types[i]? : Option RequestJson.Row) with
          | some (.meet _ cs) => (r.types.idxOf? (RequestJson.Row.clauses cs)).toList
          | _ => []))).eraseDups
      if next.length == known.length then break
      known := next
    return known

/-- The type a code unit reads a module value at: a source type (a function's
signature, a constant's annotation), or, for an unannotated constant, the
initialization unit's claim for its initializer, a type that unit checks the
initializer's value against where the constant is bound. -/
inductive ModuleType where
  | written (ty : Json)
  | claimed (A : SourceClaims.Candidate)

/-- A value of the module a code unit reaches: its name, its declaration's
position, and its type, or why it has none. -/
abbrev ModuleValue := String × Span × Except String ModuleType

/-- The table is the one the claims were lowered into; annotations the claims
did not mention grow it, and the request carries the result. -/
def extractNormalizedFn (T : SourceTypes.Table) (f : Fragment.Fn) (fc : SourceClaims.Function)
    (module : List ModuleValue := []) : Except String SourceRequest := do
  if f.name != fc.name || f.namePos != fc.namePos then throw "function claim identity mismatch"
  let scope : List ScopeBinding := f.params.map (fun p => held ⟨p.name,none⟩)
  -- The module functions this body mentions, outermost: a parameter or local
  -- of the same name shadows one, as in JavaScript.
  let mentioned := f.body.flatMap stmtNames
  let siblings := module.filter fun g => mentioned.contains g.1 || SourceTypes.prototypeNames.contains g.1
  if f.name == "undefined" || (names scope).contains "undefined" then
    throw "shadowing undefined is outside the fragment"
  if !distinct (names scope) then throw "duplicate source parameter name"
  if f.params.length != fc.params.length then throw "parameter claim count mismatch"
  if !distinct (fc.envs.map Prod.fst) || !distinct (fc.exprs.map Prod.fst) then
    throw "duplicate statement or expression claim"
  let ((inputs, R, entry), built) ← (do
    -- One binding per source parameter, and one request input per position a
    -- caller writes: a rest parameter is one binding, and its tuple's required
    -- elements are the positions. The array itself is allocated at entry.
    let bindings ← f.params.mapM (fun (p : Fragment.Param) => lower (Fragment.translate p.ty))
    let siblingTypes ← siblings.mapM fun (value : ModuleValue) => do
      let (_, pos, ty) := value
      match ty with
        | Except.ok (.written ty) => lower (Fragment.translate ty)
        | Except.ok (.claimed A) => (SourceClaims.resolve (← table).length A).mapError fun msg =>
            s!"module constant '{value.1}': {msg}"
        | Except.error reason => throw (locatedRefusal (← table) pos .bindingAnnotation reason)
    let siblingScope : List ScopeBinding :=
      (siblings.zip siblingTypes).map fun (pair : ModuleValue × Ty Nat) =>
        { source := ⟨pair.1.1, some pair.1.2.1⟩, fixed := some pair.2 }
    if f.params.dropLast.any (fun (p : Fragment.Param) => p.rest) then
      throw "a rest parameter must be the last one"
    -- A mutable `T[]` rest is an ordinary input: the body is checked for every
    -- array of that contract, the fresh one a call collects among them.
    let tupleRest := match f.params.getLast? with
      | some p => p.rest && (Fragment.arrayElement p.ty (readonly := true)).isNone
      | none => false
    let restElements : List (Ty Nat) ← match f.params.getLast? with
      | some p =>
        if tupleRest then do
          let es ← match Fragment.tupleRequired p.ty with
            | .ok es => pure es
            | .error reason => throw (locatedRefusal (← table) f.namePos .bindingAnnotation reason)
          es.mapM fun ty => lower (Fragment.translate ty)
        else pure []
      | none => pure []
    let hasRest := tupleRest
    let inputs := (if hasRest then bindings.dropLast else bindings) ++ restElements ++ siblingTypes
    -- A parameter's annotation is the assumption its caller makes, and the
    -- soundness theorem (`RequestJson.verify_safe`) takes it as given for
    -- every environment, world and heap meeting it. Each annotation is
    -- assumed at the model's meaning of its type: a primitive is that value,
    -- an arrow is a function whose invocations respect its contract over
    -- admissible heaps, and a record is a reference to a location whose
    -- fields hold the stated types, which the read and write rules then use
    -- exactly as for a record allocated here. Two such references may alias;
    -- the heap rules are stated over locations, so nothing here assumes they
    -- do not. What a JavaScript value must be for that meaning to hold (a
    -- plain data object, not an accessor or proxy) is part of the interpreted
    -- caller contract, as it is for arrows (DESIGN.md, "Trust surface").
    for ((p, A), (name, claimed)) in (f.params.zip bindings).zip fc.params do
      if p.name != name then throw "parameter claim name or order mismatch"
      let B ← SourceClaims.resolve (← table).length claimed
      let T ← table
      if !sameMeaning T A B then
        throw s!"claimed parameter type differs from the source annotation for '{name}'"
    let R ← lower (Fragment.translate f.ret)
    let claimedR ← SourceClaims.resolve (← table).length fc.ret
    if !sameMeaning (← table) R claimedR then
      throw (locatedRefusal (← table) f.namePos .returnContract
        "claimed return type differs from the source annotation")
    let stmts ← f.body.mapM (comparisonsStmt fc)
    let paramScope : List ScopeBinding ← (scope.zip bindings).mapM fun (pair : ScopeBinding × Ty Nat) => do
      let (b,contract) := pair
      if stmts.any (assignsStmt b.source.name) then
        let reference ← lower (do return [← CellClaims.reference [(valueField, contract)]])
        let b := { b with param := true }
        pure { b with storage := .cell contract reference }
      else pure { b with param := true }
    let bodyScope := paramScope ++ siblingScope
    let slotTypes := bindings ++ siblingTypes
    let fullScope := scope ++ siblingScope
    let mut first ← body (traversalBudget stmts) fc R bodyScope stmts none {}
    -- Each assigned parameter gets one fresh private cell at function entry.
    -- Replace its slot in place; the caller still supplies the original value
    -- and the function's public input contract does not mention these cells.
    for (b,i) in bodyScope.zipIdx.reverse do
      if let .cell _ reference := b.storage then
        if hasRest && i == scope.length - 1 then
          throw "an assigned rest parameter is outside the fragment"
        let Γ := (bodyScope.zip slotTypes).zipIdx.map fun (entry : (ScopeBinding × Ty Nat) × Nat) =>
          let ((binding,A),j) := entry
          if j < i then match binding.storage with
            | .cell _ ref => ref | .value => A
          else A
        let mapping := (List.range fullScope.length).map fun j => if j == i then 0 else j+1
        first ← emitAt f.namePos (.makeAt .absent [valueField] [.var i])
          (.bind ⟨first.label,some mapping⟩) Γ reference "parameter-allocation"
          (scope := fullScope)
    -- A rest parameter's array is allocated once, on entry, before the body
    -- runs: the store holding the surplus arguments, then the object that
    -- holds the store. The body's environment binds the array where its name
    -- is; the request's inputs remain the positions a caller writes.
    if hasRest then
      let some restTy := bindings.getLast? | throw "a rest parameter needs a parameter"
      let some S := storeOf (SourceTypes.graph (← table)) restTy
        | throw "a rest parameter needs an array contract"
      let fixed := bindings.length - 1
      let anonymous := held ⟨"",some f.namePos⟩
      let restScope := scope.dropLast ++ restElements.map (fun _ => anonymous) ++ siblingScope
      -- Body slots before the array read the caller's positions; the module
      -- functions after it follow the collected positions.
      let bodyMapping := (List.range slotTypes.length).map fun j =>
        if j == fixed then 0 else if j < fixed then j + 2 else j + 1 + restElements.length
      let proto ← prototypeSlot (anonymous :: restScope)
      let _ ← arrayObject S
      let object ← emitAt f.namePos (arrayTerm proto)
        (.bind ⟨first.label, some bodyMapping⟩) (S :: inputs) restTy "rest-allocation"
        (scope := anonymous :: restScope)
      let store ← emitAt f.namePos
        (.arrLit ((List.range restElements.length).map fun j => .var (fixed + j)))
        (.bind ⟨object.label, some ((List.range (inputs.length + 1)).map
          fun j => if j == 0 then 0 else j)⟩)
        inputs S "rest-allocation" (scope := restScope)
      first := store
    let entry ← emit .nul (.effect first) inputs [0]
    return (inputs, R, entry)).run { types := T }
  return ⟨⟨built.types, built.program, built.claims, R, entry.label, inputs, built.codes⟩,
    built.obligations, built.sourceMap, built.assertions, built.cuts, built.hints, built.codeSources,
    built.nodePlans⟩

/-- One function's wire claims, lowered into a fresh table. Other producers can
supply normalized candidates directly to extractNormalizedFn. -/
def extractFn (f : Fragment.Fn) (fc : Fragment.Claims) : Except String SourceRequest := do
  let (fc, T) ← (SkjsSourceClaims.translate fc).run SourceTypes.initial
  extractNormalizedFn T f fc

/-- Evidence order is source declaration order, independent of export order. -/
structure Bundle where
  functions : List Response
  obligations : List (List (ProgramCertificates.Evidence Nat))
  deriving ToJson, FromJson

/-- Statement entries are exact interfaces, in a unit's graph and in each of its
codes'. Expression observation checkpoints inside a statement require
entailment but do not reset its local context. -/
def checkGraphAssertions (cuts : List Nat) (assertions : List (Nat × HeapKnowledge.Knowledge))
    (C : ControlFlow.Certificate Nat) : Bool :=
  (cuts.all fun l => match C[l]? with
    | none => false
    | some n => n.knowledge == (assertions.lookup l).getD ⟨[],[],[]⟩) &&
  (assertions.all fun (l,k) => match C[l]? with
    | none => false
    | some n => HeapKnowledge.check n.knowledge k none)

def checkAssertions (r : SourceRequest) (c : Response) : Bool :=
  checkGraphAssertions r.cuts r.assertions c.certificate &&
  r.codeSources.length == c.codes.length &&
  (r.codeSources.zip c.codes).all fun (q, C) => checkGraphAssertions q.cuts q.assertions C

/-- Accepted source evidence has exactly the supplied knowledge at every
statement entry, even when that knowledge is empty. -/
theorem checkAssertions_cut {r : SourceRequest} {c : Response}
    (hc : checkAssertions r c = true) {l node} (hm : l ∈ r.cuts)
    (hn : c.certificate[l]? = some node) :
    node.knowledge = (r.assertions.lookup l).getD ⟨[],[],[]⟩ := by
  simp only [checkAssertions, checkGraphAssertions, Bool.and_eq_true] at hc
  replace hc := hc.1.1
  have h := List.all_eq_true.mp hc.1 l hm
  simpa [hn] using h

theorem checkAssertions_sound {r : SourceRequest} {c : Response}
    (hc : checkAssertions r c = true) {l k node ρ heap}
    (hm : (l,k) ∈ r.assertions) (hn : c.certificate[l]? = some node)
    (hk : HeapKnowledge.Holds node.knowledge ρ heap) : HeapKnowledge.Holds k ρ heap := by
  simp only [checkAssertions, checkGraphAssertions, Bool.and_eq_true] at hc
  replace hc := hc.1.1
  have h := List.all_eq_true.mp hc.2 (l,k) hm
  simp only [hn] at h
  exact HeapKnowledge.check_sound (m := none) h hk

/-- A unit's obligations, checked with the graph code its certificate checked. -/
def checkObligations (r : SourceRequest) (c : Response) (es : List (ProgramCertificates.Evidence Nat)) : Bool :=
  match codeTable r.toRequest c with
  | some table => ExpressionClaims.checkAll (RequestJson.graph r.toRequest) r.types.length
      r.obligations es (GraphCode.admits table)
  | none => false

def checkRequests (rs : List SourceRequest) (b : Bundle) : Bool :=
  rs.length == b.functions.length && rs.length == b.obligations.length &&
    (rs.zip b.functions).all (fun (r,c) => verify r.toRequest c && checkAssertions r c) &&
    ((rs.zip b.functions).zip b.obligations).all (fun ((r,c),es) => checkObligations r c es)

/-- At a graph checkpoint, the proved state invariant entails the assertion
reconstructed from source claims, not merely a producer-selected context. -/
theorem checkRequests_assertions {rs : List SourceRequest} {b : Bundle}
    (hc : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions)
    {l k n W heap ρ} (hr : (l,k) ∈ r.assertions)
    (hs : StateOk (RequestJson.graph r.toRequest) r.result c.certificate n W heap (.at l ρ)) :
    HeapKnowledge.Holds k ρ heap := by
  simp only [checkRequests,Bool.and_eq_true,List.all_eq_true] at hc
  obtain ⟨node,hn,_,hk⟩ := hs
  exact checkAssertions_sound (hc.1.2 _ hm).2 hr hn hk

/-- Every accepted extracted function has the existing all-budget guarantee.
This does not assert semantic preservation of the source compiler. -/
theorem checkRequests_safe {rs : List SourceRequest} {b : Bundle}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions) (n W heap ρ)
    (he : EnvOk (RequestJson.graph r.toRequest) r.inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W heap) :
    SafeGraph r.program (meaning (RequestJson.graph r.toRequest) r.result) n W heap (.at r.start ρ) := by
  simp only [checkRequests, Bool.and_eq_true, List.all_eq_true] at h
  exact verify_safe (h.1.2 _ hm).1 n W heap ρ he hw hh

/-- The same guarantee at every assignment of the request graph's parameter
rows: a generic body, its binders read as parameter rows, is safe at every
instantiation of them. -/
theorem checkRequests_safe_at {rs : List SourceRequest} {b : Bundle}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions)
    (η : PositiveGraphs.MixedAssignment Nat) (n W heap ρ)
    (he : EnvOk (reassign (RequestJson.graph r.toRequest) η) r.inputs ρ n W) (hw : WorldAdm W)
    (hh : HeapOk n W heap) :
    SafeGraph r.program (meaning (reassign (RequestJson.graph r.toRequest) η) r.result) n W heap
      (.at r.start ρ) := by
  simp only [checkRequests, Bool.and_eq_true, List.all_eq_true] at h
  exact verify_safe_at (h.1.2 _ hm).1 η n W heap ρ he hw hh

/-- Every supplemental claim is a derivable sequent in the same calculus. -/
theorem checkRequests_obligations {rs : List SourceRequest} {b : Bundle}
    (h : checkRequests rs b = true) {r c es} (hm : ((r,c),es) ∈ (rs.zip b.functions).zip b.obligations)
    {q e} (hq : (q,e) ∈ r.obligations.zip es) :
    HasTy (RequestJson.graph r.toRequest) q.sequent.context q.sequent.term q.sequent.type := by
  simp only [checkRequests, Bool.and_eq_true, List.all_eq_true] at h
  have ho := h.2 _ hm
  simp only [checkObligations] at ho
  split at ho
  · rename_i table ht
    have hsound : ProgramCertificates.CodesSound (RequestJson.graph r.toRequest) (GraphCode.admits table) := by
      unfold codeTable at ht
      split at ht
      · exact GraphCode.checkCodes_sound ht
      · contradiction
    exact ExpressionClaims.checkAll_sound ho hsound hq
  · contradiction

#print axioms checkRequests_assertions
#print axioms checkAssertions_cut
#print axioms checkAssertions_sound
#print axioms checkRequests_obligations
#print axioms checkRequests_safe
#print axioms checkRequests_safe_at
end Verification.Model.SourceExtraction
