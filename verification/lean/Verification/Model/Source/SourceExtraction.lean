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
Active-name shadowing is not yet supported. This compiler remains a reviewed
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
by a certificate the proved checker accepts. The proof is what identifies two
rows reserved separately for the same recursive application, whose clauses
differ only in which of them they name, as a producer's `Values<number>` and
the one a method annotation lowers to. -/
private def within (T : SourceTypes.Table) (C A : List Nat) : Bool :=
  (SourceTypes.canonical T C).all (SourceTypes.canonical T A).contains ||
    -- Two lowerings of one declaration differ in the rows they reserve and the
    -- binder rows their schemes use: a renaming table relates them cheaply.
    (let G := SourceTypes.graph T
     match CertificateProducer.tableProof G 64 C A with
       | some p => PositiveCertificates.check G C A p
       | none => false) ||
    (let G := SourceTypes.graph T
     let pool := CertificateProducer.vocabulary G
       (CertificateProducer.readsFrom G CertificateProducer.closureFuel (C ++ A)) [] [C, A]
     match CertificateProducer.subtype G pool C A with
       | some proof => PositiveCertificates.check G C A proof
       | none => false)

/-- Whether two label lists denote the same type: each within the other. -/
private def sameMeaning (T : SourceTypes.Table) (A B : List Nat) : Bool :=
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

private def exprType (fc : SourceClaims.Function) (e : Fragment.Expr) : Compiler (Ty Nat) := do
  match fc.exprs.lookup e.span with
  | some t => (SourceClaims.resolve (← table).length t).mapError fun msg =>
      s!"source expression obligation at [{e.span.1},{e.span.2}): {msg}"
  | none => throw s!"no claimed type for the expression at {spanStr e.span}"

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
    [[SourceTypes.storeField, SourceTypes.protoField]]))
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

/-- What a computed key names, by its claimed type: a field for a string
singleton, a dictionary lookup for a broad string, or an element of the
array's store for a number. The key stays in
the program, evaluated after the receiver and before any right side, and its
expression obligation must establish that claim. -/
private inductive KeyKind where
  | field (name : String)
  | dynamic
  | element

private def keyField (fc : SourceClaims.Function) (key : Fragment.Expr) : Compiler KeyKind := do
  let K ← exprType fc key
  match PositiveRules.expand (SourceTypes.graph (← table)) K with
  | [.strLit s] =>
    if SourceTypes.reservedKey s then throw s!"'{s}' is internal to the model, not a source property"
    else pure (.field s)
  | [.str] => pure .dynamic
  | _ =>
    let _ ← arrayIndex (SourceTypes.graph (← table)) K
    pure .element

/-- A claimed null/undefined/numeric singleton selects a tag-test implementation, never
an assumption: both operands remain in the program, in source order, and their
expression obligations must establish the singleton used by this translation. -/
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
    let select := fun (A : Ty Nat) =>
      if A == [0] then some Tag.isNul else if A == [3] then some Tag.isUndef else
        match PositiveRules.expand G A with
        | .numLit bits :: cs =>
          if cs.all (fun c => match c with | .numLit b => numberEqual bits b | _ => false)
          then some (.numEq bits) else none
        | [.strLit s] => some (.strEq s)
        | _ => none
    match select R, select L with
    | some tag, _ => pure (.singletonTest p tag eq true l r)
    | _, some tag => pure (.singletonTest p tag eq false l r)
    | _, _ => throw s!"unsupported source expression at [{p.1},{p.2}): equality requires a null, undefined or numeric singleton operand"
  | .logical p a l r => return .logical p a (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .coalesce p l r => return .coalesce p (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .nullishAssign p n np r => return .nullishAssign p n np (← comparisonsExpr fc r)
  | .assign p n np r => return .assign p n np (← comparisonsExpr fc r)
  | .shapeTest p t eq e => return .shapeTest p t eq (← comparisonsExpr fc e)
  | .singletonTest p t eq tl l r => return .singletonTest p t eq tl (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .not p e => return .not p (← comparisonsExpr fc e)
  | .cast p annot e => return .cast p annot (← comparisonsExpr fc e)
  | .ctor p lam => return .ctor p (← comparisonsExpr fc lam)
  | .construct p f args => return .construct p (← comparisonsExpr fc f) (← args.mapM (comparisonsExpr fc))
  | .alloc p ns es => return .alloc p ns (← es.mapM (comparisonsExpr fc))
  | .read p f e => return .read p f (← comparisonsExpr fc e)
  | .write p f l r => return .write p f (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .index p _ e key =>
    let key ← comparisonsExpr fc key
    let e ← comparisonsExpr fc e
    match ← keyField fc key with
    | .field s => return .index p (some s) e key
    | .dynamic => return .index p none e key
    | .element => return .elemAt p e key
  | .arrayLit p es => return .arrayLit p (← es.mapM (comparisonsExpr fc))
  | .arrayAssign p targets rhs =>
    match rhs with
    | .arrayLit .. => pure ()
    | _ => throw "array destructuring requires a fresh literal; external iterators are outside the fragment"
    let targets ← targets.mapM fun q => do
      return { q with default_ := ← q.default_.mapM (comparisonsExpr fc) }
    return .arrayAssign p targets (← comparisonsExpr fc rhs)
  | .elemAt p e key => return .elemAt p (← comparisonsExpr fc e) (← comparisonsExpr fc key)
  | .elemWrite p r key rhs =>
    return .elemWrite p (← comparisonsExpr fc r) (← comparisonsExpr fc key) (← comparisonsExpr fc rhs)
  | .arith p op l r => return .arith p op (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .logicalAssign p op target rhs =>
    return .logicalAssign p op (← comparisonsExpr fc target) (← comparisonsExpr fc rhs)
  | .update p op target rhs post =>
    return .update p op (← comparisonsExpr fc target) (← rhs.mapM (comparisonsExpr fc)) post
  | .indexWrite p _ r key rhs =>
    let key ← comparisonsExpr fc key
    let r ← comparisonsExpr fc r
    let rhs ← comparisonsExpr fc rhs
    match ← keyField fc key with
    | .field s => return .indexWrite p (some s) r key rhs
    | .dynamic => throw "a dynamic string index write is outside the readonly dictionary fragment"
    | .element => return .elemWrite p r key rhs
  | .withValue p f i ft bt => return .withValue p (← comparisonsExpr fc f) (← comparisonsExpr fc i) ft bt
  | .lambda p receiver tps ps defaults rest result b =>
    return .lambda p receiver tps ps (← defaults.attach.mapM fun ⟨(i,d),_⟩ => do
      return (i, ← comparisonsExpr fc d)) rest result (← comparisonsExpr fc b)
  | .bindWithReceiver p c r args => return .bindWithReceiver p (← comparisonsExpr fc c) (← comparisonsExpr fc r) (← args.mapM (comparisonsExpr fc))
  | .callWithReceiver p c r args => return .callWithReceiver p (← comparisonsExpr fc c) (← comparisonsExpr fc r) (← args.mapM (comparisonsExpr fc))
  | .applyWithReceiver p c r list => return .applyWithReceiver p (← comparisonsExpr fc c) (← comparisonsExpr fc r) (← list.mapM (comparisonsExpr fc))
  | .call p c args spread =>
    return .call p (← comparisonsExpr fc c) (← args.mapM (comparisonsExpr fc)) spread
  | .invoke p c args spreads typeArgs =>
    -- A field, by name or by a string key, or an array element by a numeric
    -- key: `comparisonsExpr` resolves the key from its claim.
    return .invoke p (← comparisonsExpr fc c) (← args.mapM (comparisonsExpr fc)) spreads typeArgs
  | .atEnv p e => return .atEnv p (← comparisonsExpr fc e)
  | .seqBody p i b => return .seqBody p (← comparisonsExpr fc i) (← comparisonsExpr fc b)
  | .ifBody p result c t e => return .ifBody p result (← comparisonsExpr fc c) (← comparisonsExpr fc t) (← comparisonsExpr fc e)
  | .letBody p n annot i b => return .letBody p n annot (← comparisonsExpr fc i) (← comparisonsExpr fc b)

private partial def comparisonsStmt (fc : SourceClaims.Function) (s : Fragment.Stmt) :
    Compiler Fragment.Stmt := do
  match s with
  | .ret p e => return .ret p (← comparisonsExpr fc e)
  | .constants p bs => return .constants p (← bs.mapM fun b => do return { b with init := ← comparisonsExpr fc b.init })
  | .mutables p bs => return .mutables p (← bs.mapM fun b => do return { b with init := ← comparisonsExpr fc b.init })
  | .pattern p props init =>
    let props ← props.mapM fun q => do
      return { q with default_ := ← q.default_.mapM (comparisonsExpr fc) }
    return .pattern p props (← comparisonsExpr fc init)
  | .arrayPattern p elems init =>
    match init with
    | .arrayLit .. => pure ()
    | _ => throw "array destructuring requires a fresh literal; external iterators are outside the fragment"
    let elems ← elems.mapM fun q => do
      return { q with default_ := ← q.default_.mapM (comparisonsExpr fc) }
    return .arrayPattern p elems (← comparisonsExpr fc init)
  | .effect p e => return .effect p (← comparisonsExpr fc e)
  | .ite p c t e =>
    return .ite p (← comparisonsExpr fc c) (← t.mapM (comparisonsStmt fc))
      (← e.mapM (fun ss => ss.mapM (comparisonsStmt fc)))
  | .loop p c b => return .loop p (← comparisonsExpr fc c) (← b.mapM (comparisonsStmt fc))
  | .brk .. | .cont .. => pure s

/-- Storage is selected from source assignments, including writes in nested
closures. Active-name shadowing is rejected by the lowering, so a matching
name cannot silently designate a different binding. Producer claims cannot
choose which parameters are mutable. -/
private partial def assignsExpr (name : String) : Fragment.Expr → Bool
  | .var .. | .lit .. | .done .. => false
  | .assign _ target _ rhs | .nullishAssign _ target _ rhs => target == name || assignsExpr name rhs
  | .lambda _ _ _ _ defaults _ _ e =>
    defaults.attach.any (fun ⟨d,_⟩ => assignsExpr name d.2) || assignsExpr name e
  | .not _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e | .atEnv _ e =>
    assignsExpr name e
  | .equality _ _ a b | .logical _ _ a b | .coalesce _ a b
  | .singletonTest _ _ _ _ a b | .write _ _ a b | .withValue _ a b _ _ | .index _ _ a b
  | .seqBody _ a b | .letBody _ _ _ a b => assignsExpr name a || assignsExpr name b
  | .indexWrite _ _ a b c | .elemWrite _ a b c => assignsExpr name a || assignsExpr name b || assignsExpr name c
  | .arith _ _ a b | .elemAt _ a b => assignsExpr name a || assignsExpr name b
  | .arrayLit _ es => es.any (assignsExpr name)
  | .arrayAssign _ targets rhs => targets.any (fun q => q.name == name ||
      (q.default_.map (assignsExpr name)).getD false) || assignsExpr name rhs
  | .logicalAssign _ _ target rhs =>
    (match target with | .var _ n => n == name | _ => false) ||
      assignsExpr name target || assignsExpr name rhs
  | .update _ _ target rhs _ =>
    (match target with | .var _ n => n == name | _ => false) ||
      assignsExpr name target || (rhs.map (assignsExpr name)).getD false
  | .alloc _ _ es => es.any (assignsExpr name)
  | .call _ f args _ | .invoke _ f args _ _ => assignsExpr name f || args.any (assignsExpr name)
  | .callWithReceiver _ f r args | .bindWithReceiver _ f r args =>
    assignsExpr name f || assignsExpr name r || args.any (assignsExpr name)
  | .ctor _ lam => assignsExpr name lam
  | .construct _ f args => assignsExpr name f || args.any (assignsExpr name)
  | .applyWithReceiver _ f r list =>
    assignsExpr name f || assignsExpr name r || (list.map (assignsExpr name)).getD false
  | .ifBody _ _ c t e => assignsExpr name c || assignsExpr name t || assignsExpr name e

private partial def assignsStmt (name : String) : Fragment.Stmt → Bool
  | .ret _ e | .effect _ e => assignsExpr name e
  | .constants _ bs | .mutables _ bs => bs.any fun b => assignsExpr name b.init
  | .pattern _ props init => assignsExpr name init ||
    props.any fun q => (q.default_.map (assignsExpr name)).getD false
  | .arrayPattern _ elems init => assignsExpr name init ||
    elems.any fun q => (q.default_.map (assignsExpr name)).getD false
  | .ite _ c t e => assignsExpr name c || t.any (assignsStmt name) ||
    (e.getD []).any (assignsStmt name)
  | .loop _ c b => assignsExpr name c || b.any (assignsStmt name)
  | .brk .. | .cont .. => false

/-- Every name a statement's expressions mention, bound or not: a superset of
the module functions its body can reach. -/
partial def stmtNames : Fragment.Stmt → List String
  | .ret _ e | .effect _ e => e.freeNames
  | .constants _ bs | .mutables _ bs => bs.flatMap fun b => b.init.freeNames
  | .pattern _ props init => init.freeNames ++
    props.flatMap fun q => (q.default_.map Fragment.Expr.freeNames).getD []
  | .arrayPattern _ elems init => init.freeNames ++
    elems.flatMap fun q => (q.default_.map Fragment.Expr.freeNames).getD []
  | .ite _ c t e => c.freeNames ++ t.flatMap stmtNames ++ (e.getD []).flatMap stmtNames
  | .loop _ c b => c.freeNames ++ b.flatMap stmtNames
  | .brk .. | .cont .. => []

/-- A module function's value as its callers see it: an ordinary function
whose receiver is irrelevant, at exactly its annotated parameters and result.
A rest parameter contributes its tuple's positions or its array's element. -/
def moduleArrow (g : Fragment.Fn) : Except String Json := do
  let fixed := if g.params.getLast?.any (·.rest) then g.params.dropLast else g.params
  let (positions, rest) ← match g.params.getLast? with
    | some p =>
      if !p.rest then pure (fixed.map (·.ty), [])
      else match Fragment.arrayElement p.ty with
        | some e => pure (fixed.map (·.ty), [("rest", e)])
        | none => pure (fixed.map (·.ty) ++ (← Fragment.tupleRequired p.ty), [])
    | none => pure ([], [])
  let top := Json.mkObj [("top", toJson true), ("atoms", toJson ([] : List Json))]
  return Json.mkObj [("top", toJson false), ("atoms", toJson [Json.mkObj
    ([("a", toJson "function"), ("this", top), ("params", toJson positions)] ++ rest ++
      [("result", g.ret), ("construct", toJson "unknown"), ("array", toJson "unknown")])])]

/-- A terminal branch uses the enclosing source result annotation, not a
fabricated expression claim at the if statement's span. -/
private def closureType (fc : SourceClaims.Function) (e : Fragment.Expr) : Compiler (Ty Nat) := do
  if let some (p, T) := (← get).resultOverride then
    if p == e.span then return T
  match e with
  | .atEnv _ b | .letBody _ _ _ _ b | .seqBody _ _ b => closureType fc b
  | .done _ => pure [0]
  | .ifBody _ (some result) _ _ _ => do lower (Fragment.callableType result)
  | e => exprType fc e

private def emit (t : Tm) (k : Continuation) (Γ : List (Ty Nat)) (A : Ty Nat) :
    Compiler Target := do
  let s : Built ← get
  set { s with program := s.program ++ [(⟨t,k⟩ : ControlFlow.Node)]
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

/-- The cells this lowering allocated sit at locations no other object in
scope has: a private cell's identity never becomes a source value, and every
record-typed slot holds something else. Stated at each cut so the allocation's
freshness survives the reset of knowledge there; every incoming edge proves
it, from the allocation or from the cut before. -/
private def distinctLinks (G : Verification.Model.PositiveGraphs.NormalGraph Nat) (scope : List ScopeBinding)
    (Γ : List (Ty Nat)) : HeapLinks.Links :=
  scope.zipIdx.flatMap fun (b,i) =>
    match b.storage with
    | .cell .. =>
      Γ.zipIdx.flatMap fun (A,j) =>
        if i == j then [] else
        match PositiveRules.expand G A with
        | [.refs fs _ _ [] _ _] => fs.map fun p => (⟨i,j,false,valueField,true,p.1⟩ : HeapLinks.Link)
        | _ => []
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
      if contract.all A.contains then
        persistentObservation b.source (pos,pos+1) reference valueField A
      else
        match HeapKnowledge.atoms (SourceTypes.graph (← table)) A with
        | some atoms => facts := facts ++ [⟨i,atoms,valueField⟩]
        | none => persistentObservation b.source (pos,pos+1) reference valueField A
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

/-- A saved read is usable only in a subtree with no possible heap effects or
escaping closure. Reads are plain modeled cells, never JavaScript accessors. -/
private def readOnly : Fragment.Expr → Bool
  | .var .. | .lit .. | .done .. => true
  | .not _ e | .cast _ _ e | .read _ _ e | .shapeTest _ _ _ e | .atEnv _ e => readOnly e
  | .equality _ _ a b | .singletonTest _ _ _ _ a b | .logical _ _ a b | .coalesce _ a b
  | .seqBody _ a b | .letBody _ _ _ a b | .index _ _ a b | .arith _ _ a b | .elemAt _ a b => readOnly a && readOnly b
  | .ifBody _ _ c t e => readOnly c && readOnly t && readOnly e
  | .alloc .. | .write .. | .indexWrite .. | .update .. | .logicalAssign .. | .assign .. | .arrayLit .. | .elemWrite .. | .arrayAssign .. | .nullishAssign .. | .lambda .. | .withValue .. | .bindWithReceiver ..
  | .callWithReceiver .. | .applyWithReceiver .. | .call .. | .invoke .. | .ctor .. | .construct .. => false

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
        pure (snapshotName name fld)
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
      throw "numeric comparison requires a union of known singleton outcomes"
    pure (DirectProof.node H term A (if q then .ifTrue else .ifFalse)
      [DirectProof.cast H A (DirectProof.node H value B rule)])
  pure (DirectProof.node Γ term A (.unionVar slot) children)

/-- A defaulted parameter's slot holds its declared type or `undefined`: the
value a call that omits the position binds there. This is the replacement the
body sees, and it is the same shape as `??`, on the `undefined` tag alone. -/
private def defaultValuePlan (G : PositiveGraphs.NormalGraph Nat) (Γ : List (Ty Nat))
    (slot : Nat) (B : Ty Nat) (d : DirectProof.Plan) : Except String DirectProof.Plan := do
  let some C := Γ[slot]? | throw "internal default-parameter slot mismatch"
  let term := Tm.ite (.test .isUndef (.var slot)) d.term (.var slot)
  let children := C.map fun label =>
    let L := Γ.set slot [label]
    let q := decide (Answers G [label] .isUndef true)
    let selected := if q then DirectProof.cast L B d else DirectProof.var L slot B
    if q || decide (Answers G [label] .isUndef false) then
      DirectProof.node L term B (if q then .ifTrue else .ifFalse) [selected]
    else
      -- A mixed label (notably unknown) needs a real Boolean branch. Both
      -- alternatives must establish B; no tag answer is assumed for it.
      let test := DirectProof.node L (.test .isUndef (.var slot)) [1,2] .test
        [DirectProof.var L slot [label]]
      DirectProof.node L term B .ifBool [test, DirectProof.cast L B d, DirectProof.var L slot B]
  pure (DirectProof.node Γ term B (.unionVar slot) children)

/-- Shared conditional proof construction for statement branches, ternaries and
short-circuit operators. Branch builders retain their own source claims; a
logical operator's constant arm is administrative and needs no invented claim. -/
private def conditionalPlan (scope : List ScopeBinding) (H : List (Ty Nat)) (A : Ty Nat)
    (cond : Fragment.Expr) (c : DirectProof.Plan)
    (yesBranch noBranch : List ScopeBinding → List (Ty Nat) → Compiler DirectProof.Plan) :
    Compiler DirectProof.Plan := do
  let G := SourceTypes.graph (← table)
  if let some (i, tag, equal) := tagConditionVariable scope cond then
    let some C := H[i]? | throw "internal closure tag-guard slot mismatch"
    -- Preserve the evaluated predicate and its claims in an anonymous slot.
    let K := c.type :: H
    let tested := i+1
    let T := K.set tested (BranchRefinement.tagSlice G C tag true)
    let F := K.set tested (BranchRefinement.tagSlice G C tag false)
    let t ← yesBranch (held ⟨"",some cond.span⟩ :: scope) (if equal then T else F)
    let e ← noBranch (held ⟨"",some cond.span⟩ :: scope) (if equal then F else T)
    let yes := if equal then t else e
    let no := if equal then e else t
    let term := Tm.ite (.test tag (.var tested)) yes.term no.term
    let children := C.map fun label =>
      let L := K.set tested [label]
      let q := decide (Answers G [label] tag true)
      DirectProof.node L term A (if q then .ifTrue else .ifFalse)
        [DirectProof.cast L A (if q then yes else no)]
    pure (DirectProof.letE H c (DirectProof.node K term A (.unionVar tested) children))
  else
    match conditionVariable scope cond with
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
field or view, or, for a key outside its own-key bound, its prototype's, as
`readCell` and the top level's search read it. -/
private def fieldRow (G : PositiveGraphs.NormalGraph Nat) (O : Ty Nat) (fld : PropKey) :
    Option (Ty Nat) :=
  match PositiveRules.expand G O with
  | [.refs fs [] vs _ _ ks] => fs.lookup fld <|> vs.lookup fld <|> do
      if !ks.any (fun K => !K.contains fld) then none
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

/-- Read a field from a cell plan under context `Γ`: one contract, a callable
bag, or an explicit union of cell contracts each naming the field. -/
private def readCell (G : PositiveGraphs.NormalGraph Nat) (Γ : List (Ty Nat)) (fld : PropKey)
    (a : DirectProof.Plan) : Compiler DirectProof.Plan := do
  match PositiveRules.expand G a.type with
  | [.refs fs [] vs [] _ ks] =>
    -- An invariant field reads at its contract; a readonly view at its bound;
    -- a key outside a bound of the object at its prototype's field or view
    -- (`readProto`), as at the top level.
    match fs.lookup fld, vs.lookup fld with
    | some B, _ => pure (DirectProof.node Γ (.readAt fld a.term) B .read [a])
    | none, some B => pure (DirectProof.node Γ (.readAt fld a.term) B .readView [a])
    | none, none =>
      let inherited : Option (Ty Nat × Ty Nat) := do
        if !ks.any (fun K => !K.contains fld) then none
        let P ← (fs ++ vs).lookup SourceTypes.protoField
        let [.refs gs [] ws _ _ _] := PositiveRules.expand G P | none
        let B ← (gs ++ ws).lookup fld
        pure (P, B)
      let some (P, B) := inherited | throw s!"read of a field '{fld}' the contract does not name"
      pure (DirectProof.node Γ (.readAt fld a.term) B (.readProto P) [a])
  | [.dict _ [] _ (B :: _)] =>
    pure (DirectProof.node Γ (.readAt fld a.term) (B ++ [3]) (.readDict B [3]) [a])
  | [.dict _ [] _ []] => throw "indexed object has no string index contract"
  | [.callable fs _ _ _] =>
    let some B := fs.lookup fld | throw s!"read of a field '{fld}' the contract does not name"
    pure (DirectProof.node Γ (.readAt fld a.term) B .readCallable [a])
  | _ =>
    if a.type.length ≤ 1 then throw "read receiver must name a cell contract"
    let alternatives ← a.type.mapM fun label => do
      let [.refs fs [] [] [] _ _] := PositiveRules.expand G [label]
        | throw "every read alternative must name a cell contract"
      let some B := fs.lookup fld
        | throw s!"read of a field '{fld}' an alternative does not name"
      pure (label,B)
    let R := (alternatives.flatMap Prod.snd).eraseDups
    let children := alternatives.map fun (label,B) =>
      let H := [label] :: Γ
      DirectProof.cast H R (DirectProof.node H (.readAt fld (.var 0)) B .read
        [DirectProof.var H 0 [label]])
    pure (DirectProof.letE Γ a (DirectProof.node (a.type::Γ)
      (.readAt fld (.var 0)) R (.unionVar 0) children))

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

/-- Build compositional proofs for lambda bodies and source ternaries without
losing their individual claims. Requirements use the lexical context at the occurrence; synthetic let
slots are introduced only after the operand supplying their type is checked. -/
private partial def closureExpr (fc : SourceClaims.Function) (scope : List ScopeBinding) (Γ : List (Ty Nat))
    (e : Fragment.Expr) : Compiler DirectProof.Plan := do
  let A ← closureType fc e
  let G := SourceTypes.graph (← table)
  if let some asserted := fc.exprCurrent.lookup e.span then
    for (fld, R) in asserted do
      match e with
      | .var _ name => observed scope Γ (snapshotName name (← stringKey fld)) ⟨"",some e.span⟩ e.span A fld R
      | _ => persistentObservation ⟨"",some e.span⟩ e.span A fld R
  let p ← match e with
  | .equality .. => throw "internal unresolved equality"
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
  | .shapeTest _ tag equal e => do
    let operand ← closureExpr fc scope Γ e
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
    let constant := fun (_ : List ScopeBinding) H => pure
      (if andOp then DirectProof.node H .fls [2] .flsLit
       else DirectProof.node H .tru [1] .truLit)
    let rhs := fun ds types => closureExpr fc ds types right
    conditionalPlan scope Γ A left l
      (if andOp then rhs else constant) (if andOp then constant else rhs)
  | .coalesce _ left right => do
    let l ← closureExpr fc scope Γ left
    let K := l.type :: Γ
    let H := (BranchRefinement.tagSlice G l.type .isNullish true) :: Γ
    -- A named immutable left operand is identical to the saved value. Move its
    -- name to that slot for the fallback; no mutable read is given an alias.
    let rightScope := match left with
      | .var _ name =>
        if (valueSlot scope name).isSome then held ⟨name,some left.span⟩ ::
          scope.map (fun b => if b.source.name == name then held ⟨"",some left.span⟩ else b)
        else held ⟨"",some left.span⟩ :: scope
      | _ => held ⟨"",some left.span⟩ :: scope
    let r ← closureExpr fc rightScope H right
    let term := Tm.ite (.test .isNullish (.var 0)) r.term (.var 0)
    let children := l.type.map fun label =>
      let L := [label] :: Γ
      let q := decide (Answers G [label] .isNullish true)
      let selected := if q then DirectProof.cast L A r else DirectProof.var L 0 A
      DirectProof.node L term A (if q then .ifTrue else .ifFalse) [selected]
    pure (DirectProof.letE Γ l (DirectProof.node K term A (.unionVar 0) children))
  | .not _ a => do
    let a ← closureExpr fc scope Γ a
    pure (DirectProof.ifE G Γ A a
      (DirectProof.node Γ .fls [2] .flsLit) (DirectProof.node Γ .tru [1] .truLit))
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
    match PositiveRules.expand G A with
    | [.refs B [] []] =>
      if B.length != ns.length then throw "allocation claim names different fields"
      let B ← (ns.map PropKey.str).mapM fun name => do
        let some D := B.lookup name | throw "allocation claim names different fields"
        pure (name,D)
      let Ref ← lower (CellClaims.reference B)
      -- The calculus evaluates these initializers from left to right.
      let casts := (ps.zip (B.map Prod.snd)).map fun (p,D) => DirectProof.cast Γ D p
      pure (DirectProof.node Γ (.makeAt .absent (ns.map .str) (ps.map (·.term))) [Ref] .alloc casts)
    | [.dict [] [] [] [E]] =>
      if ns.eraseDups.length != ns.length then throw "duplicate dictionary literal key"
      let casts := ps.map fun p => DirectProof.cast Γ E p
      pure (DirectProof.node Γ (.makeAt .absent (ns.map .str) (ps.map (·.term))) A .allocDict casts)
    | _ => throw "allocation claim must name a record or readonly dictionary contract"
  | .read _ fld a => do
    let receiver := a
    let a ← closureExpr fc scope Γ a
    let snapshot := match receiver with
      | .var _ name => (names scope).idxOf? (snapshotName name fld)
      | _ => none
    if let some i := snapshot then
      let some R := Γ[i]? | throw "internal saved-read slot mismatch"
      pure (DirectProof.var Γ i R)
    else readCell G Γ fld a
  | .index _ (some fld) receiver key => do
    -- The receiver, then the key, then the read: the key's own claim was
    -- resolved to the field, and is checked here like any operand's.
    let r ← closureExpr fc scope Γ receiver
    let k ← closureExpr fc (held ⟨"",some receiver.span⟩ :: scope) (r.type::Γ) key
    let H := k.type::r.type::Γ
    let read ← readCell G H fld (DirectProof.var H 1 r.type)
    pure (DirectProof.letE Γ r (DirectProof.letE (r.type::Γ) k read))
  | .index _ none receiver key => do
    let r ← closureExpr fc scope Γ receiver
    let k ← closureExpr fc (held ⟨"",some receiver.span⟩ :: scope) (r.type::Γ) key
    let G := SourceTypes.graph (← table)
    let [.dict _ [] _ (E :: _)] := PositiveRules.expand G r.type
      | throw "a dynamic string index requires a dictionary receiver"
    let [.str] := PositiveRules.expand G k.type
      | throw "a dynamic dictionary key must have string type"
    let H := k.type::r.type::Γ
    let read := DirectProof.node H (.indexAt (.var 1) (.var 0)) (E ++ [3])
      (.indexDict E [3]) [DirectProof.var H 1 r.type, DirectProof.var H 0 k.type]
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
    -- Both operands are checked as numbers by the rule; the result is the
    -- number family, whatever its bits.
    let a ← closureExpr fc scope Γ l
    let b ← closureExpr fc (held ⟨"",some l.span⟩ :: scope) (a.type::Γ) r
    let H := a.type::Γ
    let N : Ty Nat := [← lower (SourceTypes.use .num)]
    pure (DirectProof.letE Γ a
      (DirectProof.node H (.arith op (.var 0) b.term) N .arith [DirectProof.var H 0 a.type, b]))
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
    -- receiver's store at the key's one index.
    let r ← closureExpr fc scope Γ receiver
    let k ← closureExpr fc (held ⟨"",some receiver.span⟩ :: scope) (r.type::Γ) key
    let H := k.type::r.type::Γ
    let index ← arrayKeyTerm k.type
    let .num b := index | throw "internal array index term"
    let I : Ty Nat := [← lower (SourceTypes.use (.numLit b))]
    let store ← readCell G H SourceTypes.storeField (DirectProof.var H 1 r.type)
    let [.list T []] := PositiveRules.expand G store.type | throw "an element read needs an array"
    let U : Ty Nat := [3]
    let (E, rule) ← match ProgramCertificates.requiredAt T b, ProgramCertificates.optionalAt T b U with
      | some E, _ => pure (E, ProgramCertificates.Rule.elem)
      | none, some E => pure (E, .elemOpt U)
      | none, none => throw "an element read at an index no contract names"
    let read := DirectProof.node H (.elemAt store.term index) E rule
      [store, DirectProof.node H index I .numLit]
    pure (DirectProof.letE Γ r (DirectProof.letE (r.type::Γ) k (DirectProof.cast H A read)))
  | .elemWrite .. | .arrayAssign .. => throw "array writes inside a closed expression are outside the fragment"
  | .logicalAssign pos .nullish (.var np name) rhs =>
    closureExpr fc scope Γ (.nullishAssign pos name np rhs)
  | .logicalAssign .. => throw "logical assignment inside a closed expression is outside the fragment"
  | .bindWithReceiver _ f receiver args => do
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
    let method ← if (ProgramTyping.memberOf G r.type fld).isSome then
        pure (DirectProof.node K (memberHead G r.type fld (.var ri)) M (.bindMember []) [])
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
  | .call _ f args spreads => do
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
  | .atEnv pos body => do
    let H ← closureEnv fc pos.1 scope Γ
    for (B,i) in H.zipIdx do
      obligation pos ⟨Γ,.var i,B⟩ (some (DirectProof.var Γ i B)) "closure-entry" scope
    closureExpr fc scope H body
  | .withValue pos fn initial functionType bagType => do
    let f ← closureExpr fc scope Γ fn
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
      let P ← (ns.map PropKey.str).mapM fun name => do
        let some D := P.lookup name | throw s!"initializer field '{name}' is absent from its annotation"
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
    let P ← (ns.map PropKey.str).mapM fun name => do
      let some D := P.lookup name | throw s!"initializer field '{name}' is absent from its annotation"
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
    let paramNames := params.map Prod.fst
    if !distinct paramNames || paramNames.any (fun name => name == "" || name == "undefined" || (names scope).contains name) then
      throw "shadowing or duplicate constructor parameter is outside the fragment"
    let [.ctors L] := PositiveRules.expand G A | throw "a class value's claim must name construct signatures"
    let Ds ← params.mapM fun p => lower (Fragment.callableType p.2)
    let R ← lower (Fragment.callableType ret)
    let T ← table
    if L.isEmpty || !L.all (fun (Di,_) => Di.length == Ds.length && (Di.zip Ds).all (fun (D,B) => within T D B)) then
      throw "construct signature claim is outside the source annotation"
    let inner := held ⟨"", some pos⟩ :: (params.map fun (name,_) => held ⟨name, some pos⟩) ++ scope
    let b ← closureExpr fc inner ([3] :: Ds ++ Γ) body
    let annotation := DirectProof.cast ([3] :: Ds ++ Γ) R b
    obligation pos annotation.goal (some annotation) "closure-result" inner
    let bodies ← L.mapM fun (Di, Ri) => do
      if (Di, Ri) == (Ds, R) then pure annotation else do
        let plan ← closureExpr fc inner ([3] :: Di ++ Γ) body
        if plan.term != b.term then
          throw "a class body lowers differently under one of its construct signatures"
        pure (DirectProof.cast ([3] :: Di ++ Γ) Ri plan)
    pure (DirectProof.node Γ (.make (.closure Ds.length b.term .construct) .nul) A (.ctorE [3]) bodies)
  | .construct _ f args => do
    let callee ← closureExpr fc scope Γ f
    let [.ctors L] := PositiveRules.expand G callee.type
      | throw "`new` needs a value with construct signatures"
    let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr fc scope Γ a
    let some (Ds, R) := L.find? (·.1.length == actuals.length)
      | throw "no construct signature takes this many arguments"
    pure (DirectProof.node Γ (.construct callee.term (actuals.map (·.term))) R .construct
      (callee :: (actuals.zip Ds).map fun (a,D) => DirectProof.cast Γ D a))
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
      if let some elementJson := Fragment.arrayElement restJson then
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
      let [.arrs L []] := PositiveRules.expand G A | throw "closure claim must name a source arrow"
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
  let plan := DirectProof.cast Γ A p
  obligation e.span plan.goal (some plan) "expression-claim" scope
  -- Validate the supplied claim, but do not discard a stronger saved-read
  -- derivation needed for the enclosing return contract. atEnv is a no-op.
  match e with
  | .read _ fld (.var _ name) =>
    if (names scope).contains (snapshotName name fld) then return p else return plan
  | .var _ name =>
    if (names scope).contains (localSnapshotName name) then return p else return plan
  | .atEnv .. => return p
  | _ => return plan



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
    let slots ← outer.mapM fun b => match (names scope).idxOf? b.source.name with
      | some i => pure i
      | none => throw s!"internal extraction error: lost outer binding '{b.source.name}'"
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
  if let some (i, tag, equal) := tagConditionVariable scope cond then
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
  emitAt cond.span (.var 0) (.branchBind (adapt yes) (adapt no)) (A::Γ) A
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
    if let some (i, tag, equal) := tagConditionVariable scope cond then
      Γ.set i (BranchRefinement.tagSlice G (Γ[i]?.getD []) tag (answer == equal))
    else if let some i := testedSlot scope Γ cond then
      Γ.set i (if answer then [1] else [2])
    else Γ

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
      | .refs fs [] vs => match fs.lookup SourceTypes.storeField <|> vs.lookup SourceTypes.storeField with
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

mutual
/-- Each expression leaves its result in slot zero and preserves the original
slots after it. Anonymous temporary slots cannot be named by source identifiers.
Mappings discard only the temporaries introduced by this expression. -/
private partial def compileExpr (fc : SourceClaims.Function) (scope : List ScopeBinding) (Γ : List (Ty Nat))
    (e : Fragment.Expr) (next : Target) : Compiler Target := do
  let A ← exprType fc e
  let next ← match fc.exprCurrent.lookup e.span with
    | none => pure next
    | some asserted =>
      let facts ← asserted.mapM fun (fld, R) => do return (⟨0,← contents R,fld⟩ : HeapFacts.Fact)
      checkpoint e.span (A::Γ) facts next (scope := held ⟨"",some e.span⟩ :: scope)
  match he : e with
  | .equality .. => throw "internal unresolved equality"
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
  | .arrayAssign _ targets rhs =>
    -- The right side is held for the whole assignment, below the reads of
    -- its positions; its value is the expression's.
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun j => if j == 0 then 0 else j+1))⟩
    let effects := held ⟨"",some rhs.span⟩ :: scope
    let result ← emitAt e.span (.var 0) (.bind drop) (C::Γ) A (scope := effects)
    let writes ← arrayAssigns fc e.span C result effects (C::Γ) 0 targets
    compileExpr fc scope Γ rhs writes
  | .lit _ v => emitAt e.span (← SourceTypes.value v) (.bind next) Γ A (scope := scope)
  | .read _ fld a =>
    let B ← exprType fc a
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    -- An array's `length` is its store's, read as a number.
    let term := if fld == "length" && (storeOf (SourceTypes.graph (← table)) B).isSome
      then Tm.lenOf (.readAt SourceTypes.storeField (.var 0)) else .readAt fld (.var 0)
    let node ← emitAt e.span term (.bind drop) (B::Γ) A
      (scope := held ⟨"",some a.span⟩ :: scope)
    compileExpr fc scope Γ a node
  | .not _ a =>
    let B ← exprType fc a
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let node ← emitAt e.span (.ite (.var 0) .fls .tru) (.bind drop) (B::Γ) A
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
    let make ← emitAt e.span (.makeAt .absent (ns.map .str) ((List.range n).map fun i => .var (n-1-i)))
      (.bind drop) (As.reverse ++ Γ) A (scope := temporaries ++ scope)
    operands.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) =>
      compileExpr fc
        ((operands.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++ scope)
        ((As.take i).reverse ++ Γ) arg next) make
  | .atEnv .. | .letBody .. | .ifBody _ (some _) .. | .done .. | .seqBody .. => throw "statement environment wrapper is only supported inside a closure"
  | .ifBody _ none cond thn els =>
    -- A source ternary branches in the graph like an `if` statement, so an
    -- effect in its condition or an arm is a node with its own knowledge;
    -- each arm is compiled under the condition's refinement of its context
    -- and joins the continuation with its own claim.
    let G := SourceTypes.graph (← table)
    let yes ← compileExpr fc scope (conditionContext G scope Γ cond true) thn next
    let no ← compileExpr fc scope (conditionContext G scope Γ cond false) els next
    compileCondition fc scope Γ cond yes no
  | .bindWithReceiver .. | .withValue .. | .lambda .. | .ctor .. | .coalesce .. | .logical .. =>
    let t ← closureExpr fc scope Γ e
    emitAt e.span t.term (.bind next) Γ A (scope := scope)
  | .construct _ callee args =>
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
  | .shapeTest _ tag equal operand =>
    let B ← exprType fc operand
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
  | .call _ callee args _ | .callWithReceiver _ callee _ args | .invoke _ callee args _ _ =>
    let operands := match e with
      | .callWithReceiver _ _ receiver _ => receiver :: args
      | _ => args
    let spreads := match e with
      | .call _ _ _ s | .invoke _ _ _ s _ => s
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
            "explicit type arguments on an element call are outside the fragment")
        let K ← exprType fc key
        let index ← arrayKeyTerm K
        pure (some (o, some key, fun obj => .elemAt (.readAt SourceTypes.storeField obj) index))
      | .invoke .. => throw "a method call's target must name a field or an element"
      | _ => pure none
    let B ← exprType fc callee
    let headTys : List (Ty Nat) ← match method with
      | none => pure [B]
      | some (o, key, _) => do
        let O ← exprType fc o
        let keyTy ← key.mapM (exprType fc)
        pure (B :: keyTy.toList ++ [O])
    let headScope := match method with
      | none => [held ⟨"",some callee.span⟩]
      | some (o, key, _) => held ⟨"",some callee.span⟩ ::
          (key.map fun k => held ⟨"",some k.span⟩).toList ++ [held ⟨"",some o.span⟩]
    let h := headTys.length
    -- Into a variadic callee a spread may be anywhere among the actuals past
    -- the fixed ones. The call reads a spread once every actual is evaluated;
    -- a spread followed by an actual that runs code is therefore copied where
    -- it is written, `[...xs]`, and the call spreads the copy, which nothing
    -- else can reach. Into fixed parameters a spread is the last actual and
    -- stands for a tuple's required positions.
    let variadic := !(ProgramTyping.restSigs (SourceTypes.graph (← table)) B).isEmpty
    let copied := if variadic then spreads.filter fun i =>
        (args.drop (i + 1)).any fun a => match a with | .var .. | .lit .. => false | _ => true
      else []
    if !variadic && !spreads.isEmpty && spreads != [args.length - 1] then
      throw (locatedRefusal (← table) e.span .bindingAnnotation
        "a spread into fixed parameters must be the last argument")
    let spread := !variadic && !spreads.isEmpty
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
    -- yields (DESIGN.md, the trust boundary).
    let elements : List (Ty Nat) ← if !spread then pure [] else do
      let some arrayTy := As.getLast? | throw "a spread argument needs an operand"
      let G := SourceTypes.graph (← table)
      let some S := storeOf G arrayTy | throw "a spread argument needs a tuple contract"
      match PositiveRules.expand G S with
      | [.list T []] =>
        if !T.optional.isEmpty || T.rest.isSome then
          throw "a spread argument needs a tuple contract of required positions"
        pure T.required
      | _ => throw "a spread argument needs a tuple contract of required positions"
    let k := elements.length
    let fixedActuals := if spread then args.length - 1 else args.length
    let anonymous := held ⟨"",some e.span⟩
    let temporaries := (operands.map fun a => held ⟨"",some a.span⟩).reverse ++ headScope
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+n+h+k))⟩
    -- An actual sits above the elements a spread reads; a receiver, which is
    -- an operand and not an actual, sits below them all.
    let actuals := ((List.range fixedActuals).map fun i =>
        let v := Tm.var (k + args.length - 1 - i)
        if copied.contains i then .spread v
        else if spreads.contains i && variadic then .spread (.readAt SourceTypes.storeField v) else v) ++
      (List.range k).map fun j => Tm.var (k-1-j)
    let callEnv := elements.reverse ++ As.reverse ++ headTys ++ Γ
    -- `.call` passes its first operand as the receiver; a plain call passes
    -- `undefined`.
    let callTerm := match e with
      | .callWithReceiver .. => Tm.invoke (.var (k+n)) (.var (k+n-1)) actuals
      | .invoke .. => Tm.invoke (.var (k+n)) (.var (k+n+h-1)) actuals
      | _ => Tm.call (.var (k+n)) actuals
    -- The receiver the call passes, the `.call` operand or `undefined`, is
    -- checked where the call is made at the selected signature's receiver:
    -- a located obligation, apart from the call's own typing.
    let G := SourceTypes.graph (← table)
    let callScope := (List.replicate k anonymous) ++ temporaries ++ scope
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
    let reads ← (List.range k).reverse.foldlM (fun next j => do
      let some E := elements[j]? | throw "a spread element has no contract"
      let index ← indexTerm j
      let env := (elements.take j).reverse ++ As.reverse ++ headTys ++ Γ
      emitAt e.span (.elemAt (.readAt SourceTypes.storeField (.var j)) index) (.bind next)
        env E "spread-element"
        (scope := (List.replicate j anonymous) ++ temporaries ++ scope)) call
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
    match method with
    | none => compileExpr fc scope Γ callee right
    | some (o, key, readTerm) =>
      -- The method is read from the saved object, below any saved key.
      let saved := headTys.drop 1
      let read ← emitAt callee.span (readTerm (.var (saved.length - 1))) (.bind ⟨right.label, none⟩)
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
    let _ ← arrayObject S
    let make ← emitAt e.span (arrayTerm proto) (.bind drop)
      (S :: As.reverse ++ Γ) A (scope := makeScope)
    let store ← emitAt e.span (.arrLit ((List.range n).map fun i => .var (n-1-i))) (.bind make)
      (As.reverse ++ Γ) S (scope := temporaries ++ scope)
    elems.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) =>
      compileExpr fc
        ((elems.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++ scope)
        ((As.take i).reverse ++ Γ) arg next) store
  | .elemAt _ receiver key =>
    let B ← exprType fc receiver
    let K ← exprType fc key
    let index ← arrayKeyTerm K
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    let node ← emitAt e.span (.elemAt (.readAt SourceTypes.storeField (.var 1)) index) (.bind drop)
      (K::B::Γ) A (scope := temporaries)
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
    let node ← emitAt e.span (.readAt fld (.var 1)) (.bind drop) (K::B::Γ) A (scope := temporaries)
    let right ← compileExpr fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) key node
    compileExpr fc scope Γ receiver right
  | .index _ none receiver key =>
    let B ← exprType fc receiver
    let K ← exprType fc key
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let temporaries := held ⟨"",some key.span⟩::held ⟨"",some receiver.span⟩ :: scope
    let node ← emitAt e.span (.indexAt (.var 1) (.var 0)) (.bind drop) (K::B::Γ) A
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
  | .update _ op target rhs post =>
    -- The target's parts are evaluated once and its value read at the
    -- storage contract, never at a claim; then the right side, the
    -- operation, the write back at the contract, and the old or new value.
    let G := SourceTypes.graph (← table)
    let N : Ty Nat := [← lower (SourceTypes.use .num)]
    let fieldType := fun (B : Ty Nat) (fld : PropKey) => do
      match PositiveRules.expand G B with
      | [.refs fs [] []] =>
        let some T := fs.lookup fld | throw s!"update of a field '{fld}' the contract does not name"
        pure T
      | _ => throw "a compound assignment needs one cell contract"
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
    let one := (1.0 : Float).toBits
    let C ← match rhs with
      | some r => exprType fc r
      | none => do pure [← lower (SourceTypes.use (.numLit one))]
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
      | none => emitAt e.span (.num one) (.bind combine) (T::K) C (scope := after.drop 2)
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
      | [.refs fs [] []] =>
        let some T := fs.lookup fld | throw s!"update of a field '{fld}' the contract does not name"
        pure T
      | _ => throw "a logical assignment needs one cell contract"
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
  match cond with
  | .logical _ andOp left right =>
    let _ ← closureExpr fc scope Γ cond
    let H := conditionContext (SourceTypes.graph (← table)) scope Γ left andOp
    let rhs ← compileCondition fc scope H right yes no
    compileCondition fc scope Γ left (if andOp then rhs else yes) (if andOp then no else rhs)
  | .not _ e =>
    let _ ← closureExpr fc scope Γ cond
    compileCondition fc scope Γ e no yes
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
private partial def arrayAssigns (fc : SourceClaims.Function) (pos : Span) (A : Ty Nat) (after : Target) :
    List ScopeBinding → List (Ty Nat) → Nat → List (Fragment.ArrayElem Fragment.Expr) → Compiler Target
  | _, _, _, [] => pure after
  | scope, Γ, obj, q :: more => do
    let R ← positionRead (SourceTypes.graph (← table)) A q.index
    let bound := held ⟨"",some q.namePos⟩
    let term := Tm.elemAt (.readAt SourceTypes.storeField (.var obj)) (.num (bitsOfNat q.index))
    readWithDefault fc pos q.namePos term R q.default_ bound scope Γ fun T => do
      let some (i, .cell ..) := resolve (bound::scope) q.name
        | throw s!"assignment to '{q.name}', which is not a mutable local"
      let rest ← arrayAssigns fc pos A after scope Γ obj more
      let dropped : Target := ⟨rest.label, some ((rest.mapping.getD (List.range Γ.length)).map (·+1))⟩
      emitAt q.namePos (.writeAt valueField (.var i) (.var 0)) (.effect dropped) (T::Γ) [0]
        "storage-contract" (some pos.1) (scope := bound::scope)

end

/-- The nearest enclosing loop, with the lexical scope at each destination. -/
private structure LoopTargets where
  again : Target × List ScopeBinding
  done : Option (Target × List ScopeBinding)

/-- Where a statement begins: the entry the producer states for it. -/
private def stmtStart : Fragment.Stmt → Nat
  | .brk p | .cont p | .ret p _ | .constants p _ | .mutables p _ | .pattern p _ _ | .arrayPattern p _ _
  | .effect p _ | .loop p _ _ | .ite p _ _ _ => p.1

/-- The bindings an object pattern yields, left to right, over the object held
at slot `obj`: each binds its read at the contract's field type. `after`
compiles what follows the statement. -/
private def patternProps (fc : SourceClaims.Function) (pos : Span)
    (fields : List (PropKey × Ty Nat)) (after : List ScopeBinding → Compiler Target) :
    List ScopeBinding → List (Ty Nat) → Nat → List Fragment.PatternProp → Compiler Target
  | scope, Γ, obj, [] => do
    -- The statement is over: the object's anonymous slot, below the `obj`
    -- bindings, is dropped before the next statement's named environment.
    let next ← after (scope.take obj ++ scope.drop (obj+1))
    pure ⟨next.label, some ((next.mapping.getD (List.range (Γ.length-1))).map
      (fun j => if j < obj then j else j+1))⟩
  | scope, Γ, obj, q :: more => do
    if q.name == "undefined" then throw "shadowing undefined is outside the fragment"
    if (names scope).contains q.name then throw s!"duplicate or shadowing local declaration '{q.name}'"
    let some R := fields.lookup (.str q.field)
      | throw s!"pattern reads a field '{q.field}' the contract does not name"
    let bound := held ⟨q.name,some pos⟩
    readWithDefault fc pos q.namePos (.readAt q.field (.var obj)) R q.default_ bound scope Γ
      fun T => patternProps fc pos fields after (bound::scope) (T::Γ) (obj+1) more

/-- The bindings an array pattern yields, left to right, over the array held
at slot `obj`: each binds the read of its position of the store. -/
private def arrayElems (fc : SourceClaims.Function) (pos : Span) (A : Ty Nat)
    (after : List ScopeBinding → Compiler Target) :
    List ScopeBinding → List (Ty Nat) → Nat → List (Fragment.ArrayElem Fragment.Expr) → Compiler Target
  | scope, Γ, obj, [] => do
    let next ← after (scope.take obj ++ scope.drop (obj+1))
    pure ⟨next.label, some ((next.mapping.getD (List.range (Γ.length-1))).map
      (fun j => if j < obj then j else j+1))⟩
  | scope, Γ, obj, q :: more => do
    if q.name == "undefined" then throw "shadowing undefined is outside the fragment"
    if (names scope).contains q.name then throw s!"duplicate or shadowing local declaration '{q.name}'"
    let R ← positionRead (SourceTypes.graph (← table)) A q.index
    let bound := held ⟨q.name,some pos⟩
    let term := Tm.elemAt (.readAt SourceTypes.storeField (.var obj)) (.num (bitsOfNat q.index))
    readWithDefault fc pos q.namePos term R q.default_ bound scope Γ
      fun T => arrayElems fc pos A after (bound::scope) (T::Γ) (obj+1) more

/-- The declarators of a `const`, bound left to right under the one entry `Γ`
the producer states for the statement: each initializer is compiled in the
scope the earlier bindings extend, and no cut separates them, because the
producer states none. `after` compiles what follows the whole statement. -/
private def constants (fc : SourceClaims.Function) (pos : Span)
    (after : List ScopeBinding → Compiler Target) :
    List ScopeBinding → List (Ty Nat) → List Fragment.Binding → Compiler Target
  | scope, _, [] => after scope
  | scope, Γ, b :: more => do
    if b.name == "undefined" then throw "shadowing undefined is outside the fragment"
    if (names scope).contains b.name then throw s!"duplicate or shadowing local declaration '{b.name}'"
    let A ← exprType fc b.init
    let B ← match b.annot with | none => pure A | some ty => lower (Fragment.translate ty)
    let next ← constants fc pos after (held ⟨b.name,some pos⟩::scope) (A::Γ) more
    let annotation ← emitAt b.init.span (.var 0) (.effect next) (A::Γ) B "binding-annotation" (some pos.1)
      (scope := held ⟨b.name,some b.init.span⟩::scope)
    compileExpr fc scope Γ b.init annotation

/-- The declarators of a `let`, each allocating its own private cell, in the
same left-to-right order under the statement's one entry. An unannotated
binding's contract is read at `next`, the entry of the statement that follows
the whole list: the first place every binding of the list stands in scope. -/
private def mutables (fc : SourceClaims.Function) (pos : Span) (next : Option Nat)
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
        let some start := next
          | throw s!"no claimed storage contract for '{b.name}' at {pos.1}"
        let some candidate := (fc.envs.lookup start).bind (·.lookup b.name)
          | throw s!"no claimed storage contract for '{b.name}' at {start}"
        (SourceClaims.resolve (← table).length candidate).mapError fun msg =>
          s!"storage contract for '{b.name}' at {start}: {msg}"
    let reference ← lower (do return [← CellClaims.reference [(valueField, contract)]])
    -- The slot holds the identity of a cell only this lowering allocated.
    -- Storage is decided here, by the declaration, and nowhere else.
    let binding : ScopeBinding := { source := ⟨b.name,some pos⟩, storage := .cell contract reference }
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
private def body : Nat → SourceClaims.Function → Ty Nat → List ScopeBinding → List Fragment.Stmt →
    Option (Target × List ScopeBinding) → Option LoopTargets → Compiler Target
  | 0, _, _, _, _, _, _ => throw "internal extraction error: exhausted structural traversal"
  | fuel+1, fc, R, scope, stmts, tail, loopTargets => do
    let target ← match stmts with
    | [] => leave fc.namePos R scope tail
    | .brk pos :: rest | .cont pos :: rest =>
      if !rest.isEmpty then throw "statements after break or continue are outside the fragment"
      let some targets := loopTargets | throw "break or continue outside a source loop"
      let Γ ← env fc pos.1 scope
      let destination := match stmts with
        | .brk _ :: _ => targets.done
        | _ => some targets.again
      let next ← leave fc.namePos R scope destination
      emitAt pos .nul (.effect next) Γ [0] (scope := scope)
    | .ret pos e :: rest =>
      if !rest.isEmpty then throw "statements after return are outside the fragment"
      let Γ ← env fc pos.1 scope
      let A ← exprType fc e
      let done ← emitAt e.span (.var 0) .ret (A::Γ) R "return-contract" (some pos.1)
        (scope := held ⟨"",some e.span⟩ :: scope)
      compileExpr fc scope Γ e done
    | .constants pos bindings :: rest =>
      let Γ ← env fc pos.1 scope
      constants fc pos (fun scope => body fuel fc R scope rest tail loopTargets) scope Γ bindings
    | .ite pos cond thn els :: rest =>
      let Γ ← env fc pos.1 scope
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail loopTargets
        pure (some (next,scope))
      let yes ← body fuel fc R scope thn continuation loopTargets
      let no ← body fuel fc R scope (els.getD []) continuation loopTargets
      compileCondition fc scope Γ cond yes no
    | .loop pos cond loopBody :: rest =>
      let Γ ← env fc pos.1 scope
      -- Reserve a stable label for incoming and back edges. Replace its stub
      -- before returning; the completed program is independently checked.
      let head ← emitAt cond.span .nul .ret Γ [0] (scope := scope)
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail loopTargets
        pure (some (next,scope))
      let yes ← body fuel fc R scope loopBody (some (head,scope)) (some ⟨(head,scope),continuation⟩)
      let no ← leave fc.namePos R scope continuation
      let condition ← compileCondition fc scope Γ cond yes no
      modify fun s => { s with program := s.program.set head.label ⟨.nul,.effect condition⟩ }
      let facts ← entryFacts fc pos.1 scope
      let links := distinctLinks (SourceTypes.graph (← table)) scope Γ
      if !facts.isEmpty || !links.isEmpty then
        modify fun s => { s with
          assertions := s.assertions ++ [(head.label,⟨facts,[],links⟩)]
          sourceMap := s.sourceMap.set head.label (some ⟨pos,"heap-observation",some pos.1,sources scope⟩) }
      modify fun s => { s with cuts := head.label :: s.cuts }
      pure head
    | .mutables pos bindings :: rest =>
      let Γ ← env fc pos.1 scope
      mutables fc pos (rest.head?.map stmtStart)
        (fun scope => body fuel fc R scope rest tail loopTargets) scope Γ bindings
    | .pattern pos props init :: rest =>
      let Γ ← env fc pos.1 scope
      let A ← exprType fc init
      let G := SourceTypes.graph (← table)
      let [.refs fields [] []] := PositiveRules.expand G A
        | throw "an object pattern requires a single record contract"
      -- The object is held anonymously for the whole statement, below the
      -- bindings it yields; the reads address it by its slot.
      let next ← patternProps fc pos fields (fun scope => body fuel fc R scope rest tail loopTargets)
        (held ⟨"",some init.span⟩ :: scope) (A::Γ) 0 props
      compileExpr fc scope Γ init next
    | .arrayPattern pos elems init :: rest =>
      let Γ ← env fc pos.1 scope
      let A ← exprType fc init
      -- The array is held anonymously for the whole statement, below the
      -- bindings it yields; the reads address its store by its slot.
      let next ← arrayElems fc pos A (fun scope => body fuel fc R scope rest tail loopTargets)
        (held ⟨"",some init.span⟩ :: scope) (A::Γ) 0 elems
      compileExpr fc scope Γ init next
    | .effect pos e :: rest =>
      let Γ ← env fc pos.1 scope
      let next ← body fuel fc R scope rest tail loopTargets
      let drop := ⟨next.label, some ((next.mapping.getD (List.range Γ.length)).map (·+1))⟩
      compileExpr fc scope Γ e drop
    match stmts with
    | [] | .loop .. :: _ => return target
    | st :: _ =>
      let pos := match st with
        | .brk p | .cont p | .ret p _ | .constants p _ | .mutables p _ | .pattern p _ _ | .arrayPattern p _ _ | .effect p _ | .loop p _ _ | .ite p _ _ _ => p
      let facts ← entryFacts fc pos.1 scope
      let entry ← checkpoint pos (← env fc pos.1 scope) facts target (some pos.1) scope
      modify fun s => { s with cuts := entry.label :: s.cuts }
      return entry

private def traversalBudget : List Fragment.Stmt → Nat
  | [] => 1
  | .brk .. :: rest | .cont .. :: rest | .ret .. :: rest | .constants .. :: rest | .mutables .. :: rest | .pattern .. :: rest | .arrayPattern .. :: rest | .effect .. :: rest => 1 + traversalBudget rest
  | .loop _ _ loopBody :: rest => 1 + traversalBudget loopBody + traversalBudget rest
  | .ite _ _ thn none :: rest => 2 + traversalBudget thn + traversalBudget rest
  | .ite _ _ thn (some els) :: rest =>
      1 + traversalBudget thn + traversalBudget els + traversalBudget rest
termination_by stmts => sizeOf stmts


structure SourceRequest extends Request where
  obligations : List ExpressionClaims.Required
  sourceMap : SourceMap := []
  assertions : List (Nat × HeapKnowledge.Knowledge) := []
  /-- Full statement-entry interfaces; absent assertions mean empty knowledge. -/
  cuts : List Nat := []
  /-- Labels the program mentions but no claim does: search hints only. -/
  hints : List Nat := []

/-- Search hints only: the primitives and the labels the request mentions, so
a coercion does not consider every unrelated signature in the table. The
consumer still checks against the complete graph and the exact request. -/
def SourceRequest.searchLabels (r : SourceRequest) : List Nat :=
  let roots := ([0,1,2,3] ++ r.result ++ r.inputs.flatten ++ r.hints ++
    r.claims.flatMap (fun (c : PointClaim Nat) => c.type ++ c.context.flatten) ++
    r.obligations.flatMap (fun (o : ExpressionClaims.Required) => o.sequent.type ++ o.sequent.context.flatten)).eraseDups
  -- Readonly array coercions depend on the store's element unions two levels
  -- below the object. Close the vocabulary over the finite reachable graph.
  (List.range r.types.length).foldl (fun known _ =>
    (known ++ known.flatMap (fun i => ((r.types[i]?.map RequestJson.Row.union).getD []).flatMap
      (fun c => (RequestJson.clauseTypes c).flatten))).eraseDups) roots

/-- A value of the module a code unit reaches: its name, its declaration's
position, and its source type (a function's signature, a constant's
annotation), or why it has none. -/
abbrev ModuleValue := String × Span × Except String Json

/-- The table is the one the claims were lowered into; annotations the claims
did not mention grow it, and the request carries the result. -/
def extractNormalizedFn (T : SourceTypes.Table) (f : Fragment.Fn) (fc : SourceClaims.Function)
    (module : List ModuleValue := []) : Except String SourceRequest := do
  if f.name != fc.name || f.namePos != fc.namePos then throw "function claim identity mismatch"
  let scope : List ScopeBinding := f.params.map (fun p => held ⟨p.name,none⟩)
  -- The module functions this body mentions, outermost: a parameter or local
  -- of the same name shadows one, as in JavaScript.
  let mentioned := f.body.flatMap stmtNames
  let siblings := module.filter fun g => mentioned.contains g.1 || g.1 == arrayPrototypeName
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
      let ty ← match ty with
        | Except.ok ty => pure ty
        | Except.error reason => throw (locatedRefusal (← table) pos .bindingAnnotation reason)
      lower (Fragment.translate ty)
    let siblingScope : List ScopeBinding :=
      (siblings.zip siblingTypes).map fun (pair : ModuleValue × Ty Nat) =>
        { source := ⟨pair.1.1, some pair.1.2.1⟩, fixed := some pair.2 }
    if f.params.dropLast.any (fun (p : Fragment.Param) => p.rest) then
      throw "a rest parameter must be the last one"
    -- A mutable `T[]` rest is an ordinary input: the body is checked for every
    -- array of that contract, the fresh one a call collects among them.
    let tupleRest := match f.params.getLast? with
      | some p => p.rest && (Fragment.arrayElement p.ty).isNone
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
    -- caller contract, as it is for arrows (DESIGN.md, the trust boundary).
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
        pure { b with storage := .cell contract reference }
      else pure b
    let bodyScope := paramScope ++ siblingScope
    let slotTypes := bindings ++ siblingTypes
    let fullScope := scope ++ siblingScope
    let mut first ← body (traversalBudget stmts) fc R bodyScope stmts none none
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
  return ⟨⟨built.types, built.program, built.claims, R, entry.label, inputs⟩,
    built.obligations, built.sourceMap, built.assertions, built.cuts, built.hints⟩

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

/-- Statement entries are exact interfaces. Expression observation checkpoints
inside a statement require entailment but do not reset its local context. -/
def checkAssertions (r : SourceRequest) (c : Response) : Bool :=
  (r.cuts.all fun l => match c.certificate[l]? with
    | none => false
    | some n => n.knowledge == (r.assertions.lookup l).getD ⟨[],[],[]⟩) &&
  (r.assertions.all fun (l,k) => match c.certificate[l]? with
    | none => false
    | some n => HeapKnowledge.check n.knowledge k none)

/-- Accepted source evidence has exactly the supplied knowledge at every
statement entry, even when that knowledge is empty. -/
theorem checkAssertions_cut {r : SourceRequest} {c : Response}
    (hc : checkAssertions r c = true) {l node} (hm : l ∈ r.cuts)
    (hn : c.certificate[l]? = some node) :
    node.knowledge = (r.assertions.lookup l).getD ⟨[],[],[]⟩ := by
  simp only [checkAssertions, Bool.and_eq_true] at hc
  have h := List.all_eq_true.mp hc.1 l hm
  simpa [hn] using h

theorem checkAssertions_sound {r : SourceRequest} {c : Response}
    (hc : checkAssertions r c = true) {l k node ρ heap}
    (hm : (l,k) ∈ r.assertions) (hn : c.certificate[l]? = some node)
    (hk : HeapKnowledge.Holds node.knowledge ρ heap) : HeapKnowledge.Holds k ρ heap := by
  simp only [checkAssertions, Bool.and_eq_true] at hc
  have h := List.all_eq_true.mp hc.2 (l,k) hm
  simp only [hn] at h
  exact HeapKnowledge.check_sound (m := none) h hk

def checkRequests (rs : List SourceRequest) (b : Bundle) : Bool :=
  rs.length == b.functions.length && rs.length == b.obligations.length &&
    (rs.zip b.functions).all (fun (r,c) => verify r.toRequest c && checkAssertions r c) &&
    (rs.zip b.obligations).all (fun (r,es) =>
      ExpressionClaims.checkAll (RequestJson.graph r.toRequest) r.types.length r.obligations es)

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

/-- Every supplemental claim is a derivable sequent in the same calculus. -/
theorem checkRequests_obligations {rs : List SourceRequest} {b : Bundle}
    (h : checkRequests rs b = true) {r es} (hm : (r,es) ∈ rs.zip b.obligations)
    {q e} (hq : (q,e) ∈ r.obligations.zip es) :
    HasTy (RequestJson.graph r.toRequest) q.sequent.context q.sequent.term q.sequent.type := by
  simp only [checkRequests, Bool.and_eq_true, List.all_eq_true] at h
  exact ExpressionClaims.checkAll_sound (h.2 _ hm) hq

#print axioms checkRequests_assertions
#print axioms checkAssertions_cut
#print axioms checkAssertions_sound
#print axioms checkRequests_obligations
#print axioms checkRequests_safe
end Verification.Model.SourceExtraction
