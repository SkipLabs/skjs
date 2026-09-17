import Verification.ExperimentState.SkjsSourceClaims
import Verification.ExperimentState.ExpressionClaims
import Verification.ExperimentState.GenericSource
import Verification.ExperimentState.GenericAlias

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
namespace Verification.ExperimentState.SourceExtraction
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment

private def distinct [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

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
  deriving Repr

private def held (d : Descriptor) : ScopeBinding := ⟨d, .value⟩

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

private abbrev Compiler := StateT Built (Except String)

private def table : Compiler SourceTypes.Table := do return (← get).types

private def lower (m : SourceTypes.Lowering α) : Compiler α := do
  let s ← get
  let (a, T) ← m.run s.types
  set { s with types := T }
  return a

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
        | [.numLit bits] => some (.numEq bits)
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
  | .alloc p ns es => return .alloc p ns (← es.mapM (comparisonsExpr fc))
  | .read p f e => return .read p f (← comparisonsExpr fc e)
  | .write p f l r => return .write p f (← comparisonsExpr fc l) (← comparisonsExpr fc r)
  | .withValue p f i ft bt => return .withValue p (← comparisonsExpr fc f) (← comparisonsExpr fc i) ft bt
  | .lambda p ps result b => return .lambda p ps result (← comparisonsExpr fc b)
  | .bindWithReceiver p c r args => return .bindWithReceiver p (← comparisonsExpr fc c) (← comparisonsExpr fc r) (← args.mapM (comparisonsExpr fc))
  | .callWithReceiver p c r args => return .callWithReceiver p (← comparisonsExpr fc c) (← comparisonsExpr fc r) (← args.mapM (comparisonsExpr fc))
  | .call p c args => return .call p (← comparisonsExpr fc c) (← args.mapM (comparisonsExpr fc))
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
  | .not _ e | .read _ _ e | .shapeTest _ _ _ e | .atEnv _ e
  | .lambda _ _ _ e => assignsExpr name e
  | .equality _ _ a b | .logical _ _ a b | .coalesce _ a b
  | .singletonTest _ _ _ _ a b | .write _ _ a b | .withValue _ a b _ _
  | .seqBody _ a b | .letBody _ _ _ a b => assignsExpr name a || assignsExpr name b
  | .alloc _ _ es => es.any (assignsExpr name)
  | .call _ f args => assignsExpr name f || args.any (assignsExpr name)
  | .callWithReceiver _ f r args | .bindWithReceiver _ f r args =>
    assignsExpr name f || assignsExpr name r || args.any (assignsExpr name)
  | .ifBody _ _ c t e => assignsExpr name c || assignsExpr name t || assignsExpr name e

private partial def assignsStmt (name : String) : Fragment.Stmt → Bool
  | .ret _ e | .effect _ e => assignsExpr name e
  | .constants _ bs | .mutables _ bs => bs.any fun b => assignsExpr name b.init
  | .pattern _ props init => assignsExpr name init ||
    props.any fun q => (q.default_.map (assignsExpr name)).getD false
  | .ite _ c t e => assignsExpr name c || t.any (assignsStmt name) ||
    (e.getD []).any (assignsStmt name)
  | .loop _ c b => assignsExpr name c || b.any (assignsStmt name)
  | .brk .. | .cont .. => false

/-- A terminal branch uses the enclosing source result annotation, not a
fabricated expression claim at the if statement's span. -/
private def closureType (fc : SourceClaims.Function) : Fragment.Expr → Compiler (Ty Nat)
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

/-- A checkpoint is an actual no-op graph node. Every incoming edge must
justify its supplied current-heap assertion, including backedges. -/
private def checkpoint (pos : Span) (Γ : List (Ty Nat)) (facts : HeapFacts.Facts)
    (next : Target) (entry : Option Nat := none) (scope : List ScopeBinding := []) :
    Compiler Target := do
  if facts.isEmpty then return next
  let t ← emitAt pos .nul (.effect next) Γ [0] "heap-observation" entry scope
  modify fun s => { s with assertions := s.assertions ++ [(t.label,⟨facts,[],[]⟩)] }
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
    (fld : String) (R : Ty Nat) : Compiler Unit := do
  -- The obligation below is an inclusion of types, so the observed type needs
  -- only to be one this table names. It does not need a supported primitive predicate:
  -- that is what a primitive assertion on an edge needs, and this is not one.
  if !RequestJson.validTy (← table).length R then throw "invalid current-content type label"
  let clauses := PositiveRules.expand (SourceTypes.graph (← table)) A
  if clauses.isEmpty then throw "current-content assertion requires nonempty cell contracts"
  let invariants ← clauses.mapM fun clause => do
    let .refs W [] := clause
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
-- A saved local value is different from a field of the object it contains.
-- This prefix cannot begin a source identifier or a name.field snapshot.
private def localSnapshotName (name : String) : String := ".local:" ++ name
private def isSnapshot (name : String) : Bool := name.any (· == '.')

private def observed (scope : List ScopeBinding) (Γ : List (Ty Nat))
    (snapshot : String) (d : Descriptor) (pos : Span) (A : Ty Nat)
    (fld : String) (R : Ty Nat) : Compiler Unit := do
  if let some i := (names scope).idxOf? snapshot then
    let plan := DirectProof.var Γ i R
    obligation pos plan.goal (some plan) "heap-observation" scope
  else
    persistentObservation d pos A fld R

/-- A saved read is usable only in a subtree with no possible heap effects or
escaping closure. Reads are plain modeled cells, never JavaScript accessors. -/
private def readOnly : Fragment.Expr → Bool
  | .var .. | .lit .. | .done .. => true
  | .not _ e | .read _ _ e | .shapeTest _ _ _ e | .atEnv _ e => readOnly e
  | .equality _ _ a b | .singletonTest _ _ _ _ a b | .logical _ _ a b | .coalesce _ a b
  | .seqBody _ a b | .letBody _ _ _ a b => readOnly a && readOnly b
  | .ifBody _ _ c t e => readOnly c && readOnly t && readOnly e
  | .alloc .. | .write .. | .assign .. | .nullishAssign .. | .lambda .. | .withValue .. | .bindWithReceiver ..
  | .callWithReceiver .. | .call .. => false

/-- Save the plain read in a singleton comparison. The other operand is
necessarily a literal; moving that literal across the read has no effect. -/
private def readGuard (scope : List ScopeBinding) :
    Fragment.Expr → Option (String × Fragment.Expr × Fragment.Expr)
  | .not pos e => (readGuard scope e).map fun (snapshot,r,c) => (snapshot,r,.not pos c)
  | .singletonTest pos tag equal testLeft left right => do
    let (r,lit) := if testLeft then (left,right) else (right,left)
    let .lit .. := lit | none
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
  let captured := scope.filter (fun b => b.source.name != "" && !isSnapshot b.source.name)
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
        observed scope Γ (snapshotName name fld) ⟨name,none⟩ (pos,pos+1) receiver fld R
  (scope.zipIdx).mapM fun (b,i) => do
    let name := b.source.name
    let A := if name == "" || isSnapshot name then Γ[i]? else H[named.idxOf name]?
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

/-- Select an exact-arity signature, preferring one covering every actual type. -/
private def selectSignature (L : PositiveRules.Ops Nat) (As : List (Ty Nat)) :
    Except String (List (Ty Nat) × Ty Nat) := do
  let choices := L.filter fun p => p.1.length == As.length
  let some p := (choices.find? fun p => (As.zip p.1).all fun (A,D) => A.all D.contains) <|> choices.head?
    | throw "callee has no signature with the actual argument count"
  return p

/-- Nest saved operand plans in their original evaluation order. -/
private def saveOperands (ps : List DirectProof.Plan) (body : DirectProof.Plan) : DirectProof.Plan :=
  ps.foldr (fun p b => DirectProof.letE p.goal.context p b) body

private def creationChildren : DirectProof.Plan → Option (List DirectProof.Plan)
  | .cast _ p => creationChildren p
  | .rule _ .funE ps => some ps
  | _ => none
private def allocationChildren : DirectProof.Plan → Option (List DirectProof.Plan)
  | .cast _ p => allocationChildren p
  | .rule _ .alloc ps => some ps
  | _ => none

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
      | .var _ name => observed scope Γ (snapshotName name fld) ⟨"",some e.span⟩ e.span A fld R
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
  | .alloc _ ns es => do
    let [.refs B []] := PositiveRules.expand G A
      | throw "allocation claim must name a record contract"
    if B.length != ns.length then throw "allocation claim names different fields"
    let B ← ns.mapM fun name => do
      let some D := B.lookup name | throw "allocation claim names different fields"
      pure (name,D)
    let Ref ← lower (CellClaims.reference B)
    if es.length != ns.length then throw "allocation initializer count mismatch"
    -- Every initializer is checked in the lexical context of the literal, which
    -- is what the allocation rule asks for; the calculus still evaluates them
    -- left to right, and the rule's soundness carries each claim forward.
    let ps ← es.mapM fun a => closureExpr fc scope Γ a
    let casts := (ps.zip (B.map Prod.snd)).map fun (p,D) => DirectProof.cast Γ D p
    pure (DirectProof.node Γ (.makeAt .absent ns (ps.map (·.term))) [Ref] .alloc casts)
  | .read _ fld a => do
    let receiver := a
    let a ← closureExpr fc scope Γ a
    let snapshot := match receiver with
      | .var _ name => (names scope).idxOf? (snapshotName name fld)
      | _ => none
    if let some i := snapshot then
      let some R := Γ[i]? | throw "internal saved-read slot mismatch"
      pure (DirectProof.var Γ i R)
    else match PositiveRules.expand G a.type with
    | [.refs fs []] =>
      let some B := fs.lookup fld | throw s!"read of a field '{fld}' the contract does not name"
      pure (DirectProof.node Γ (.readAt fld a.term) B .read [a])
    | [.callable fs _ _] =>
      let some B := fs.lookup fld | throw s!"read of a field '{fld}' the contract does not name"
      pure (DirectProof.node Γ (.readAt fld a.term) B .readCallable [a])
    | _ =>
      if a.type.length ≤ 1 then throw "read receiver must name a cell contract"
      let alternatives ← a.type.mapM fun label => do
        let [.refs fs []] := PositiveRules.expand G [label]
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
  | .bindWithReceiver _ f receiver args => do
    let callee ← closureExpr fc scope Γ f
    let receiverPlan ← closureExpr fc (held ⟨"",some f.span⟩ :: scope) (callee.type::Γ) receiver
    let startScope := held ⟨"",some receiver.span⟩::held ⟨"",some f.span⟩ :: scope
    let (plans,K,_) ← args.attach.foldlM (fun (ps,H,ds) ⟨arg,_⟩ => do
      let p ← closureExpr fc ds H arg
      pure (ps ++ [p],p.type::H,held ⟨"",some arg.span⟩ :: ds))
      ([callee,receiverPlan],receiverPlan.type::callee.type::Γ,startScope)
    let G := SourceTypes.graph (← table)
    let [.arrs [(Ds,R)]] := PositiveRules.expand G A
      | throw "bound function claim requires one free signature"
    let L ← match PositiveRules.expand G callee.type with
      | [.arrs L] | [.callable _ _ L] => pure L
      | _ => throw "bind target requires a single callable contract"
    let boundTypes := (plans.drop 2).map (·.type)
    let (domains,result) ← selectSignature L (boundTypes ++ Ds)
    let H := Ds ++ K
    let indexes := (List.range args.length).map (fun i => Ds.length + args.length - 1 - i) ++
      List.range Ds.length
    let fn := DirectProof.var H (Ds.length + args.length + 1) callee.type
    let actuals := (indexes.zip domains).map fun (i,D) => DirectProof.var H i D
    let rule := match PositiveRules.expand G callee.type with
      | [.callable ..] => ProgramCertificates.Rule.callCallable
      | _ => .app
    let body := DirectProof.cast H R
      (DirectProof.node H (.call fn.term (actuals.map (·.term))) result rule (fn::actuals))
    let bound := DirectProof.node K (.make (.closure Ds.length body.term) .nul) A .funE [body]
    pure (saveOperands plans bound)
  | .callWithReceiver _ f receiver args => do
    let callee ← closureExpr fc scope Γ f
    let K := callee.type :: Γ
    let receiverPlan ← closureExpr fc (held ⟨"",some f.span⟩ :: scope) K receiver
    let H := receiverPlan.type :: K
    let ds := held ⟨"",some receiver.span⟩::held ⟨"",some f.span⟩ :: scope
    let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr fc ds H a
    let L ← match PositiveRules.expand G callee.type with
      | [.arrs L] | [.callable _ _ L] => pure L
      | _ => throw ".call target requires a single callable contract"
    let (Ds,R) ← selectSignature L (actuals.map (·.type))
    let rule := match PositiveRules.expand G callee.type with
      | [.callable ..] => ProgramCertificates.Rule.callCallable
      | _ => .app
    let call := DirectProof.node H (.call (.var 1) (actuals.map (·.term))) R rule
      (DirectProof.var H 1 callee.type :: (actuals.zip Ds).map fun (a,D) => DirectProof.cast H D a)
    pure (DirectProof.letE Γ callee (DirectProof.letE K receiverPlan call))
  | .call _ f args => do
    let callee ← closureExpr fc scope Γ f
    match PositiveRules.expand G callee.type with
    | [.arrs L] | [.callable _ _ L] =>
      let rule := match PositiveRules.expand G callee.type with
        | [.callable ..] => ProgramCertificates.Rule.callCallable
        | _ => .app
      let actuals ← args.attach.mapM fun ⟨a,_⟩ => closureExpr fc scope Γ a
      let (Ds,R) ← selectSignature L (actuals.map (·.type))
      pure (DirectProof.node Γ (.call callee.term (actuals.map (·.term))) R rule
        (callee :: (actuals.zip Ds).map fun (a,D) => DirectProof.cast Γ D a))
    | _ =>
      if callee.type.length ≤ 1 then throw "callee must name a source arrow"
      -- Save callee first, then each actual, before splitting its immutable slot.
      let (_,_,actuals) ← args.attach.foldlM (fun (ctx,sc,ps) ⟨a,_⟩ => do
        let p ← closureExpr fc sc ctx a
        pure (p.type::ctx,held ⟨"",some a.span⟩::sc,ps ++ [p]))
        (callee.type::Γ,held ⟨"",some f.span⟩ :: scope,[])
      let As := actuals.map (·.type)
      let alternatives ← callee.type.mapM fun label => do
        let [.arrs L] := PositiveRules.expand G [label]
          | throw "every callee alternative must name a source arrow"
        let (Ds,R) ← selectSignature L As
        pure (label,Ds,R)
      let R := (alternatives.flatMap fun (_,_,R) => R).eraseDups
      let n := As.length
      let H := As.reverse ++ callee.type::Γ
      let term := Tm.call (.var n) ((List.range n).map fun i => .var (n-1-i))
      let children := alternatives.map fun (label,Ds,result) =>
        let branch := As.reverse ++ [label]::Γ
        DirectProof.cast branch R (DirectProof.node branch term result .app
          (DirectProof.var branch n [label] ::
            ((As.zip Ds).zipIdx.map fun ((A,D),i) =>
              DirectProof.cast branch D (DirectProof.var branch (n-1-i) A))))
      pure (saveOperands (callee::actuals)
        (DirectProof.node H term R (.unionVar n) children))
  | .write _ fld receiver rhs => do
    let B ← exprType fc receiver
    let single ← match PositiveRules.expand G B with
      | [.refs fs []] =>
        let some D := fs.lookup fld
          | throw s!"write to a field '{fld}' the contract does not name"
        pure (some D)
      | _ => pure none
    let alternatives ← if single.isSome then pure [] else do
      if B.length ≤ 1 then throw "write receiver must name a cell contract"
      B.mapM fun label => do
        let [.refs fs []] := PositiveRules.expand G [label]
          | throw "every write alternative must name a cell contract"
        let some D := fs.lookup fld
          | throw s!"write to a field '{fld}' an alternative does not name"
        pure (label,D)
    let r ← closureExpr fc scope Γ receiver
    let a ← closureExpr fc (held ⟨"",some receiver.span⟩ :: scope) (B::Γ) rhs
    let C := a.type
    let H := C::B::Γ
    let term := Tm.writeAt fld (.var 1) (.var 0)
    let write := match single with
      | some D => DirectProof.node H term [0] .write
          [DirectProof.var H 1 B,DirectProof.cast H D (DirectProof.var H 0 C)]
      | none =>
        let children := alternatives.map fun (label,D) =>
          let branch := C :: [label] :: Γ
          DirectProof.node branch term [0] .write
            [DirectProof.var branch 1 [label],DirectProof.cast branch D (DirectProof.var branch 0 C)]
        DirectProof.node H term [0] (.unionVar 1) children
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
    let [.arrs L] := PositiveRules.expand G F | throw "initializer requires a free function annotation"
    let [.refs P []] := PositiveRules.expand G PRef
      | throw "initializer requires an invariant record annotation"
    let .make (.closure arity body) .nul := f.term | throw "initializer requires a fresh arrow"
    let some bodies := creationChildren f | throw "initializer requires a checked arrow body"
    let some values := allocationChildren property
      | throw "initializer requires a fresh object literal"
    let .alloc _ ns _ := initial | throw "initializer requires a fresh object literal"
    if values.length != P.length then throw "initializer literal does not match its annotation"
    -- Initializers stay in source order. An annotation may list the same fields
    -- in another order; pairing by position would silently rename their values.
    let P ← ns.mapM fun name => do
      let some D := P.lookup name | throw s!"initializer field '{name}' is absent from its annotation"
      pure (name,D)
    let fp := DirectProof.cast Γ F f
    let pp := DirectProof.cast Γ PRef property
    obligation fn.span fp.goal (some fp) "callable-function-annotation" scope
    obligation initial.span pp.goal (some pp) "callable-field-annotation" scope
    let C ← lower (SourceTypes.use (.callable P [] L))
    let casts := (values.zip (P.map Prod.snd)).map fun (v,D) => DirectProof.cast Γ D v
    pure (DirectProof.node Γ
      (.makeAt (.closure arity body) (P.map Prod.fst) (values.map (·.term))) [C] .makeCallable
      (casts ++ bodies))
  | .lambda pos params ret body => do
    let paramNames := params.map Prod.fst
    if !distinct paramNames || paramNames.any (fun name => name == "" || name == "undefined" || (names scope).contains name) then
      throw "shadowing or duplicate closure parameter is outside the fragment"
    let Ds ← params.mapM fun p => lower (Fragment.callableType p.2)
    let R ← lower (Fragment.callableType ret)
    let inner := (paramNames.map fun name => held ⟨name,some pos⟩) ++ scope
    let [.arrs L] := PositiveRules.expand G A | throw "closure claim must name a source arrow"
    if L.isEmpty || !L.all (fun (Di,_) => Di.length == Ds.length && (Di.zip Ds).all (fun (D,A) => D.all A.contains)) then
      throw "closure signature claim is outside the source annotation"
    let b ← closureExpr fc inner (Ds ++ Γ) body
    let annotation := DirectProof.cast (Ds ++ Γ) R b
    obligation pos annotation.goal (some annotation) "closure-result" inner
    let bodies ← L.mapM fun (Di,Ri) => do
      if (Di,Ri) == (Ds,R) then pure annotation
      else return DirectProof.cast (Di ++ Γ) Ri (← closureExpr fc inner (Di ++ Γ) body)
    pure (DirectProof.node Γ (.make (.closure Ds.length b.term) .nul) A .funE bodies)
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

/-- Each expression leaves its result in slot zero and preserves the original
slots after it. Anonymous temporary slots cannot be named by source identifiers.
Mappings discard only the temporaries introduced by this expression. -/
private def compileExpr (fc : SourceClaims.Function) (scope : List ScopeBinding) (Γ : List (Ty Nat))
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
  | .lit _ v => emitAt e.span (← SourceTypes.value v) (.bind next) Γ A (scope := scope)
  | .read _ fld a =>
    let B ← exprType fc a
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let node ← emitAt e.span (.readAt fld (.var 0)) (.bind drop) (B::Γ) A
      (scope := held ⟨"",some a.span⟩ :: scope)
    compileExpr fc scope Γ a node
  | .not _ a =>
    let B ← exprType fc a
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let node ← emitAt e.span (.ite (.var 0) .fls .tru) (.bind drop) (B::Γ) A
      (scope := held ⟨"",some a.span⟩ :: scope)
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
  | .atEnv .. | .letBody .. | .ifBody _ (some _) .. | .done .. | .seqBody .. => throw "statement environment wrapper is only supported inside a closure"
  | .bindWithReceiver .. | .withValue .. | .lambda .. | .ifBody _ none .. | .coalesce .. | .logical .. =>
    let t ← closureExpr fc scope Γ e
    emitAt e.span t.term (.bind next) Γ A (scope := scope)
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
  | .call _ callee args | .callWithReceiver _ callee _ args =>
    let operands := match e with
      | .callWithReceiver _ _ receiver _ => receiver :: args
      | _ => args
    let B ← exprType fc callee
    let As ← operands.mapM (exprType fc)
    let n := As.length
    let temporaries := (operands.map fun a => held ⟨"",some a.span⟩).reverse ++ [held ⟨"",some callee.span⟩]
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+n+1))⟩
    let call ← emitAt e.span (.call (.var n) ((List.range args.length).map fun i => .var (args.length-1-i)))
      (.bind drop) (As.reverse ++ B::Γ) A (scope := temporaries ++ scope)
    let right ← operands.attach.zipIdx.reverse.foldlM (fun next (⟨arg,_⟩,i) =>
      compileExpr fc
        ((operands.take i |>.map fun a => held ⟨"",some a.span⟩).reverse ++ held ⟨"",some callee.span⟩ :: scope)
        ((As.take i).reverse ++ B::Γ) arg next) call
    compileExpr fc scope Γ callee right
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
termination_by e
decreasing_by
  all_goals simp_all +zetaDelta
  all_goals first
    | decreasing_tactic
    | (rcases ‹_ ∨ _› with h | h
       · subst_vars; decreasing_tactic
       · have := List.sizeOf_lt_of_mem h; omega)


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

/-- Compile compound conditions as short-circuit edges. The full source
expression still has an independent claimed typing obligation; the runtime
traverses its operands once instead of evaluating it and then replaying it. -/
private def compileCondition (fc : SourceClaims.Function) (scope : List ScopeBinding)
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
termination_by cond

/-- The nearest enclosing loop, with the lexical scope at each destination. -/
private structure LoopTargets where
  again : Target × List ScopeBinding
  done : Option (Target × List ScopeBinding)

/-- Where a statement begins: the entry the producer states for it. -/
private def stmtStart : Fragment.Stmt → Nat
  | .brk p | .cont p | .ret p _ | .constants p _ | .mutables p _ | .pattern p _ _
  | .effect p _ | .loop p _ _ | .ite p _ _ _ => p.1

/-- The properties of an object pattern, read in order from the object held
in slot `obj`, under the statement's one entry. A property without a default
binds its read at the contract's field type. One with a default dispatches on
the read being undefined: the default is compiled only on that arm, the
defined slice of the read is the other, and both arms join at a node typed
by their union, which every incoming edge must establish. `after` compiles
what follows the statement. -/
private def patternProps (fc : SourceClaims.Function) (pos : Span)
    (fields : List (String × Ty Nat)) (after : List ScopeBinding → Compiler Target) :
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
    let some R := fields.lookup q.field
      | throw s!"pattern reads a field '{q.field}' the contract does not name"
    let G := SourceTypes.graph (← table)
    let bound := held ⟨q.name,some pos⟩
    match q.default_ with
    | none =>
      let next ← patternProps fc pos fields after (bound::scope) (R::Γ) (obj+1) more
      emitAt q.namePos (.readAt q.field (.var obj)) (.bind next) Γ R "pattern-read" (some pos.1)
        (scope := scope)
    | some d =>
      let D ← exprType fc d
      let present := BranchRefinement.tagSlice G R .isUndef false
      let T := (present ++ D).eraseDups
      let next ← patternProps fc pos fields after (bound::scope) (T::Γ) (obj+1) more
      -- A merge has no unique predecessor: each arm proves the binding's type.
      let join ← emitAt q.namePos .nul (.effect next) (T::Γ) [0] "pattern-default-join" (some pos.1)
        (scope := bound::scope)
      -- The undefined read is dropped before the default is evaluated; its
      -- value is what the arm binds.
      let fallback ← compileExpr fc scope Γ d join
      let yes : Target := ⟨fallback.label, some ((fallback.mapping.getD (List.range Γ.length)).map (·+1))⟩
      -- tagBind introduces a refined copy; discard the older read.
      let adapt := fun (t : Target) =>
        ⟨t.label, some ((t.mapping.getD (List.range (Γ.length+1))).map
          (fun j => if j == 0 then 0 else j+1))⟩
      let dispatch ← emitAt q.namePos (.var 0) (.tagBind .isUndef (adapt yes) (adapt join))
        (R::Γ) R "pattern-default-dispatch" (some pos.1) (scope := held ⟨"",some q.namePos⟩ :: scope)
      emitAt q.namePos (.readAt q.field (.var obj)) (.bind dispatch) Γ R "pattern-read" (some pos.1)
        (scope := scope)

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
    let binding : ScopeBinding := ⟨⟨b.name,some pos⟩, .cell contract reference⟩
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
      if !facts.isEmpty then
        modify fun s => { s with
          assertions := s.assertions ++ [(head.label,⟨facts,[],[]⟩)]
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
      let [.refs fields []] := PositiveRules.expand G A
        | throw "an object pattern requires a single record contract"
      -- The object is held anonymously for the whole statement, below the
      -- bindings it yields; the reads address it by its slot.
      let next ← patternProps fc pos fields (fun scope => body fuel fc R scope rest tail loopTargets)
        (held ⟨"",some init.span⟩ :: scope) (A::Γ) 0 props
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
        | .brk p | .cont p | .ret p _ | .constants p _ | .mutables p _ | .pattern p _ _ | .effect p _ | .loop p _ _ | .ite p _ _ _ => p
      let facts ← entryFacts fc pos.1 scope
      let entry ← checkpoint pos (← env fc pos.1 scope) facts target (some pos.1) scope
      modify fun s => { s with cuts := entry.label :: s.cuts }
      return entry

private def traversalBudget : List Fragment.Stmt → Nat
  | [] => 1
  | .brk .. :: rest | .cont .. :: rest | .ret .. :: rest | .constants .. :: rest | .mutables .. :: rest | .pattern .. :: rest | .effect .. :: rest => 1 + traversalBudget rest
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

/-- Search hints only: the primitives and the labels the request mentions, so
a coercion does not consider every unrelated signature in the table. The
consumer still checks against the complete graph and the exact request. -/
def SourceRequest.searchLabels (r : SourceRequest) : List Nat :=
  ([0,1,2,3] ++ r.result ++ r.inputs.flatten ++
    r.claims.flatMap (fun (c : PointClaim Nat) => c.type ++ c.context.flatten) ++
    r.obligations.flatMap (fun (o : ExpressionClaims.Required) => o.sequent.type ++ o.sequent.context.flatten)).eraseDups

/-- The table is the one the claims were lowered into; annotations the claims
did not mention grow it, and the request carries the result. -/
def extractNormalizedFn (T : SourceTypes.Table) (f : Fragment.Fn) (fc : SourceClaims.Function) :
    Except String SourceRequest := do
  if f.name != fc.name || f.namePos != fc.namePos then throw "function claim identity mismatch"
  let scope : List ScopeBinding := f.params.map (fun p => held ⟨p.name,none⟩)
  if f.name == "undefined" || (names scope).contains "undefined" then
    throw "shadowing undefined is outside the fragment"
  if !distinct (names scope) then throw "duplicate source parameter name"
  if f.params.length != fc.params.length then throw "parameter claim count mismatch"
  if !distinct (fc.envs.map Prod.fst) || !distinct (fc.exprs.map Prod.fst) then
    throw "duplicate statement or expression claim"
  let ((inputs, R, entry), built) ← (do
    let inputs ← f.params.mapM (fun (p : Fragment.Param) => lower (Fragment.translate p.ty))
    -- A parameter's annotation is the assumption its caller makes, and the
    -- soundness theorem takes it as given for every value meeting it. A
    -- primitive or an arrow can be assumed. Callable arguments may expose
    -- captured cells, so arrow contracts cover admissible future heaps and
    -- invocation effects rather than promising snapshot contents.
    -- A cell cannot: a structural object annotation does not rule out
    -- accessors, so the plain-cell interpretation may be false of a value
    -- that conforms to the annotation. Cells must be allocated here.
    let G := SourceTypes.graph (← table)
    if inputs.any (fun A => A.any fun i => match PositiveRules.expand G [i] with
        | [.refs _ _] => true | _ => false) then
      throw "cell parameters need an external-value boundary, which is outside the fragment"
    for ((p, A), (name, claimed)) in (f.params.zip inputs).zip fc.params do
      if p.name != name then throw "parameter claim name or order mismatch"
      let B ← SourceClaims.resolve (← table).length claimed
      if A != B then throw s!"claimed parameter type differs from the source annotation for '{name}'"
    let R ← lower (Fragment.translate f.ret)
    let claimedR ← SourceClaims.resolve (← table).length fc.ret
    if R != claimedR then throw "claimed return type differs from the source annotation"
    let stmts ← f.body.mapM (comparisonsStmt fc)
    let bodyScope : List ScopeBinding ← (scope.zip inputs).mapM fun (pair : ScopeBinding × Ty Nat) => do
      let (b,contract) := pair
      if stmts.any (assignsStmt b.source.name) then
        let reference ← lower (do return [← CellClaims.reference [(valueField, contract)]])
        pure { b with storage := .cell contract reference }
      else pure b
    let mut first ← body (traversalBudget stmts) fc R bodyScope stmts none none
    -- Each assigned parameter gets one fresh private cell at function entry.
    -- Replace its slot in place; the caller still supplies the original value
    -- and the function's public input contract does not mention these cells.
    for (b,i) in bodyScope.zipIdx.reverse do
      if let .cell _ reference := b.storage then
        let Γ := (bodyScope.zip inputs).zipIdx.map fun (entry : (ScopeBinding × Ty Nat) × Nat) =>
          let ((binding,A),j) := entry
          if j < i then match binding.storage with
            | .cell _ ref => ref | .value => A
          else A
        let mapping := (List.range scope.length).map fun j => if j == i then 0 else j+1
        first ← emitAt f.namePos (.makeAt .absent [valueField] [.var i])
          (.bind ⟨first.label,some mapping⟩) Γ reference "parameter-allocation"
          (scope := scope)
    let entry ← emit .nul (.effect first) inputs [0]
    return (inputs, R, entry)).run { types := T }
  return ⟨⟨built.types, built.program, built.claims, R, entry.label, inputs⟩,
    built.obligations, built.sourceMap, built.assertions, built.cuts⟩

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
end Verification.ExperimentState.SourceExtraction
