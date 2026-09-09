import Verification.ExperimentState.SkjsSourceClaims
import Verification.ExperimentState.ExpressionClaims

/-! First source adapter for the stateful consumer. Names are resolved against
initialized local bindings. Supplied expression types and source annotations
become distinct obligations. The consumer reconstructs the request from source
and claims; evidence never supplies the program it is checked against.

The currently supported source slice is deliberately small: primitive parameters,
initialized consts, branches, variables, null/boolean literals and local plain
cells (allocation, reads and assignments), expression-bodied closures and calls,
with every path returning. Boolean variable tests, including negations, refine the tested binding.
Active-name shadowing is not yet supported. This compiler remains a reviewed
extraction boundary, not a proved TypeScript semantics. Its output is checked by the proved calculus consumer. -/
namespace Verification.ExperimentState.SourceExtraction
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open SourceInput

private def distinct [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

/-- Name lookup is unchanged: descriptors carry the same names in the same
order, and an unnamed one can never match a source identifier. -/
private def names (scope : List Descriptor) : List String := scope.map (·.name)

private def envCore (fc : SourceClaims.Function) (pos : Nat) (scope : List Descriptor) :
    Except String (List (Ty Nat)) := do
  let vars ← match fc.envs.lookup pos with
    | some vars => pure vars
    | none => throw s!"missing statement environment at {pos}"
  if !distinct (vars.map Prod.fst) then throw s!"duplicate environment binding at {pos}"
  scope.mapM fun d => do
    let name := d.name
    match vars.lookup name with
    | some t => (SourceClaims.resolve t).mapError fun msg =>
        if msg == "type claim unavailable from producer" then
          s!"unavailable claimed binding '{name}' at {pos}"
        else msg
    | none => throw s!"missing claimed binding '{name}' at {pos}"

private def env (fc : SourceClaims.Function) (pos : Nat) (scope : List Descriptor) :
    Except String (List (Ty Nat)) :=
  (envCore fc pos scope).mapError fun msg => s!"source environment obligation at {pos}: {msg}"

private def exprType (fc : SourceClaims.Function) (e : SourceInput.Expr) : Except String (Ty Nat) := do
  match fc.exprs.lookup e.span with
  | some t => (SourceClaims.resolve t).mapError fun msg =>
      s!"source expression obligation at [{e.span.1},{e.span.2}): {msg}"
  | none => throw s!"no claimed type for the expression at {spanStr e.span}"

/-- A terminal branch uses the enclosing source result annotation, not a
fabricated expression claim at the if statement's span. -/
private def closureType (fc : SourceClaims.Function) : SourceInput.Expr → Except String (Ty Nat)
  | .atEnv _ b | .letBody _ _ _ _ b | .seqBody _ _ b => closureType fc b
  | .done _ => pure [0]
  | .ifBody _ (some result) _ _ _ => do SourceTypes.translate (← decodeTy result)
  | e => exprType fc e

private structure Built where
  program : Program := []
  claims : List (PointClaim Nat) := []
  obligations : List ExpressionClaims.Required := []
  sourceMap : SourceMap := []
  assertions : List (Nat × HeapKnowledge.Knowledge) := []
  /-- Full statement-entry interfaces; absent assertions mean empty knowledge. -/
  cuts : List Nat := []

private abbrev Compiler := StateT Built (Except String)

private def emit (t : Tm) (k : Continuation) (Γ : List (Ty Nat)) (A : Ty Nat) :
    Compiler Target := do
  let s : Built ← get
  set (Built.mk (s.program ++ [⟨t,k⟩]) (s.claims ++ [⟨Γ,A⟩]) s.obligations (s.sourceMap ++ [none]) s.assertions s.cuts)
  return ⟨s.program.length, none⟩

/-- Record this node's source map entry. Explanatory only; never part of the
certified request. The context must be describable binding for binding: a
context this cannot name is an extraction bug, not a slot number for a reader,
so it fails here rather than reaching a message. -/
private def emitAt (pos : Span) (t : Tm) (k : Continuation) (Γ : List (Ty Nat)) (A : Ty Nat)
    (role : String := "node-typing") (environmentStart : Option Nat := none)
    (scope : List Descriptor := []) : Compiler Target := do
  let target ← emit t k Γ A
  if scope.length != Γ.length then
    throw s!"internal extraction error: source map covers {scope.length} of {Γ.length} bindings at {pos.1}"
  if let some d := scope.find? (!·.describes) then
    throw s!"internal extraction error: undescribed binding '{d.name}' at {pos.1}"
  modify fun s =>
    { s with sourceMap := s.sourceMap.set target.label (some ⟨pos,role,environmentStart,scope⟩) }
  return target

/-- A checkpoint is an actual no-op graph node. Every incoming edge must
justify its supplied current-heap assertion, including backedges. -/
private def checkpoint (pos : Span) (Γ : List (Ty Nat)) (facts : HeapFacts.Facts)
    (next : Target) (entry : Option Nat := none) (scope : List Descriptor := []) :
    Compiler Target := do
  if facts.isEmpty then return next
  let t ← emitAt pos .nul (.effect next) Γ [0] "heap-observation" entry scope
  modify fun s => { s with assertions := s.assertions ++ [(t.label,⟨facts,[],[]⟩)] }
  return t

private def contents (A : Ty Nat) : Except String (List HeapFacts.Literal) := do
  if !RequestJson.validTy SourceTypes.types.length A then throw "invalid current-content type label"
  let some R := HeapKnowledge.literals SourceTypes.graph A
    | throw "current-content predicate must be a finite primitive type"
  return R

private def entryFacts (fc : SourceClaims.Function) (pos : Nat) (scope : List Descriptor) :
    Except String HeapFacts.Facts := do
  let cs := (fc.entryCurrent.lookup pos).getD []
  scope.zipIdx.foldlM (fun facts (d,i) => do
    let name := d.name
    match cs.lookup name with
    | none => return facts
    | some A => return facts ++ [⟨i,← contents A⟩]) []

/-- Record a source obligation with its source map, under the same invariant as
`emitAt`: every context binding must be describable in the words of the source. -/
private def obligation (pos : Span) (j : ProgramCertificates.Sequent Nat) (plan : Option DirectProof.Plan)
    (role : String) (scope : List Descriptor) : Compiler Unit := do
  if scope.length != j.context.length then
    throw s!"internal extraction error: source map covers {scope.length} of {j.context.length} bindings at {pos.1}"
  if scope.any (!·.describes) then
    throw s!"internal extraction error: undescribed binding at {pos.1}"
  modify fun s => { s with obligations := s.obligations ++ [⟨pos,j,plan,role,scope⟩] }

/-- Ordinary lambda proofs cannot retain transient heap observations across
calls. Require their declared storage contract to imply such an observation
uniformly; this is a located proof obligation, never a discarded assertion. -/
private def persistentObservation (d : Descriptor) (pos : Span) (A R : Ty Nat) : Compiler Unit := do
  let _ ← contents R
  let [.refs W []] := PositiveRules.expand SourceTypes.graph A
    | throw "current-content assertion requires a single cell contract"
  let plan := DirectProof.var [W] 0 R
  obligation pos plan.goal (some plan) "heap-observation" [d]

/-- Statement claims name source bindings only. Preserve anonymous evaluation
slots at their already checked types while projecting the supplied named slots. -/
private def closureEnv (fc : SourceClaims.Function) (pos : Nat) (scope : List Descriptor)
    (Γ : List (Ty Nat)) : Compiler (List (Ty Nat)) := do
  let named := (names scope).filter (· != "")
  let H ← env fc pos (named.map (fun n => ⟨n,none⟩))
  for (name,A) in named.zip H do
    if let some R := ((fc.entryCurrent.lookup pos).getD []).lookup name then
      persistentObservation ⟨name,none⟩ (pos,pos+1) A R
  (scope.zipIdx).mapM fun (d,i) => do
    let name := d.name
    let A := if name == "" then Γ[i]? else H[named.idxOf name]?
    match A with
    | some A => pure A
    | none => throw "internal closure slot mismatch"

/-- Negations of an immutable variable retain its identity and reverse the
branch polarity. Arbitrary expressions deliberately carry no alias refinement. -/
private def conditionVariable (scope : List Descriptor) : SourceInput.Expr → Option (Nat × Bool)
  | .var _ name => ((names scope).idxOf? name).map (·, false)
  | .not _ e => (conditionVariable scope e).map fun (i, reversed) => (i, !reversed)
  | _ => none

/-- Only a syntactic immutable variable retains an alias to the observed value.
Reads and calls deliberately do not qualify, even if their types look stable. -/
private def nullConditionVariable (scope : List Descriptor) : SourceInput.Expr → Option (Nat × Bool)
  | .not _ e => (nullConditionVariable scope e).map fun (i, equal) => (i, !equal)
  | .nullTest _ equal testLeft left right =>
    match (if testLeft then left else right) with
    | .var _ name => ((names scope).idxOf? name).map (·, equal)
    | _ => none
  | _ => none

private def nullTestTerm (equal : Bool) (slot : Nat) : Tm :=
  .ite (.test .isNul (.var slot)) (if equal then .tru else .fls) (if equal then .fls else .tru)

/-- The fixed source graph has a uniform head shape at each label. Splitting
its explicit union lets the ordinary tag rule prove each alternative. -/
private def nullTestPlan (Γ : List (Ty Nat)) (slot : Nat) (equal : Bool) (A : Ty Nat) :
    Except String DirectProof.Plan := do
  let some C := Γ[slot]? | throw "internal null-test slot mismatch"
  let term := nullTestTerm equal slot
  let children ← C.mapM fun a => do
    let H := Γ.set slot [a]
    let q := decide (Answers SourceTypes.graph [a] .isNul true)
    let value := if q == equal then Tm.tru else .fls
    let B := if q == equal then [1] else [2]
    let rule := if q == equal then ProgramCertificates.Rule.truLit else .flsLit
    pure (DirectProof.node H term A (if q then .ifTrue else .ifFalse)
      [DirectProof.cast H A (DirectProof.node H value B rule)])
  pure (DirectProof.node Γ term A (.unionVar slot) children)

/-- Shared conditional proof construction for statement branches, ternaries and
short-circuit operators. Branch builders retain their own source claims; a
logical operator's constant arm is administrative and needs no invented claim. -/
private def conditionalPlan (scope : List Descriptor) (H : List (Ty Nat)) (A : Ty Nat)
    (cond : SourceInput.Expr) (c : DirectProof.Plan)
    (yesBranch noBranch : List Descriptor → List (Ty Nat) → Compiler DirectProof.Plan) :
    Compiler DirectProof.Plan := do
  if let some (i, equal) := nullConditionVariable scope cond then
    let some C := H[i]? | throw "internal closure null-guard slot mismatch"
    -- Preserve the evaluated predicate and its claims in an anonymous slot.
    let K := c.type :: H
    let tested := i+1
    let T := K.set tested (BranchRefinement.tagSlice SourceTypes.graph C .isNul true)
    let F := K.set tested (BranchRefinement.tagSlice SourceTypes.graph C .isNul false)
    let t ← yesBranch (⟨"",some cond.span⟩::scope) (if equal then T else F)
    let e ← noBranch (⟨"",some cond.span⟩::scope) (if equal then F else T)
    let yes := if equal then t else e
    let no := if equal then e else t
    let term := Tm.ite (.test .isNul (.var tested)) yes.term no.term
    let children := C.map fun label =>
      let L := K.set tested [label]
      let q := decide (Answers SourceTypes.graph [label] .isNul true)
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
      pure (DirectProof.ifE SourceTypes.graph H A c t e)

/-- Build compositional proofs for lambda bodies and source ternaries without
losing their individual claims. Requirements use the lexical context at the occurrence; synthetic let
slots are introduced only after the operand supplying their type is checked. -/
private def closureExpr (fc : SourceClaims.Function) (scope : List Descriptor) (Γ : List (Ty Nat))
    (e : SourceInput.Expr) : Compiler DirectProof.Plan := do
  let A ← closureType fc e
  if let some R := fc.exprCurrent.lookup e.span then
    persistentObservation ⟨"",some e.span⟩ e.span A R
  let p ← match e with
  | .var _ name =>
    match (names scope).idxOf? name with
    | some i => pure (DirectProof.var Γ i A)
    | none => throw s!"unbound or uninitialized closure variable '{name}'"
  | .lit _ v => do
    let t ← SourceTypes.value v
    let (B,r) ← match t with
      | .nul => pure ([0],ProgramCertificates.Rule.nul)
      | .tru => pure ([1],ProgramCertificates.Rule.truLit)
      | .fls => pure ([2],ProgramCertificates.Rule.flsLit)
      | _ => throw "unsupported closure literal"
    pure (DirectProof.node Γ t B r)
  | .nullTest _ equal testLeft left right => do
    let leftSpan := left.span
    let left ← closureExpr fc scope Γ left
    let right ← closureExpr fc (⟨"",some leftSpan⟩::scope) (left.type::Γ) right
    let H := right.type::left.type::Γ
    let result ← nullTestPlan H (if testLeft then 1 else 0) equal A
    pure (DirectProof.letE Γ left (DirectProof.letE (left.type::Γ) right result))
  | .logical _ andOp left right => do
    let l ← closureExpr fc scope Γ left
    let constant := fun (_ : List Descriptor) H => pure
      (if andOp then DirectProof.node H .fls [2] .flsLit
       else DirectProof.node H .tru [1] .truLit)
    let rhs := fun ds types => closureExpr fc ds types right
    conditionalPlan scope Γ A left l
      (if andOp then rhs else constant) (if andOp then constant else rhs)
  | .coalesce _ left right => do
    let l ← closureExpr fc scope Γ left
    let K := l.type :: Γ
    let H := (BranchRefinement.tagSlice SourceTypes.graph l.type .isNul true) :: Γ
    -- A named immutable left operand is identical to the saved value. Move its
    -- name to that slot for the fallback; no mutable read is given an alias.
    let rightScope := match left with
      | .var _ name => ⟨name,some left.span⟩ ::
          scope.map (fun d => if d.name == name then ⟨"",some left.span⟩ else d)
      | _ => ⟨"",some left.span⟩ :: scope
    let r ← closureExpr fc rightScope H right
    let term := Tm.ite (.test .isNul (.var 0)) r.term (.var 0)
    let children := l.type.map fun label =>
      let L := [label] :: Γ
      let q := decide (Answers SourceTypes.graph [label] .isNul true)
      let selected := if q then DirectProof.cast L A r else DirectProof.var L 0 A
      DirectProof.node L term A (if q then .ifTrue else .ifFalse) [selected]
    pure (DirectProof.letE Γ l (DirectProof.node K term A (.unionVar 0) children))
  | .not _ a => do
    let a ← closureExpr fc scope Γ a
    pure (DirectProof.ifE SourceTypes.graph Γ A a
      (DirectProof.node Γ .fls [2] .flsLit) (DirectProof.node Γ .tru [1] .truLit))
  | .alloc _ a => do
    let [.refs B []] := PositiveRules.expand SourceTypes.graph A
      | throw "allocation claim must name a cell contract"
    let a ← closureExpr fc scope Γ a
    pure (DirectProof.node Γ (.alloc a.term) A .alloc [DirectProof.cast Γ B a])
  | .read _ a => do
    let a ← closureExpr fc scope Γ a
    let [.refs B []] := PositiveRules.expand SourceTypes.graph a.type
      | throw "read receiver must name a cell contract"
    pure (DirectProof.node Γ (.read a.term) B .read [a])
  | .app _ f a => do
    let f ← closureExpr fc scope Γ f
    let a ← closureExpr fc scope Γ a
    let [.arrs [(D,R)]] := PositiveRules.expand SourceTypes.graph f.type
      | throw "callee must name a unary source arrow"
    pure (DirectProof.node Γ (.app f.term a.term) R .app [f,DirectProof.cast Γ D a])
  | .write _ receiver rhs => do
    let B ← exprType fc receiver
    let [.refs D []] := PositiveRules.expand SourceTypes.graph B
      | throw "write receiver must name a cell contract"
    let r ← closureExpr fc scope Γ receiver
    let a ← closureExpr fc (⟨"",some receiver.span⟩::scope) (B::Γ) rhs
    let C := a.type
    let H := C::B::Γ
    let write := DirectProof.node H (.write (.var 1) (.var 0)) [0] .write
      [DirectProof.var H 1 B,DirectProof.cast H D (DirectProof.var H 0 C)]
    let done := DirectProof.letE H write (DirectProof.var ([0]::H) 1 C)
    pure (DirectProof.letE Γ r (DirectProof.letE (B::Γ) a done))
  | .done _ => pure (DirectProof.node Γ .nul [0] .nul)
  | .seqBody _ init body => do
    let a ← closureExpr fc scope Γ init
    let b ← closureExpr fc (⟨"",some init.span⟩::scope) (a.type::Γ) body
    pure (DirectProof.letE Γ a b)
  | .letBody pos name annot init body => do
    if name != "" && (names scope).contains name then
      throw "duplicate or shadowing closure local"
    let H ← closureEnv fc pos.1 scope Γ
    for (B,i) in H.zipIdx do
      obligation pos ⟨Γ,.var i,B⟩ (some (DirectProof.var Γ i B)) "closure-entry" scope
    let I ← exprType fc init
    let B ← match annot with
      | some ty => SourceInput.translate ty
      | none => pure I
    let a ← closureExpr fc scope H init
    let annotation := DirectProof.cast H B a
    obligation init.span annotation.goal (some annotation) "binding-annotation" scope
    let b ← closureExpr fc (⟨name,some init.span⟩::scope) (I::H) body
    pure (DirectProof.letE H a b)
  | .ifBody pos result cond thn els => do
    let H ← if result.isSome then closureEnv fc pos.1 scope Γ else pure Γ
    if result.isSome then
      for (B,i) in H.zipIdx do
        obligation pos ⟨Γ,.var i,B⟩ (some (DirectProof.var Γ i B)) "closure-entry" scope
    let c ← closureExpr fc scope H cond
    conditionalPlan scope H A cond c
      (fun names types => closureExpr fc names types thn)
      (fun names types => closureExpr fc names types els)
  | .atEnv pos body => do
    let H ← closureEnv fc pos.1 scope Γ
    for (B,i) in H.zipIdx do
      obligation pos ⟨Γ,.var i,B⟩ (some (DirectProof.var Γ i B)) "closure-entry" scope
    closureExpr fc scope H body
  | .lam pos name arg ret body => do
    if (names scope).contains name then throw "shadowing closure parameter is outside the source slice"
    let D ← SourceTypes.translate (← decodeTy arg)
    let R ← SourceTypes.translate (← decodeTy ret)
    if A != [FunctionClaims.label D R] then throw "closure signature claim differs from source annotations"
    let b ← closureExpr fc (⟨name,some pos⟩::scope) (D::Γ) body
    let annotation := DirectProof.cast (D::Γ) R b
    obligation pos annotation.goal (some annotation) "closure-result" (⟨name,some pos⟩::scope)
    pure (DirectProof.node Γ (.lam b.term) A .lam [annotation])
  let plan := DirectProof.cast Γ A p
  obligation e.span plan.goal (some plan) "expression-claim" scope
  return plan
termination_by e

/-- Each expression leaves its result in slot zero and preserves the original
slots after it. Anonymous temporary slots cannot be named by source identifiers.
Mappings discard only the temporaries introduced by this expression. -/
private def compileExpr (fc : SourceClaims.Function) (scope : List Descriptor) (Γ : List (Ty Nat))
    (e : SourceInput.Expr) (next : Target) : Compiler Target := do
  let A ← exprType fc e
  let next ← match fc.exprCurrent.lookup e.span with
    | none => pure next
    | some R => checkpoint e.span (A::Γ) [⟨0,← contents R⟩] next (scope := ⟨"",some e.span⟩::scope)
  match e with
  | .var _ name =>
    let i ← match (names scope).idxOf? name with
      | some i => pure i
      | none => throw s!"unbound or uninitialized source variable '{name}'"
    emitAt e.span (.var i) (.bind next) Γ A (scope := scope)
  | .lit _ v => emitAt e.span (← SourceTypes.value v) (.bind next) Γ A (scope := scope)
  | .alloc _ a | .read _ a | .not _ a =>
    let B ← exprType fc a
    let op := match e with
      | .alloc .. => Tm.alloc
      | .not .. => fun t => Tm.ite t .fls .tru
      | _ => Tm.read
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let node ← emitAt e.span (op (.var 0)) (.bind drop) (B::Γ) A
      (scope := ⟨"",some a.span⟩::scope)
    compileExpr fc scope Γ a node
  | .atEnv .. | .letBody .. | .ifBody _ (some _) .. | .done .. | .seqBody .. => throw "statement environment wrapper is only supported inside a closure"
  | .lam .. | .ifBody _ none .. | .coalesce .. | .logical .. =>
    let t ← closureExpr fc scope Γ e
    emitAt e.span t.term (.bind next) Γ A (scope := scope)
  | .nullTest _ equal testLeft left right =>
    let B ← exprType fc left
    let C ← exprType fc right
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let test ← emitAt e.span (nullTestTerm equal (if testLeft then 1 else 0)) (.bind drop) (C::B::Γ) A
      (scope := ⟨"",some right.span⟩::⟨"",some left.span⟩::scope)
    let right ← compileExpr fc (⟨"",some left.span⟩::scope) (B::Γ) right test
    compileExpr fc scope Γ left right
  | .app _ callee arg =>
    let B ← exprType fc callee
    let C ← exprType fc arg
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let call ← emitAt e.span (.app (.var 1) (.var 0)) (.bind drop) (C::B::Γ) A
      (scope := ⟨"",some arg.span⟩::⟨"",some callee.span⟩::scope)
    let right ← compileExpr fc (⟨"",some callee.span⟩::scope) (B::Γ) arg call
    compileExpr fc scope Γ callee right
  | .write _ receiver rhs =>
    let B ← exprType fc receiver
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    -- JS assignment returns its evaluated RHS; the calculus write returns null.
    let effects := ⟨"",some rhs.span⟩::⟨"",some receiver.span⟩::scope
    let result ← emitAt e.span (.var 0) (.bind drop) (C::B::Γ) A (scope := effects)
    let write ← emitAt e.span (.write (.var 1) (.var 0)) (.effect result) (C::B::Γ) [0]
      (scope := effects)
    let right ← compileExpr fc (⟨"",some receiver.span⟩::scope) (B::Γ) rhs write
    compileExpr fc scope Γ receiver right
termination_by e

/-- Leaving a block drops its local slots simultaneously. Active-name shadowing
is gated until the export can identify hidden bindings independently. -/
private def leave (scope : List Descriptor) (tail : Option (Target × List Descriptor)) :
    Except String Target := do
  let (target, outer) ← match tail with
    | some t => pure t
    | none => throw "the current source slice requires a return on every path"
  let slots ← outer.mapM fun d => match (names scope).idxOf? d.name with
    | some i => pure i
    | none => throw s!"internal extraction error: lost outer binding '{d.name}'"
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
private def testedSlot (scope : List Descriptor) (Γ : List (Ty Nat)) (cond : SourceInput.Expr) : Option Nat :=
  do
    let (i, _) ← conditionVariable scope cond
    if Γ[i]? == some [1] || Γ[i]? == some [2] then none else some i

/-- Share polarity handling between conditionals and loop heads. The saved
condition is in slot zero. Only a syntactically identified immutable variable
may be replaced by the recovered Boolean witness. -/
private def emitBranch (scope : List Descriptor) (Γ : List (Ty Nat)) (cond : SourceInput.Expr)
    (A : Ty Nat) (yes no : Target) : Compiler Target := do
  if let some (i, equal) := nullConditionVariable scope cond then
    let some C := Γ[i]? | throw "internal null-guard slot mismatch"
    let adapt := fun t =>
      let mapped := branchMapping scope.length (some i) t
      ⟨mapped.label, some ((mapped.mapping.getD []).map
        (fun j => if j == 0 then 0 else j+1))⟩
    -- The source predicate has already run and all operand claims were checked.
    -- Reading the same immutable variable observes its tag without repeating
    -- any source expression or trusting the saved Boolean's annotation.
    return ← emitAt cond.span (.var (i+1))
      (.tagBind .isNul (adapt (if equal then yes else no)) (adapt (if equal then no else yes)))
      (A::Γ) C "tag-dispatch" (scope := ⟨"",some cond.span⟩::scope)
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
    (scope := ⟨"",some cond.span⟩::scope)

/-- Facts justified on the path to a short-circuit operand. Only immutable
source bindings are refined; every generated edge checks this candidate context.
A true conjunction / false disjunction establishes both operand outcomes. The
other outcomes deliberately retain the input context rather than compute a join. -/
private def conditionContext (scope : List Descriptor) (Γ : List (Ty Nat))
    (cond : SourceInput.Expr) (answer : Bool) : List (Ty Nat) :=
  match cond with
  | .not _ e => conditionContext scope Γ e (!answer)
  | .logical _ andOp left right =>
    if answer == andOp then
      conditionContext scope (conditionContext scope Γ left answer) right answer
    else Γ
  | _ =>
    if let some (i, equal) := nullConditionVariable scope cond then
      Γ.set i (BranchRefinement.tagSlice SourceTypes.graph (Γ[i]?.getD []) .isNul (answer == equal))
    else if let some i := testedSlot scope Γ cond then
      Γ.set i (if answer then [1] else [2])
    else Γ

/-- Compile compound conditions as short-circuit edges. The full source
expression still has an independent claimed typing obligation; the runtime
traverses its operands once instead of evaluating it and then replaying it. -/
private def compileCondition (fc : SourceClaims.Function) (scope : List Descriptor)
    (Γ : List (Ty Nat)) (cond : SourceInput.Expr) (yes no : Target) : Compiler Target := do
  let simple := do
    let A ← exprType fc cond
    let node ← emitBranch scope Γ cond A yes no
    compileExpr fc scope Γ cond node
  match cond with
  | .logical _ andOp left right =>
    let _ ← closureExpr fc scope Γ cond
    let H := conditionContext scope Γ left andOp
    let rhs ← compileCondition fc scope H right yes no
    compileCondition fc scope Γ left (if andOp then rhs else yes) (if andOp then no else rhs)
  | .not _ e =>
    let _ ← closureExpr fc scope Γ cond
    compileCondition fc scope Γ e no yes
  | _ => simple
termination_by cond

/-- The nearest enclosing loop, with the lexical scope at each destination. -/
private structure LoopTargets where
  again : Target × List Descriptor
  done : Option (Target × List Descriptor)

/-- Compile the continuation once, then point both arms at it. Allocation order
is intentionally independent of source order; `start` records the real entry.
Fuel bounds structural traversal, not execution or certificate search. -/
private def body : Nat → SourceClaims.Function → Ty Nat → List Descriptor → List SourceInput.Stmt →
    Option (Target × List Descriptor) → Option LoopTargets → Compiler Target
  | 0, _, _, _, _, _, _ => throw "internal extraction error: exhausted structural traversal"
  | fuel+1, fc, R, scope, stmts, tail, loopTargets => do
    let target ← match stmts with
    | [] => leave scope tail
    | .brk pos :: rest | .cont pos :: rest =>
      if !rest.isEmpty then throw "statements after break or continue are outside the current source slice"
      let some targets := loopTargets | throw "break or continue outside a source loop"
      let Γ ← env fc pos.1 scope
      let destination := match stmts with
        | .brk _ :: _ => targets.done
        | _ => some targets.again
      let next ← leave scope destination
      emitAt pos .nul (.effect next) Γ [0] (scope := scope)
    | .ret pos e :: rest =>
      if !rest.isEmpty then throw "statements after return are outside the current source slice"
      let Γ ← env fc pos.1 scope
      let A ← exprType fc e
      let done ← emitAt e.span (.var 0) .ret (A::Γ) R "return-contract" (some pos.1)
        (scope := ⟨"",some e.span⟩::scope)
      compileExpr fc scope Γ e done
    | .cst pos name annot e :: rest =>
      if (names scope).contains name then throw s!"duplicate or shadowing local declaration '{name}'"
      let Γ ← env fc pos.1 scope
      let A ← exprType fc e
      let B ← match annot with | none => pure A | some ty => SourceInput.translate ty
      let next ← body fuel fc R (⟨name,some pos⟩::scope) rest tail loopTargets
      let annotation ← emitAt e.span (.var 0) (.effect next) (A::Γ) B "binding-annotation" (some pos.1)
        (scope := ⟨name,some e.span⟩::scope)
      compileExpr fc scope Γ e annotation
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
      let no ← leave scope continuation
      let condition ← compileCondition fc scope Γ cond yes no
      modify fun s => { s with program := s.program.set head.label ⟨.nul,.effect condition⟩ }
      let facts ← entryFacts fc pos.1 scope
      if !facts.isEmpty then
        modify fun s => { s with
          assertions := s.assertions ++ [(head.label,⟨facts,[],[]⟩)]
          sourceMap := s.sourceMap.set head.label (some ⟨pos,"heap-observation",some pos.1,scope⟩) }
      modify fun s => { s with cuts := head.label :: s.cuts }
      pure head
    | .effect pos e :: rest =>
      let Γ ← env fc pos.1 scope
      let next ← body fuel fc R scope rest tail loopTargets
      let drop := ⟨next.label, some ((next.mapping.getD (List.range Γ.length)).map (·+1))⟩
      compileExpr fc scope Γ e drop
    match stmts with
    | [] | .loop .. :: _ => return target
    | st :: _ =>
      let pos := match st with
        | .brk p | .cont p | .ret p _ | .cst p _ _ _ | .effect p _ | .loop p _ _ | .ite p _ _ _ => p
      let facts ← entryFacts fc pos.1 scope
      let entry ← checkpoint pos (← env fc pos.1 scope) facts target (some pos.1) scope
      modify fun s => { s with cuts := entry.label :: s.cuts }
      return entry

private def traversalBudget : List SourceInput.Stmt → Nat
  | [] => 1
  | .brk .. :: rest | .cont .. :: rest | .ret .. :: rest | .cst .. :: rest | .effect .. :: rest => 1 + traversalBudget rest
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

/-- Search hints only. The fixed source graph's arrow/reference operands contain
primitive labels; avoid considering all unrelated signatures at every coercion.
The consumer still checks against the complete graph and the exact request. -/
def SourceRequest.searchLabels (r : SourceRequest) : List Nat :=
  ([0,1,2] ++ r.result ++ r.inputs.flatten ++
    r.claims.flatMap (fun (c : PointClaim Nat) => c.type ++ c.context.flatten) ++
    r.obligations.flatMap (fun (o : ExpressionClaims.Required) => o.sequent.type ++ o.sequent.context.flatten)).eraseDups

def extractNormalizedFn (f : SourceInput.Fn) (fc : SourceClaims.Function) : Except String SourceRequest := do
  if f.name != fc.name || f.namePos != fc.namePos then throw "function claim identity mismatch"
  let scope : List Descriptor := f.params.map (fun p => ⟨p.name,none⟩)
  if !distinct (names scope) then throw "duplicate source parameter name"
  if f.params.length != fc.params.length then throw "parameter claim count mismatch"
  let inputs ← f.params.mapM (fun p => SourceInput.translate p.ty)
  -- Cell sourceMap must be plain allocations in this source slice. Structural
  -- parameter annotations alone cannot rule out JavaScript accessors.
  if inputs.any (fun A => A.any (· ≥ 3)) then
    throw "cell or function parameters require an external-value boundary not yet supported"
  for (p, (name, claimed)) in f.params.zip fc.params do
    if p.name != name then throw "parameter claim name or order mismatch"
    let A ← SourceInput.translate p.ty
    let B ← SourceClaims.resolve claimed
    if A != B then throw s!"claimed parameter type differs from the source annotation for '{name}'"
  if !distinct (fc.envs.map Prod.fst) || !distinct (fc.exprs.map Prod.fst) then
    throw "duplicate statement or expression claim"
  let R ← SourceInput.translate f.ret
  let claimedR ← SourceClaims.resolve fc.ret
  if R != claimedR then throw "claimed return type differs from the source annotation"
  let (entry, built) ← (do
    let first ← body (traversalBudget f.body) fc R scope f.body none none
    emit .nul (.effect first) inputs [0]).run {}
  return ⟨⟨2, SourceTypes.types, built.program, built.claims, R, entry.label, inputs⟩, built.obligations, built.sourceMap, built.assertions, built.cuts⟩

/-- Existing wire callers pass through the SKJS adapter. Other producers can
supply normalized candidates directly to extractNormalizedFn. -/
def extractFn (f : SourceInput.Fn) (fc : SourceInput.Claims) : Except String SourceRequest :=
  extractNormalizedFn f (SkjsSourceClaims.translate fc)

def extract (ast claims : Json) (fileKey : String) : Except String (List SourceRequest) := do
  if (← jStr (← jField ast "file")) != fileKey then throw "AST file key mismatch"
  let files ← claims.getArr?
  let selected ← files.toList.filterM fun f => do return (← jStr (← jField f "file")) == fileKey
  if selected.length != 1 then throw "expected exactly one matching claim file"
  let fs ← SourceInput.decodeAst ast
  let cs ← SourceInput.decodeTypeClaims claims fileKey
  if fs.isEmpty then throw "no source functions to verify"
  if !distinct (fs.map (fun f => (f.name, f.namePos))) then throw "duplicate source function identities"
  if !distinct (cs.map (fun f => (f.name, f.namePos))) then throw "duplicate function claims"
  if fs.length != cs.length then throw "function claim count mismatch"
  fs.mapM fun f => do
    let fc ← match cs.find? (fun c => c.name == f.name && c.namePos == f.namePos) with
      | some c => pure c
      | none => throw s!"missing claims for '{f.name}'"
    extractFn f fc

/-- Evidence order is source declaration order, independent of export order. -/
structure Bundle where
  version : Nat
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
  b.version == 3 && rs.length == b.functions.length && rs.length == b.obligations.length &&
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

def checkJson (ast claims : Json) (fileKey : String) (evidence : Json) : Except String Unit := do
  let rs ← extract ast claims fileKey
  let b : Bundle ← decodeStrict evidence
  if checkRequests rs b then return ()
  throw "source evidence does not justify the extracted program and exact claims"

def produceJson (ast claims : Json) (fileKey : String) (fuel : Nat) : Except String Json := do
  let rs ← extract ast claims fileKey
  let es ← rs.mapM fun r => ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length fuel r.obligations
  let cs ← (rs.zip es).mapM fun (r,proofs) => do
    let j ← RequestJson.produceJson (toJson r.toRequest) fuel [] proofs r.sourceMap (some r.searchLabels) r.assertions r.cuts
    decodeResponse r.toRequest j
  let evidence := toJson (Bundle.mk 3 cs es)
  checkJson ast claims fileKey evidence
  return evidence

/-- Tie source-mode acceptance to the actual decoded inputs and extracted requests. -/
theorem checkJson_checked {ast claims evidence : Json} {fileKey : String}
    (h : checkJson ast claims fileKey evidence = .ok ()) :
    ∃ rs b, extract ast claims fileKey = .ok rs ∧
      decodeStrict evidence = .ok b ∧ checkRequests rs b = true := by
  unfold checkJson at h
  cases he : extract ast claims fileKey with
  | error e => simp only [he] at h; contradiction
  | ok rs =>
    cases hb : (decodeStrict evidence : Except String Bundle) with
    | error e => simp only [he, hb] at h; contradiction
    | ok b =>
      simp only [he, hb] at h
      change (if checkRequests rs b = true then Except.ok () else
        Except.error "source evidence does not justify the extracted program and exact claims") = .ok () at h
      split at h
      · exact ⟨rs,b,rfl,rfl,by assumption⟩
      · contradiction

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
#print axioms checkJson_checked
#print axioms checkRequests_safe
end Verification.ExperimentState.SourceExtraction
