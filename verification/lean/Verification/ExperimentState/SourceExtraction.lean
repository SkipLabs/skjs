import Verification.ExperimentState.SkjsSourceClaims
import Verification.ExperimentState.ExpressionClaims

/-! First source adapter for the stateful consumer. Names are resolved against
initialized local bindings. Supplied expression types and source annotations
become distinct obligations. The consumer reconstructs the request from source
and claims; evidence never supplies the program it is checked against.

The currently supported source slice is deliberately small: primitive parameters,
initialized consts, branches, variables, null/boolean literals and local plain
cells (allocation, reads and assignments), expression-bodied closures and calls,
with every path returning. Boolean variable tests refine the tested binding.
Active-name shadowing is not yet supported. This compiler remains a reviewed
extraction boundary, not a proved TypeScript semantics. Its output is checked by the proved calculus consumer. -/
namespace Verification.ExperimentState.SourceExtraction
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open SourceInput

private def distinct [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

private def envCore (fc : SourceClaims.Function) (pos : Nat) (scope : List String) :
    Except String (List (Ty Nat)) := do
  let vars ← match fc.envs.lookup pos with
    | some vars => pure vars
    | none => throw s!"missing statement environment at {pos}"
  if !distinct (vars.map Prod.fst) then throw s!"duplicate environment binding at {pos}"
  scope.mapM fun name => do
    match vars.lookup name with
    | some t => SourceClaims.resolve t
    | none => throw s!"missing claimed binding '{name}' at {pos}"

private def env (fc : SourceClaims.Function) (pos : Nat) (scope : List String) :
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
  | .ifBody _ result _ _ _ => do SourceTypes.translate (← decodeTy result)
  | e => exprType fc e

private structure Built where
  program : Program := []
  claims : List (PointClaim Nat) := []
  obligations : List ExpressionClaims.Required := []
  origins : List (Option Span) := []

private abbrev Compiler := StateT Built (Except String)

private def emit (t : Tm) (k : Continuation) (Γ : List (Ty Nat)) (A : Ty Nat) :
    Compiler Target := do
  let s : Built ← get
  set (Built.mk (s.program ++ [⟨t,k⟩]) (s.claims ++ [⟨Γ,A⟩]) s.obligations (s.origins ++ [none]))
  return ⟨s.program.length, none⟩

/-- Diagnostic metadata only; never part of the certified request. -/
private def emitAt (pos : Span) (t : Tm) (k : Continuation) (Γ : List (Ty Nat)) (A : Ty Nat) :
    Compiler Target := do
  let target ← emit t k Γ A
  modify fun s => { s with origins := s.origins.set target.label (some pos) }
  return target

/-- Statement claims name source bindings only. Preserve anonymous evaluation
slots at their already checked types while projecting the supplied named slots. -/
private def closureEnv (fc : SourceClaims.Function) (pos : Nat) (scope : List String)
    (Γ : List (Ty Nat)) : Except String (List (Ty Nat)) := do
  let names := scope.filter (· != "")
  let H ← env fc pos names
  (scope.zipIdx).mapM fun (name,i) => do
    let A := if name == "" then Γ[i]? else H[names.idxOf name]?
    match A with
    | some A => pure A
    | none => throw "internal closure slot mismatch"

/-- Lower expressions inside lambda bodies without losing their individual
claims. Requirements use the lexical context at the occurrence; synthetic let
slots are introduced only after the operand supplying their type is checked. -/
private def closureExpr (fc : SourceClaims.Function) (scope : List String) (Γ : List (Ty Nat))
    (e : SourceInput.Expr) : Compiler DirectProof.Plan := do
  let A ← closureType fc e
  let p ← match e with
  | .var _ name =>
    match scope.idxOf? name with
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
    let a ← closureExpr fc (""::scope) (B::Γ) rhs
    let C := a.type
    let H := C::B::Γ
    let write := DirectProof.node H (.write (.var 1) (.var 0)) [0] .write
      [DirectProof.var H 1 B,DirectProof.cast H D (DirectProof.var H 0 C)]
    let done := DirectProof.letE H write (DirectProof.var ([0]::H) 1 C)
    pure (DirectProof.letE Γ r (DirectProof.letE (B::Γ) a done))
  | .done _ => pure (DirectProof.node Γ .nul [0] .nul)
  | .seqBody _ init body => do
    let a ← closureExpr fc scope Γ init
    let b ← closureExpr fc (""::scope) (a.type::Γ) body
    pure (DirectProof.letE Γ a b)
  | .letBody pos name annot init body => do
    if name != "" && scope.contains name then
      throw "duplicate or shadowing closure local"
    let H ← closureEnv fc pos.1 scope Γ
    for (B,i) in H.zipIdx do
      modify fun s => { s with obligations := s.obligations ++ [⟨pos,⟨Γ,.var i,B⟩,some (DirectProof.var Γ i B)⟩] }
    let I ← exprType fc init
    let B ← match annot with
      | some ty => SourceInput.translate ty
      | none => pure I
    let a ← closureExpr fc scope H init
    let annotation := DirectProof.cast H B a
    modify fun s => { s with obligations := s.obligations ++ [⟨init.span,annotation.goal,some annotation⟩] }
    let b ← closureExpr fc (name::scope) (I::H) body
    pure (DirectProof.letE H a b)
  | .ifBody pos _ cond thn els => do
    let H ← closureEnv fc pos.1 scope Γ
    for (B,i) in H.zipIdx do
      modify fun s => { s with obligations := s.obligations ++ [⟨pos,⟨Γ,.var i,B⟩,some (DirectProof.var Γ i B)⟩] }
    let c ← closureExpr fc scope H cond
    match cond with
    | .var _ name =>
      let some i := scope.idxOf? name | throw "unbound closure condition"
      let T := H.set i [1]
      let F := H.set i [2]
      let t ← closureExpr fc scope T thn
      let e ← closureExpr fc scope F els
      pure (DirectProof.node H (.ite c.term t.term e.term) A (.ifBoolVar [1] [2])
        [DirectProof.cast T A t,DirectProof.cast F A e])
    | _ =>
      let t ← closureExpr fc scope H thn
      let e ← closureExpr fc scope H els
      pure (DirectProof.node H (.ite c.term t.term e.term) A .ifBool
        [c,DirectProof.cast H A t,DirectProof.cast H A e])
  | .atEnv pos body => do
    let H ← closureEnv fc pos.1 scope Γ
    for (B,i) in H.zipIdx do
      modify fun s => { s with obligations := s.obligations ++ [⟨pos,⟨Γ,.var i,B⟩,some (DirectProof.var Γ i B)⟩] }
    closureExpr fc scope H body
  | .lam pos name arg ret body => do
    if scope.contains name then throw "shadowing closure parameter is outside the source slice"
    let D ← SourceTypes.translate (← decodeTy arg)
    if D != [0] then throw "source closures currently require a null argument"
    let R ← SourceTypes.translate (← decodeTy ret)
    if A != [FunctionClaims.label R] then throw "closure signature claim differs from source annotations"
    let b ← closureExpr fc (name::scope) (D::Γ) body
    let annotation := DirectProof.cast (D::Γ) R b
    modify fun s => { s with obligations := s.obligations ++ [⟨pos,annotation.goal,some annotation⟩] }
    pure (DirectProof.node Γ (.lam b.term) A .lam [annotation])
  let plan := DirectProof.cast Γ A p
  modify fun s => { s with obligations := s.obligations ++ [⟨e.span,plan.goal,some plan⟩] }
  return plan
termination_by e

/-- Each expression leaves its result in slot zero and preserves the original
slots after it. Anonymous temporary slots cannot be named by source identifiers.
Mappings discard only the temporaries introduced by this expression. -/
private def compileExpr (fc : SourceClaims.Function) (scope : List String) (Γ : List (Ty Nat))
    (e : SourceInput.Expr) (next : Target) : Compiler Target := do
  let A ← exprType fc e
  match e with
  | .var _ name =>
    let i ← match scope.idxOf? name with
      | some i => pure i
      | none => throw s!"unbound or uninitialized source variable '{name}'"
    emitAt e.span (.var i) (.bind next) Γ A
  | .lit _ v => emitAt e.span (← SourceTypes.value v) (.bind next) Γ A
  | .alloc _ a | .read _ a =>
    let B ← exprType fc a
    let op := match e with | .alloc .. => Tm.alloc | _ => Tm.read
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let node ← emitAt e.span (op (.var 0)) (.bind drop) (B::Γ) A
    compileExpr fc scope Γ a node
  | .atEnv .. | .letBody .. | .ifBody .. | .done .. | .seqBody .. => throw "statement environment wrapper is only supported inside a closure"
  | .lam .. =>
    let t ← closureExpr fc scope Γ e
    emitAt e.span t.term (.bind next) Γ A
  | .app _ callee arg =>
    let B ← exprType fc callee
    let C ← exprType fc arg
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let call ← emitAt e.span (.app (.var 1) (.var 0)) (.bind drop) (C::B::Γ) A
    let right ← compileExpr fc (""::scope) (B::Γ) arg call
    compileExpr fc scope Γ callee right
  | .write _ receiver rhs =>
    let B ← exprType fc receiver
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    -- JS assignment returns its evaluated RHS; the calculus write returns null.
    let result ← emitAt e.span (.var 0) (.bind drop) (C::B::Γ) A
    let write ← emitAt e.span (.write (.var 1) (.var 0)) (.effect result) (C::B::Γ) [0]
    let right ← compileExpr fc (""::scope) (B::Γ) rhs write
    compileExpr fc scope Γ receiver right
termination_by e

/-- Leaving a block drops its local slots simultaneously. Active-name shadowing
is gated until the export can identify hidden bindings independently. -/
private def leave (scope : List String) (tail : Option (Target × List String)) :
    Except String Target := do
  let (target, outer) ← match tail with
    | some t => pure t
    | none => throw "the current source slice requires a return on every path"
  let slots ← outer.mapM fun name => match scope.idxOf? name with
    | some i => pure i
    | none => throw s!"internal extraction error: lost outer binding '{name}'"
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
private def testedSlot (scope : List String) (Γ : List (Ty Nat)) (cond : SourceInput.Expr) : Option Nat :=
  match cond with
  | .var _ name => do
    let i ← scope.idxOf? name
    if Γ[i]? == some [1] || Γ[i]? == some [2] then none else some i
  | _ => none

/-- The nearest enclosing loop, with the lexical scope at each destination. -/
private structure LoopTargets where
  again : Target × List String
  done : Option (Target × List String)

/-- Compile the continuation once, then point both arms at it. Allocation order
is intentionally independent of source order; `start` records the real entry.
Fuel bounds structural traversal, not execution or certificate search. -/
private def body : Nat → SourceClaims.Function → Ty Nat → List String → List SourceInput.Stmt →
    Option (Target × List String) → Option LoopTargets → Compiler Target
  | 0, _, _, _, _, _, _ => throw "internal extraction error: exhausted structural traversal"
  | fuel+1, fc, R, scope, stmts, tail, loopTargets => do
    match stmts with
    | [] => leave scope tail
    | .brk pos :: rest | .cont pos :: rest =>
      if !rest.isEmpty then throw "statements after break or continue are outside the current source slice"
      let some targets := loopTargets | throw "break or continue outside a source loop"
      let Γ ← env fc pos.1 scope
      let destination := match stmts with
        | .brk _ :: _ => targets.done
        | _ => some targets.again
      let next ← leave scope destination
      emit .nul (.effect next) Γ [0]
    | .ret pos e :: rest =>
      if !rest.isEmpty then throw "statements after return are outside the current source slice"
      let Γ ← env fc pos.1 scope
      let A ← exprType fc e
      let done ← emitAt e.span (.var 0) .ret (A::Γ) R
      compileExpr fc scope Γ e done
    | .cst pos name annot e :: rest =>
      if scope.contains name then throw s!"duplicate or shadowing local declaration '{name}'"
      let Γ ← env fc pos.1 scope
      let A ← exprType fc e
      let B ← match annot with | none => pure A | some ty => SourceInput.translate ty
      let next ← body fuel fc R (name::scope) rest tail loopTargets
      let annotation ← emitAt e.span (.var 0) (.effect next) (A::Γ) B
      compileExpr fc scope Γ e annotation
    | .ite pos cond thn els :: rest =>
      let Γ ← env fc pos.1 scope
      let A ← exprType fc cond
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail loopTargets
        pure (some (next,scope))
      let yes ← body fuel fc R scope thn continuation loopTargets
      let no ← body fuel fc R scope (els.getD []) continuation loopTargets
      let tested := testedSlot scope Γ cond
      -- Branch on the saved value; the edge maps discard its older copy and
      -- retain the new refinement slot supplied by branchBind.
      let adapt := fun t =>
        let mapped := branchMapping scope.length tested t
        ⟨mapped.label, some ((mapped.mapping.getD []).map
          (fun i => if i == 0 then 0 else i+1))⟩
      let node ← emitAt cond.span (.var 0) (.branchBind (adapt yes) (adapt no)) (A::Γ) A
      compileExpr fc scope Γ cond node
    | .loop pos cond loopBody :: rest =>
      let Γ ← env fc pos.1 scope
      let A ← exprType fc cond
      -- Reserve a stable label for incoming and back edges. Replace its stub
      -- before returning; the completed program is independently checked.
      let head ← emitAt cond.span .nul .ret Γ [0]
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail loopTargets
        pure (some (next,scope))
      let yes ← body fuel fc R scope loopBody (some (head,scope)) (some ⟨(head,scope),continuation⟩)
      let no ← leave scope continuation
      let tested := testedSlot scope Γ cond
      let adapt := fun t =>
        let mapped := branchMapping scope.length tested t
        ⟨mapped.label, some ((mapped.mapping.getD []).map
          (fun i => if i == 0 then 0 else i+1))⟩
      let branch ← emitAt cond.span (.var 0) (.branchBind (adapt yes) (adapt no)) (A::Γ) A
      let condition ← compileExpr fc scope Γ cond branch
      modify fun s => { s with program := s.program.set head.label ⟨.nul,.effect condition⟩ }
      return head
    | .effect pos e :: rest =>
      let Γ ← env fc pos.1 scope
      let next ← body fuel fc R scope rest tail loopTargets
      let drop := ⟨next.label, some ((next.mapping.getD (List.range Γ.length)).map (·+1))⟩
      compileExpr fc scope Γ e drop

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
  origins : List (Option Span) := []

def extractNormalizedFn (f : SourceInput.Fn) (fc : SourceClaims.Function) : Except String SourceRequest := do
  if f.name != fc.name || f.namePos != fc.namePos then throw "function claim identity mismatch"
  let scope := f.params.map (·.name)
  if !distinct scope then throw "duplicate source parameter name"
  if f.params.length != fc.params.length then throw "parameter claim count mismatch"
  let inputs ← f.params.mapM (fun p => SourceInput.translate p.ty)
  -- Cell origins must be plain allocations in this source slice. Structural
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
  return ⟨⟨2, SourceTypes.types, built.program, built.claims, R, entry.label, inputs⟩, built.obligations, built.origins⟩

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

def checkRequests (rs : List SourceRequest) (b : Bundle) : Bool :=
  b.version == 3 && rs.length == b.functions.length && rs.length == b.obligations.length &&
    (rs.zip b.functions).all (fun (r,c) => verify r.toRequest c) &&
    (rs.zip b.obligations).all (fun (r,es) =>
      ExpressionClaims.checkAll (RequestJson.graph r.toRequest) r.types.length r.obligations es)

def checkJson (ast claims : Json) (fileKey : String) (evidence : Json) : Except String Unit := do
  let rs ← extract ast claims fileKey
  let b : Bundle ← decodeStrict evidence
  if checkRequests rs b then return ()
  throw "source evidence does not justify the extracted program and exact claims"

def produceJson (ast claims : Json) (fileKey : String) (fuel : Nat) : Except String Json := do
  let rs ← extract ast claims fileKey
  let es ← rs.mapM fun r => ExpressionClaims.produce (RequestJson.graph r.toRequest)
    (List.range r.types.length) r.types.length fuel r.obligations
  let cs ← (rs.zip es).mapM fun (r,proofs) => do
    let j ← RequestJson.produceJson (toJson r.toRequest) fuel [] proofs r.origins
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
  exact verify_safe (h.1.2 _ hm) n W heap ρ he hw hh

/-- Every supplemental claim is a derivable sequent in the same calculus. -/
theorem checkRequests_obligations {rs : List SourceRequest} {b : Bundle}
    (h : checkRequests rs b = true) {r es} (hm : (r,es) ∈ rs.zip b.obligations)
    {q e} (hq : (q,e) ∈ r.obligations.zip es) :
    HasTy (RequestJson.graph r.toRequest) q.sequent.context q.sequent.term q.sequent.type := by
  simp only [checkRequests, Bool.and_eq_true, List.all_eq_true] at h
  exact ExpressionClaims.checkAll_sound (h.2 _ hm) hq

#print axioms checkRequests_obligations
#print axioms checkJson_checked
#print axioms checkRequests_safe
end Verification.ExperimentState.SourceExtraction
