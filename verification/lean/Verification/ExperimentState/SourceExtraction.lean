import Verification.ExperimentState.SourceInput

/-! First source adapter for the stateful consumer. Names are resolved against
initialized local bindings. Supplied expression types and source annotations
become distinct obligations. The consumer reconstructs the request from source
and claims; evidence never supplies the program it is checked against.

The currently supported source slice is deliberately small: primitive parameters,
initialized consts, branches, variables, null/boolean literals and local plain
cells (allocation, reads and assignments), bounded reader closures and calls,
with every
path returning. Boolean variable tests refine the tested binding. Active-name
shadowing is not yet supported. This compiler remains a reviewed extraction boundary, not a proved
TypeScript semantics. Its output is checked by the proved calculus consumer. -/
namespace Verification.ExperimentState.SourceExtraction
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open SourceInput

private def distinct [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

private def env (fc : Claims) (pos : Nat) (scope : List String) :
    Except String (List (Ty Nat)) := do
  let vars ← match fc.envs.lookup pos with
    | some vars => pure vars
    | none => throw s!"missing statement environment at {pos}"
  if !distinct (vars.map Prod.fst) then throw s!"duplicate environment binding at {pos}"
  scope.mapM fun name => do
    match vars.lookup name with
    | some t => SourceInput.translate t
    | none => throw s!"missing claimed binding '{name}' at {pos}"

private def exprType (fc : Claims) (e : SourceInput.Expr) : Except String (Ty Nat) := do
  match fc.exprs.lookup e.span with
  | some t => SourceInput.translate t
  | none => throw s!"no claimed type for the expression at {spanStr e.span}"

private structure Built where
  program : Program := []
  claims : List (PointClaim Nat) := []

private abbrev Compiler := StateT Built (Except String)

private def emit (t : Tm) (k : Continuation) (Γ : List (Ty Nat)) (A : Ty Nat) :
    Compiler Target := do
  let s ← get
  set (Built.mk (s.program ++ [⟨t,k⟩]) (s.claims ++ [⟨Γ,A⟩]))
  return ⟨s.program.length, none⟩

/-- The first closure slice has no internal statement environments. Its body
claim is the declared result, so the existing lambda premise checks that exact
claim. A read receiver must retain the exact captured-slot contract. -/
private def closureBody (fc : Claims) (scope : List String) (Γ : List (Ty Nat))
    (e : SourceInput.Expr) (R : Ty Nat) : Except String Tm := do
  if (← exprType fc e) != R then
    throw "closure body claim must match its declared result in this slice"
  let resolve := fun name => do
    match scope.idxOf? name with
    | some i => pure i
    | none => throw s!"unbound or uninitialized closure variable '{name}'"
  match e with
  | .var _ name => return .var (← resolve name)
  | .lit _ v => SourceTypes.value v
  | .read _ receiver =>
    match receiver with
    | .var _ name =>
      let i ← resolve name
      let C ← exprType fc receiver
      if Γ[i]? != some C then throw "closure receiver claim differs from its captured binding"
      return .read (.var i)
    | _ => throw "closure read must use a captured variable"
  | _ => throw "closure body outside the value/read source slice"

/-- Each expression leaves its result in slot zero and preserves the original
slots after it. Anonymous temporary slots cannot be named by source identifiers.
Mappings discard only the temporaries introduced by this expression. -/
private def compileExpr (fc : Claims) (scope : List String) (Γ : List (Ty Nat))
    (e : SourceInput.Expr) (next : Target) : Compiler Target := do
  let A ← exprType fc e
  match e with
  | .var _ name =>
    let i ← match scope.idxOf? name with
      | some i => pure i
      | none => throw s!"unbound or uninitialized source variable '{name}'"
    emit (.var i) (.bind next) Γ A
  | .lit _ v => emit (← SourceTypes.value v) (.bind next) Γ A
  | .alloc _ a | .read _ a =>
    let B ← exprType fc a
    let op := match e with | .alloc .. => Tm.alloc | _ => Tm.read
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+1))⟩
    let node ← emit (op (.var 0)) (.bind drop) (B::Γ) A
    compileExpr fc scope Γ a node
  | .lam _ name arg ret body =>
    if scope.contains name then throw "shadowing closure parameter is outside the source slice"
    let D ← SourceTypes.translate (← decodeTy arg)
    if D != [0] then throw "source closures currently require a null argument"
    let R ← SourceTypes.translate (← decodeTy ret)
    if A != [FunctionClaims.label R] then throw "closure signature claim differs from source annotations"
    let t ← closureBody fc (name::scope) (D::Γ) body R
    emit (.lam t) (.bind next) Γ A
  | .app _ callee arg =>
    let B ← exprType fc callee
    let C ← exprType fc arg
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    let call ← emit (.app (.var 1) (.var 0)) (.bind drop) (C::B::Γ) A
    let right ← compileExpr fc (""::scope) (B::Γ) arg call
    compileExpr fc scope Γ callee right
  | .write _ receiver rhs =>
    let B ← exprType fc receiver
    let C ← exprType fc rhs
    let drop := ⟨next.label, some ((next.mapping.getD (List.range (Γ.length+1))).map
      (fun i => if i == 0 then 0 else i+2))⟩
    -- JS assignment returns its evaluated RHS; the calculus write returns null.
    let result ← emit (.var 0) (.bind drop) (C::B::Γ) A
    let write ← emit (.write (.var 1) (.var 0)) (.effect result) (C::B::Γ) [0]
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

/-- Compile the continuation once, then point both arms at it. Allocation order
is intentionally independent of source order; `start` records the real entry.
Fuel bounds structural traversal, not execution or certificate search. -/
private def body : Nat → Claims → Ty Nat → List String → List SourceInput.Stmt →
    Option (Target × List String) → Compiler Target
  | 0, _, _, _, _, _ => throw "internal extraction error: exhausted structural traversal"
  | fuel+1, fc, R, scope, stmts, tail => do
    match stmts with
    | [] => leave scope tail
    | .ret pos e :: rest =>
      if !rest.isEmpty then throw "statements after return are outside the current source slice"
      let Γ ← env fc pos.1 scope
      let A ← exprType fc e
      let done ← emit (.var 0) .ret (A::Γ) R
      compileExpr fc scope Γ e done
    | .cst pos name annot e :: rest =>
      if scope.contains name then throw s!"duplicate or shadowing local declaration '{name}'"
      let Γ ← env fc pos.1 scope
      let A ← exprType fc e
      let B ← match annot with | none => pure A | some ty => SourceInput.translate ty
      let next ← body fuel fc R (name::scope) rest tail
      let annotation ← emit (.var 0) (.effect next) (A::Γ) B
      compileExpr fc scope Γ e annotation
    | .ite pos cond thn els :: rest =>
      let Γ ← env fc pos.1 scope
      let A ← exprType fc cond
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail
        pure (some (next,scope))
      let yes ← body fuel fc R scope thn continuation
      let no ← body fuel fc R scope (els.getD []) continuation
      let tested := match cond with | .var _ name => scope.idxOf? name | _ => none
      -- Branch on the saved value; the edge maps discard its older copy and
      -- retain the new refinement slot supplied by branchBind.
      let adapt := fun t =>
        let mapped := branchMapping scope.length tested t
        ⟨mapped.label, some ((mapped.mapping.getD []).map
          (fun i => if i == 0 then 0 else i+1))⟩
      let node ← emit (.var 0) (.branchBind (adapt yes) (adapt no)) (A::Γ) A
      compileExpr fc scope Γ cond node
    | .effect pos e :: rest =>
      let Γ ← env fc pos.1 scope
      let next ← body fuel fc R scope rest tail
      let drop := ⟨next.label, some ((next.mapping.getD (List.range Γ.length)).map (·+1))⟩
      compileExpr fc scope Γ e drop

private def traversalBudget : List SourceInput.Stmt → Nat
  | [] => 1
  | .ret .. :: rest | .cst .. :: rest | .effect .. :: rest => 1 + traversalBudget rest
  | .ite _ _ thn none :: rest => 2 + traversalBudget thn + traversalBudget rest
  | .ite _ _ thn (some els) :: rest =>
      1 + traversalBudget thn + traversalBudget els + traversalBudget rest
termination_by stmts => sizeOf stmts


def extractFn (f : SourceInput.Fn) (fc : Claims) : Except String Request := do
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
    let B ← SourceInput.translate claimed
    if A != B then throw s!"claimed parameter type differs from the source annotation for '{name}'"
  if !distinct (fc.envs.map Prod.fst) || !distinct (fc.exprs.map Prod.fst) then
    throw "duplicate statement or expression claim"
  let R ← SourceInput.translate f.ret
  let claimedR ← SourceInput.translate fc.ret
  if R != claimedR then throw "claimed return type differs from the source annotation"
  let (entry, built) ← (do
    let first ← body (traversalBudget f.body) fc R scope f.body none
    emit .nul (.effect first) inputs [0]).run {}
  return ⟨2, SourceTypes.types, built.program, built.claims, R, entry.label, inputs⟩

def extract (ast claims : Json) (fileKey : String) : Except String (List Request) := do
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
  deriving ToJson, FromJson

def checkRequests (rs : List Request) (b : Bundle) : Bool :=
  b.version == 2 && rs.length == b.functions.length &&
    (rs.zip b.functions).all (fun (r,c) => verify r c)

def checkJson (ast claims : Json) (fileKey : String) (evidence : Json) : Except String Unit := do
  let rs ← extract ast claims fileKey
  let b : Bundle ← decodeStrict evidence
  if checkRequests rs b then return ()
  throw "source evidence does not justify the extracted program and exact claims"

def produceJson (ast claims : Json) (fileKey : String) (fuel : Nat) : Except String Json := do
  let rs ← extract ast claims fileKey
  let cs ← rs.mapM fun r => do
    let j ← RequestJson.produceJson (toJson r) fuel
    decodeResponse r j
  let evidence := toJson (Bundle.mk 2 cs)
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
theorem checkRequests_safe {rs : List Request} {b : Bundle}
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions) (n W heap ρ)
    (he : EnvOk (RequestJson.graph r) r.inputs ρ n W) (hw : WorldAdm W) (hh : HeapOk n W heap) :
    SafeGraph r.program (meaning (RequestJson.graph r) r.result) n W heap (.at r.start ρ) := by
  simp only [checkRequests, Bool.and_eq_true, List.all_eq_true] at h
  exact verify_safe (h.2 _ hm) n W heap ρ he hw hh

#print axioms checkJson_checked
#print axioms checkRequests_safe
end Verification.ExperimentState.SourceExtraction
