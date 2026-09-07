import Verification.ExperimentState.SourceTypes

/-! First source adapter for the stateful consumer. Names are resolved against
initialized local bindings. Supplied expression types and source annotations
become distinct obligations. The consumer reconstructs the request from source
and claims; evidence never supplies the program it is checked against.

The currently supported source slice is deliberately small: closed functions,
initialized consts, branches, variables and null/boolean literals, with every
path returning. Boolean variable tests refine the tested binding. Active-name
shadowing is not yet supported. This compiler remains a reviewed extraction boundary, not a proved
TypeScript semantics. Its output is checked by the proved calculus consumer. -/
namespace Verification.ExperimentState.SourceExtraction
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson

private def distinct [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

private def expr (scope : List String) : Expr → Except String Tm
  | .var _ name => match scope.idxOf? name with
    | some i => .ok (.var i)
    | none => .error s!"unbound or uninitialized source variable '{name}'"
  | .lit _ v => SourceTypes.value v
  | _ => .error "expression outside the current stateful source slice"

private def env (fc : FunTypeClaims) (pos : Nat) (scope : List String) :
    Except String (List (Ty Nat)) := do
  let vars ← match lookupEnv fc.envs pos with
    | some vars => pure vars
    | none => throw s!"missing statement environment at {pos}"
  if !distinct (vars.map Prod.fst) then throw s!"duplicate environment binding at {pos}"
  scope.mapM fun name => do
    match vars.lookup name with
    | some (some t) => SourceTypes.translate t
    | some none => throw s!"unsupported claimed type for '{name}' at {pos}"
    | none => throw s!"missing claimed binding '{name}' at {pos}"

private def exprType (fc : FunTypeClaims) (e : Expr) : Except String (Ty Nat) := do
  SourceTypes.translate (← claimTy fc e.span)

private structure Built where
  program : Program := []
  claims : List (PointClaim Nat) := []

private abbrev Compiler := StateT Built (Except String)

private def emit (t : Tm) (k : Continuation) (Γ : List (Ty Nat)) (A : Ty Nat) :
    Compiler Target := do
  let s ← get
  set (Built.mk (s.program ++ [⟨t,k⟩]) (s.claims ++ [⟨Γ,A⟩]))
  return ⟨s.program.length, none⟩

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
private def body : Nat → FunTypeClaims → Ty Nat → List String → List Stmt →
    Option (Target × List String) → Compiler Target
  | 0, _, _, _, _, _ => throw "internal extraction error: exhausted structural traversal"
  | fuel+1, fc, R, scope, stmts, tail => do
    match stmts with
    | [] => leave scope tail
    | .ret pos e :: rest =>
      if !rest.isEmpty then throw "statements after return are outside the current source slice"
      let Γ ← env fc pos.1 scope
      let t ← expr scope e
      let A ← exprType fc e
      let done ← emit (.var 0) .ret (A::Γ) R
      emit t (.bind done) Γ A
    | .cst pos name annot e :: rest =>
      if scope.contains name then throw s!"duplicate or shadowing local declaration '{name}'"
      let Γ ← env fc pos.1 scope
      let t ← expr scope e
      let A ← exprType fc e
      let B ← match annot with | none => pure A | some ty => SourceTypes.translate ty
      let next ← body fuel fc R (name::scope) rest tail
      let annotation ← emit (.var 0) (.effect next) (A::Γ) B
      emit t (.bind annotation) Γ A
    | .ite pos cond thn els :: rest =>
      let Γ ← env fc pos.1 scope
      let t ← expr scope cond
      let A ← exprType fc cond
      let continuation ← if rest.isEmpty then pure tail else do
        let next ← body fuel fc R scope rest tail
        pure (some (next,scope))
      let yes ← body fuel fc R scope thn continuation
      let no ← body fuel fc R scope (els.getD []) continuation
      let tested := match t with | .var i => some i | _ => none
      emit t (.branchBind (branchMapping scope.length tested yes)
        (branchMapping scope.length tested no)) Γ A

private def traversalBudget : List Stmt → Nat
  | [] => 1
  | .ret .. :: rest | .cst .. :: rest => 1 + traversalBudget rest
  | .ite _ _ thn none :: rest => 2 + traversalBudget thn + traversalBudget rest
  | .ite _ _ thn (some els) :: rest =>
      1 + traversalBudget thn + traversalBudget els + traversalBudget rest
termination_by stmts => sizeOf stmts


def extractFn (f : Verification.Fn) (fc : FunTypeClaims) : Except String Request := do
  if f.name != fc.name || f.namePos != fc.namePos then throw "function claim identity mismatch"
  if !f.params.isEmpty || !fc.params.isEmpty then throw "the current source slice requires closed functions"
  if !distinct (fc.envs.map Prod.fst) || !distinct (fc.exprs.map Prod.fst) then
    throw "duplicate statement or expression claim"
  let R ← SourceTypes.translate f.ret
  let claimedR ← match fc.ret with
    | some t => SourceTypes.translate t
    | none => throw "unsupported claimed return type"
  if R != claimedR then throw "claimed return type differs from the source annotation"
  let (entry, built) ← (body (traversalBudget f.body) fc R [] f.body none).run {}
  return ⟨1, SourceTypes.types, built.program, built.claims, R, entry.label⟩

def extract (ast claims : Json) (fileKey : String) : Except String (List Request) := do
  if (← jStr (← jField ast "file")) != fileKey then throw "AST file key mismatch"
  let files ← claims.getArr?
  let selected ← files.toList.filterM fun f => do return (← jStr (← jField f "file")) == fileKey
  if selected.length != 1 then throw "expected exactly one matching claim file"
  let fs ← decodeAst ast
  let cs ← decodeTypeClaims claims fileKey
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
  b.version == 1 && rs.length == b.functions.length &&
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
  let evidence := toJson (Bundle.mk 1 cs)
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
    (h : checkRequests rs b = true) {r c} (hm : (r,c) ∈ rs.zip b.functions) (n : Nat) :
    SafeGraph r.program (meaning (RequestJson.graph r) r.result) n (ofList []) []
      (.at r.start (fun _ => .nul)) := by
  simp only [checkRequests, Bool.and_eq_true, List.all_eq_true] at h
  exact verify_safe (h.2 _ hm) n

#print axioms checkJson_checked
#print axioms checkRequests_safe
end Verification.ExperimentState.SourceExtraction
