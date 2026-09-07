import Verification.ExperimentState.SourceTypes

/-! First source adapter for the stateful consumer. Names are resolved against
initialized local bindings. Supplied expression types and source annotations
become distinct obligations. The consumer reconstructs the request from source
and claims; evidence never supplies the program it is checked against.

The currently supported source slice is deliberately small: closed functions,
straight-line initialized consts, a final return, variables and null/boolean
literals. This compiler remains a reviewed extraction boundary, not a proved
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

/-- Two nodes per statement keep claimed types separate from annotations.
The annotation node checks the saved value without changing its runtime binding. -/
private def body (fc : FunTypeClaims) (R : Ty Nat) (scope : List String) (label : Nat) :
    List Stmt → Except String (Program × List (PointClaim Nat))
  | [] => .error "the current source slice requires a final return"
  | .ret pos e :: rest => do
    if !rest.isEmpty then throw "statements after return are outside the current source slice"
    let Γ ← env fc pos.1 scope
    let t ← expr scope e
    let A ← exprType fc e
    return ([⟨t, .bind ⟨label+1, none⟩⟩, ⟨.var 0, .ret⟩],
      [⟨Γ,A⟩, ⟨A::Γ,R⟩])
  | .cst pos name annot e :: rest => do
    if scope.contains name then throw s!"duplicate local declaration '{name}'"
    let Γ ← env fc pos.1 scope
    let t ← expr scope e
    let A ← exprType fc e
    let B ← match annot with | none => pure A | some ty => SourceTypes.translate ty
    let (P, claims) ← body fc R (name::scope) (label+2) rest
    return (⟨t, .bind ⟨label+1, none⟩⟩ :: ⟨.var 0, .effect ⟨label+2, none⟩⟩ :: P,
      ⟨Γ,A⟩ :: ⟨A::Γ,B⟩ :: claims)
  | .ite .. :: _ => .error "branches are outside the current stateful source slice"

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
  let (P, claims) ← body fc R [] 0 f.body
  return ⟨1, SourceTypes.types, P, claims, R, 0⟩

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
