import Verification.ExperimentState.Fragment
import Verification.ExperimentState.CellClaims
import Verification.ExperimentState.GenericBounds

/-! Source extraction of first-order generic function bodies.

Variable-copy bodies are checked under distinct rigid parameters and forward
upper bounds by the existing variable, let and subtype rules. Bodies may copy `T` through `const y: T = x` and
extra parameters (`fst`), along `letE_safeP` and `var_safeP`.
`T extends boolean` is an assumption `T ≤ boolean`:
`asBoolean<T extends boolean>(x: T): boolean { return x }` transports along
that inclusion. It does not justify `true ≤ T`. Other generic shapes remain
outside the fragment. Producer claims enter through the shared source interface. -/
namespace Verification.ExperimentState.GenericSource
open Lean Claim

def paramName (j : Json) : Except String String := do
  CellClaims.fieldsExactly j ["top", "atoms"]
  if ← (← jField j "top").getBool? then throw "expected a type parameter, not unknown"
  let [atom] ← jArr j "atoms" | throw "expected a single type-parameter atom"
  CellClaims.fieldsExactly atom ["a", "name"]
  if (← jStr (← jField atom "a")) != "param" then throw "expected a type-parameter atom"
  let name ← jStr (← jField atom "name")
  if name.isEmpty then throw "empty type-parameter name"
  return name

def booleanType : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "boolean")]])]

def isBooleanType (j : Json) : Bool := j == booleanType

/-- Label zero is boolean; distinct declared parameters get distinct positive labels. -/
def typeIndex (params : List String) (j : Json) : Except String Nat := do
  if isBooleanType j then return 0
  let name ← paramName j
  let some index := params.idxOf? name | throw s!"undeclared type parameter '{name}'"
  return index + 1

def boundEdges (params : List Fragment.TypeParam) : Except String (List (Nat × Nat)) := do
  let mut seen : List String := []
  let mut edges := []
  for tp in params do
    if tp.name == "undefined" then throw "shadowing undefined is outside the source slice"
    if tp.name ∈ seen then throw "duplicate type parameter"
    if let some bound := tp.bound then
      let upper ← match typeIndex seen bound with
        | .ok i => pure i
        | .error _ => throw "only `extends boolean` or an earlier type parameter is in the fragment"
      edges := edges ++ [(seen.length + 1, upper)]
    seen := seen ++ [tp.name]
  return edges

def variableType (env : List (String × Nat)) : Fragment.Expr → Except String Nat
  | .var _ name =>
    match env.find? (fun p => p.1 == name) with
    | some p => return p.2
    | none => throw s!"generic body refers to unbound variable '{name}'"
  | _ => throw "generic body requires a variable copy"

/-- The executable relation has a `SubP` soundness proof in `GenericBounds`.
Bounds originate only at positive parameter labels. -/
def subtype (edges : List (Nat × Nat)) (a b : Nat) : Bool :=
  GenericBounds.follows edges (edges.length + 1) a b

partial def copyBody (params : List String) (edges : List (Nat × Nat))
    (env : List (String × Nat)) (result : Nat) : List Fragment.Stmt → Except String Unit
  | [] => throw "generic identity requires an explicit return"
  | [.ret _ e] => do
    let actual ← match e with
      | .lit _ (.vbool true) =>
        if !edges.isEmpty then throw "an upper bound does not justify true ≤ T"
        else throw "generic identity requires returning a variable"
      | _ => variableType env e
    unless subtype edges actual result do
      throw "generic return is not justified by the declared upper bounds (returning T as boolean requires T extends boolean)"
  | .cst _ name annot init :: rest => do
    if name == "undefined" then throw "shadowing undefined is outside the source slice"
    if env.any (fun p => p.1 == name) then throw "active-name shadowing is outside the source slice"
    let some annot := annot | throw "generic const requires a type annotation"
    let expected ← typeIndex params annot
    let actual ← variableType env init
    unless subtype edges actual expected do
      throw "generic const is not justified by the declared upper bounds"
    copyBody params edges (env ++ [(name, expected)]) result rest
  | _ => throw "generic identity requires const copies followed by a return"

/-- Check generic variable-copy bodies using distinct rigid parameters and
forward upper bounds, including dependent chains. Producer signatures must
match source annotations exactly; bounds never identify their endpoints. -/
def checkScheme (f : Fragment.Fn) (typeParams : List Fragment.TypeParam)
    (fc : Fragment.Claims) : Except String Unit := do
  if f.name != fc.name || f.namePos != fc.namePos then
    throw "function claim identity mismatch"
  if typeParams.isEmpty then throw "generic body requires type parameters"
  let edges ← boundEdges typeParams
  let params := typeParams.map (·.name)
  if f.params.isEmpty then throw "generic body requires a value parameter"
  let names := f.params.map (·.name)
  if names.eraseDups.length != names.length then throw "duplicate source parameter"
  let env ← f.params.mapM fun p => do
    if p.name == "undefined" then throw "shadowing undefined is outside the source slice"
    return (p.name, ← typeIndex params p.ty)
  let result ← typeIndex params f.ret
  copyBody params edges env result f.body
  if f.params.length != fc.params.length then throw "parameter claim count mismatch"
  for (p, c) in f.params.zip fc.params do
    if p.name != c.1 then throw "parameter claim name or order mismatch"
    if (← typeIndex params p.ty) != (← typeIndex params c.2) then
      throw "claimed generic identity types differ from the source annotation"
  if (← typeIndex params fc.ret) != result then
    throw "claimed generic identity types differ from the source annotation"

private def typeName (params : List String) (i : Nat) : String :=
  if i == 0 then "boolean" else (params[i-1]?).getD "?"

private def requireSubtype (params : List String) (edges : List (Nat × Nat))
    (env : List (String × Nat)) (pos : Span) (role subject : String)
    (actual expected : Nat) : Except String Unit := do
  unless subtype edges actual expected do
    let context := String.intercalate "; " (env.map fun (name,t) => s!"{name}: {typeName params t}")
    let bounds := String.intercalate ", " (edges.map fun (a,b) =>
      s!"{typeName params a} ≤ {typeName params b}")
    throw s!"generic {role} at [{pos.1},{pos.2}): {bounds}; {context} ⊢ {subject} : {typeName params expected}; cannot establish {typeName params actual} ≤ {typeName params expected}"

private def claimedType (params : List String) (pos : Span) (role : String)
    (ty : Json) : Except String Nat :=
  match typeIndex params ty with
  | .ok t => pure t
  | .error reason => throw s!"generic {role} at [{pos.1},{pos.2}): {reason}"

private def entryClaims (params : List String) (edges : List (Nat × Nat))
    (fc : Fragment.Claims) (env : List (String × Nat)) (pos : Span) :
    Except String (List (String × Nat)) := do
  let some raw := fc.envs.lookup pos.1
    | throw s!"generic entry claim at [{pos.1},{pos.2}): missing statement environment"
  let names := raw.map Prod.fst
  if names.eraseDups.length != names.length then
    throw s!"generic entry claim at [{pos.1},{pos.2}): duplicate binding"
  let source := raw
  if source.length != env.length || source.any (fun p => !(env.map Prod.fst).contains p.1) then
    throw s!"generic entry claim at [{pos.1},{pos.2}): bindings differ from the source scope"
  env.mapM fun (name,actual) => do
    let some ty := source.lookup name | throw s!"missing generic binding '{name}'"
    let expected ← claimedType params pos "entry claim" ty
    requireSubtype params edges env pos "entry claim" name actual expected
    return (name,expected)

private def expressionClaim (params : List String) (edges : List (Nat × Nat))
    (fc : Fragment.Claims) (env : List (String × Nat)) (e : Fragment.Expr) :
    Except String Nat := do
  let some ty := fc.exprs.lookup e.span
    | throw s!"generic expression claim at [{e.span.1},{e.span.2}): missing expression claim"
  let expected ← claimedType params e.span "expression claim" ty
  let actual ← variableType env e
  let subject := match e with | .var _ name => name | _ => "expression"
  requireSubtype params edges env e.span "expression claim" subject actual expected
  return expected

private def claimSites : List Fragment.Stmt → List Nat × List Span
  | [] => ([],[])
  | .ret pos e :: rest =>
    let (entries,expressions) := claimSites rest
    (pos.1 :: entries,e.span :: expressions)
  | .cst pos _ _ e :: rest =>
    let (entries,expressions) := claimSites rest
    (pos.1 :: entries,e.span :: expressions)
  | _ :: rest => claimSites rest

private def bodyClaims (params : List String) (edges : List (Nat × Nat))
    (fc : Fragment.Claims) (env : List (String × Nat)) (result : Nat) :
    List Fragment.Stmt → Except String Unit
  | [.ret pos e] => do
    let H ← entryClaims params edges fc env pos
    let actual ← expressionClaim params edges fc H e
    requireSubtype params edges H pos "return contract" "returned expression" actual result
  | .cst pos name (some annot) init :: rest => do
    let H ← entryClaims params edges fc env pos
    let actual ← expressionClaim params edges fc H init
    let expected ← typeIndex params annot
    requireSubtype params edges H pos "binding annotation" name actual expected
    bodyClaims params edges fc (H ++ [(name,expected)]) result rest
  | _ => throw "generic claim checking requires a checked variable-copy body"

/-- Both production and independent consumption reconstruct these obligations.
Every source entry and expression must occur exactly once; no supplied point is
silently ignored. Subtyping uses the proved rigid-bound relation. -/
def check (f : Fragment.Fn) (typeParams : List Fragment.TypeParam)
    (fc : Fragment.Claims) : Except String Unit := do
  checkScheme f typeParams fc
  let params := typeParams.map (·.name)
  let edges ← boundEdges typeParams
  let (entries,expressions) := claimSites f.body
  let suppliedEntries := fc.envs.map Prod.fst
  let suppliedExpressions := fc.exprs.map Prod.fst
  if suppliedEntries.eraseDups.length != suppliedEntries.length ||
      suppliedEntries.length != entries.length || suppliedEntries.any (fun p => !entries.contains p) then
    throw "generic entry claims: missing, duplicate or unmatched statement site"
  if suppliedExpressions.eraseDups.length != suppliedExpressions.length ||
      suppliedExpressions.length != expressions.length || suppliedExpressions.any (fun p => !expressions.contains p) then
    throw "generic expression claims: missing, duplicate or unmatched expression site"
  let env ← f.params.mapM fun p => do return (p.name, ← typeIndex params p.ty)
  bodyClaims params edges fc env (← typeIndex params f.ret) f.body

private def paramT : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "param"), ("name", toJson "T")]])]

private def idFn : Fragment.Fn :=
  ⟨"id", (0, 2), [⟨"x", paramT⟩], paramT, [.ret (10, 18) (.var (17, 18) "x")]⟩

private def idClaims : Fragment.Claims :=
  ⟨"id", (0, 2), [("x", paramT)], paramT, [], []⟩

private def tpT : Fragment.TypeParam := ⟨"T", none⟩

private def tpTbool : Fragment.TypeParam := ⟨"T", some booleanType⟩

private def asBoolFn : Fragment.Fn :=
  ⟨"asBoolean", (0, 2), [⟨"x", paramT⟩], booleanType, [.ret (10, 18) (.var (17, 18) "x")]⟩

private def asBoolClaims : Fragment.Claims :=
  ⟨"asBoolean", (0, 2), [("x", paramT)], booleanType, [], []⟩

#guard (match checkScheme idFn [tpT] idClaims with | .ok () => true | _ => false)
#guard (match checkScheme {idFn with body := [.effect (10, 18) (.var (17, 18) "x")]} [tpT] idClaims with
  | .error e => "generic identity requires".isPrefixOf e
  | _ => false)
#guard (match checkScheme idFn [tpT, tpT] idClaims with
  | .error e => "duplicate type parameter".isPrefixOf e
  | _ => false)
#guard (match checkScheme asBoolFn [tpTbool] asBoolClaims with | .ok () => true | _ => false)
#guard (match checkScheme asBoolFn [tpT] asBoolClaims with
  | .error e => "generic return".isPrefixOf e
  | _ => false)
#guard (match checkScheme {idFn with body := [.ret (10, 18) (.lit (17, 18) (.vbool true))]}
    [tpTbool] idClaims with
  | .error e => "an upper bound does not justify true".isPrefixOf e
  | _ => false)

private def bindFn : Fragment.Fn :=
  ⟨"bind", (0, 2), [⟨"x", paramT⟩], paramT,
    [.cst (2, 3) "y" (some paramT) (.var (4, 5) "x"),
     .ret (6, 7) (.var (8, 9) "y")]⟩

private def bindClaims : Fragment.Claims :=
  ⟨"bind", (0, 2), [("x", paramT)], paramT, [], []⟩

private def fstFn : Fragment.Fn :=
  ⟨"fst", (0, 2), [⟨"x", paramT⟩, ⟨"y", paramT⟩], paramT,
    [.ret (10, 18) (.var (17, 18) "x")]⟩

private def fstClaims : Fragment.Claims :=
  ⟨"fst", (0, 2), [("x", paramT), ("y", paramT)], paramT, [], []⟩

#guard (match checkScheme bindFn [tpT] bindClaims with | .ok () => true | _ => false)
#guard (match checkScheme fstFn [tpT] fstClaims with | .ok () => true | _ => false)
#guard (match checkScheme {bindFn with body :=
    [.cst (2, 3) "y" (some paramT) (.var (4, 5) "x"),
     .ret (6, 7) (.var (8, 9) "x")]} [tpT] bindClaims with
  | .ok () => true | _ => false)
#guard (match checkScheme {bindFn with body :=
    [.cst (2, 3) "y" none (.var (4, 5) "x"),
     .ret (6, 7) (.var (8, 9) "y")]} [tpT] bindClaims with
  | .error e => "generic const requires".isPrefixOf e | _ => false)

end Verification.ExperimentState.GenericSource
