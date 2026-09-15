import Verification.ExperimentState.SourceInput
import Verification.ExperimentState.CellClaims
import Verification.ExperimentState.GenericBounds

/-! Source extraction of first-order generic function bodies.

Variable-copy bodies are checked under distinct rigid parameters and forward
upper bounds by the existing variable, let and subtype rules. Bodies may copy `T` through `const y: T = x` and
extra parameters (`fst`), along `letE_safeP` and `var_safeP`.
`T extends boolean` is an assumption `T ≤ boolean`:
`asBoolean<T extends boolean>(x: T): boolean { return x }` transports along
that inclusion. It does not justify `true ≤ T`. Other generic shapes remain
outside the fragment. SKJS still supplies the parameter and result claims. -/
namespace Verification.ExperimentState.GenericSource
open Lean Wire

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

def boundEdges (params : List SourceInput.TypeParam) : Except String (List (Nat × Nat)) := do
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

def variableType (env : List (String × Nat)) : SourceInput.Expr → Except String Nat
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
    (env : List (String × Nat)) (result : Nat) : List SourceInput.Stmt → Except String Unit
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
def check (f : SourceInput.Fn) (typeParams : List SourceInput.TypeParam)
    (fc : SourceInput.Claims) : Except String Unit := do
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

private def paramT : Json :=
  Json.mkObj [("top", toJson false),
    ("atoms", toJson [Json.mkObj [("a", toJson "param"), ("name", toJson "T")]])]

private def idFn : SourceInput.Fn :=
  ⟨"id", (0, 2), [⟨"x", paramT⟩], paramT, [.ret (10, 18) (.var (17, 18) "x")]⟩

private def idClaims : SourceInput.Claims :=
  ⟨"id", (0, 2), [("x", paramT)], paramT, [], []⟩

private def tpT : SourceInput.TypeParam := ⟨"T", none⟩

private def tpTbool : SourceInput.TypeParam := ⟨"T", some booleanType⟩

private def asBoolFn : SourceInput.Fn :=
  ⟨"asBoolean", (0, 2), [⟨"x", paramT⟩], booleanType, [.ret (10, 18) (.var (17, 18) "x")]⟩

private def asBoolClaims : SourceInput.Claims :=
  ⟨"asBoolean", (0, 2), [("x", paramT)], booleanType, [], []⟩

#guard (match check idFn [tpT] idClaims with | .ok () => true | _ => false)
#guard (match check {idFn with body := [.effect (10, 18) (.var (17, 18) "x")]} [tpT] idClaims with
  | .error e => "generic identity requires".isPrefixOf e
  | _ => false)
#guard (match check idFn [tpT, tpT] idClaims with
  | .error e => "duplicate type parameter".isPrefixOf e
  | _ => false)
#guard (match check asBoolFn [tpTbool] asBoolClaims with | .ok () => true | _ => false)
#guard (match check asBoolFn [tpT] asBoolClaims with
  | .error e => "generic return".isPrefixOf e
  | _ => false)
#guard (match check {idFn with body := [.ret (10, 18) (.lit (17, 18) (.vbool true))]}
    [tpTbool] idClaims with
  | .error e => "an upper bound does not justify true".isPrefixOf e
  | _ => false)

private def bindFn : SourceInput.Fn :=
  ⟨"bind", (0, 2), [⟨"x", paramT⟩], paramT,
    [.cst (2, 3) "y" (some paramT) (.var (4, 5) "x"),
     .ret (6, 7) (.var (8, 9) "y")]⟩

private def bindClaims : SourceInput.Claims :=
  ⟨"bind", (0, 2), [("x", paramT)], paramT, [], []⟩

private def fstFn : SourceInput.Fn :=
  ⟨"fst", (0, 2), [⟨"x", paramT⟩, ⟨"y", paramT⟩], paramT,
    [.ret (10, 18) (.var (17, 18) "x")]⟩

private def fstClaims : SourceInput.Claims :=
  ⟨"fst", (0, 2), [("x", paramT), ("y", paramT)], paramT, [], []⟩

#guard (match check bindFn [tpT] bindClaims with | .ok () => true | _ => false)
#guard (match check fstFn [tpT] fstClaims with | .ok () => true | _ => false)
#guard (match check {bindFn with body :=
    [.cst (2, 3) "y" (some paramT) (.var (4, 5) "x"),
     .ret (6, 7) (.var (8, 9) "x")]} [tpT] bindClaims with
  | .ok () => true | _ => false)
#guard (match check {bindFn with body :=
    [.cst (2, 3) "y" none (.var (4, 5) "x"),
     .ret (6, 7) (.var (8, 9) "y")]} [tpT] bindClaims with
  | .error e => "generic const requires".isPrefixOf e | _ => false)

end Verification.ExperimentState.GenericSource
