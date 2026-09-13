import Verification.ExperimentState.SourceInput
import Verification.ExperimentState.CellClaims

/-! Source extraction of first-order generic function bodies.

A function `id<T>(x: T): T { return x }` is checked under a rigid `T` by the
existing identity theorem. Bodies may copy `T` through `const y: T = x` and
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

def boundBoolean (bound : Option Json) : Except String Bool :=
  match bound with
  | none => return false
  | some b =>
    if isBooleanType b then return true
    else throw "only `extends boolean` is in the fragment"

def copyInit (t : String) (env : List String) : SourceInput.Expr → Except String Unit
  | .var _ name =>
    if name ∈ env then return ()
    else throw s!"generic body must initialize from a '{t}' binding"
  | _ => throw "generic body requires `const y: T = x`"

def copyConst (t : String) (env : List String) : SourceInput.Stmt → Except String String
  | .cst _ name (some annot) init => do
    if name == "undefined" then throw "shadowing undefined is outside the source slice"
    if name ∈ env then throw "active-name shadowing is outside the source slice"
    let pt ← paramName annot
    if pt != t then throw s!"generic const must be annotated '{t}'"
    copyInit t env init
    return name
  | .cst _ _ none _ => throw "generic const requires a T annotation"
  | _ => throw "generic body requires `const y: T = x` then `return y`"

def copyReturn (t : String) (env : List String) (ext : Bool) :
    SourceInput.Stmt → Except String Unit
  | .ret _ (.var _ name) =>
    if name ∈ env then return ()
    else throw s!"generic body must return a '{t}' binding"
  | .ret _ (.lit _ (.vbool true)) =>
    if ext then throw "T extends boolean does not justify true ≤ T"
    else throw "generic identity requires a body that is `return x`"
  | _ => throw "generic identity requires a body that is `return x`"

partial def copyBody (t : String) (env : List String) (ext : Bool) :
    List SourceInput.Stmt → Except String Unit
  | [] => throw "generic identity requires a body that is `return x`"
  | [last] => copyReturn t env ext last
  | s :: rest => do
    let name ← copyConst t env s
    copyBody t (env ++ [name]) ext rest

/-- Identity, `const y: T = x; return y`, extra `T` parameters, or `T → boolean`
under `T extends boolean`. -/
def check (f : SourceInput.Fn) (typeParams : List SourceInput.TypeParam)
    (fc : SourceInput.Claims) : Except String Unit := do
  if f.name != fc.name || f.namePos != fc.namePos then
    throw "function claim identity mismatch"
  let [tp] := typeParams | throw "only one type parameter is in the fragment"
  let t := tp.name
  if t == "undefined" then throw "shadowing undefined is outside the source slice"
  let ext ← boundBoolean tp.bound
  if f.params.isEmpty then throw "generic body requires a value parameter of type T"
  let names := f.params.map (·.name)
  if names.eraseDups.length != names.length then throw "duplicate source parameter"
  for p in f.params do
    if p.name == "undefined" then throw "shadowing undefined is outside the source slice"
    let pt ← paramName p.ty
    if pt != t then throw s!"generic body requires parameter '{p.name}' to be '{t}'"
  copyBody t names ext f.body
  if f.params.length != fc.params.length then throw "parameter claim count mismatch"
  for (p, c) in f.params.zip fc.params do
    if p.name != c.1 then throw "parameter claim name or order mismatch"
    let claimedPt ← paramName c.2
    if claimedPt != t then
      throw "claimed generic identity types differ from the source annotation"
  if isBooleanType f.ret then
    if !ext then
      throw "returning a type parameter as boolean requires T extends boolean"
    unless isBooleanType fc.ret do
      throw "claimed generic identity types differ from the source annotation"
  else
    let rt ← paramName f.ret
    let claimedR ← paramName fc.ret
    if rt != t || claimedR != t then
      throw s!"generic identity requires parameter and result to be '{t}'"

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
  | .error e => "only one type parameter".isPrefixOf e
  | _ => false)
#guard (match check asBoolFn [tpTbool] asBoolClaims with | .ok () => true | _ => false)
#guard (match check asBoolFn [tpT] asBoolClaims with
  | .error e => "returning a type parameter as boolean".isPrefixOf e
  | _ => false)
#guard (match check {idFn with body := [.ret (10, 18) (.lit (17, 18) (.vbool true))]}
    [tpTbool] idClaims with
  | .error e => "T extends boolean does not justify true".isPrefixOf e
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
