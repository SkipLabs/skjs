import Verification.Model.Source.EquationLowering

/-! Lowering source declarations to recursive equations (RECURSIVE-EQUATIONS
§8), on parser output: the upstream `Promise` and `PromiseLike`, the growing
`Pair`, the recursive alias `Box`, a class's generic methods and an upstream
Skip runtime document. The fixtures are the parser's documents for pipeline
cases, spans zeroed. No request reads the module yet, so these checks stand
in for pipeline cases until S6 wires it in. -/
namespace Verification.Model.EquationLoweringTests
open Lean EquationGraphs EquationLowering

def parse (text : String) : Json := (Json.parse text).toOption.getD .null

def promiseDoc : Json := parse (include_str "EquationLowering/promise-covariance.json")
def pairDoc : Json := parse (include_str "EquationLowering/generic-growing-application.json")
def boxDoc : Json := parse (include_str "EquationLowering/box.json")
def classDoc : Json := parse (include_str "EquationLowering/class-generic-method.json")
def sumDoc : Json := parse (include_str "EquationLowering/sum-collections.json")

def head? (L : Lowered) (name : String) : Option Nat := L.names.toList.idxOf? name

def header? (L : Lowered) (name : String) : Option Header :=
  (head? L name).bind (L.equations.signature[·]?)

def variance? (L : Lowered) (name : String) : Option (List Variance) :=
  (header? L name).map (·.variance.map (·.2))

def checked (L : Lowered) : Bool := match L.variances with
  | .ok _ => true
  | .error _ => false

def refused (L : Lowered) : List String := match L.variances with
  | .ok _ => []
  | .error hs => hs

def trees (U : List (Label sig)) : List Tree := U.map (·.1)

def annotation? (L : Lowered) (path : String) : Option (List Tree) :=
  (L.annotations.lookup path).map trees

def run (doc : Json) (claims : List Json := []) (f : Lowered → Bool) : Bool :=
  match lower doc claims with
  | .ok L => f L
  | .error _ => false

def refusal (doc : Json) : String := match lower doc with
  | .ok _ => ""
  | .error e => e

/-! ### `Promise` and `PromiseLike` -/

-- Finitely many heads: `Promise`, `PromiseLike`, their generic methods, the
-- callbacks' literal heads and primitives. `catch`'s `Promise<T | R>` is an
-- application in the method's template, not a new head.
#guard run promiseDoc [] fun L =>
  L.equations.signature.length == 21 &&
  (head? L "Promise.\"then\"").isSome && (head? L "Promise.\"catch\"").isSome &&
  (head? L "PromiseLike.\"then\"").isSome &&
  (header? L "Promise.\"then\"").map (·.binders.map (·.name)) == some ["TResult1", "TResult2"]

-- The proposed variances check, `Promise` and `PromiseLike` covariant.
#guard run promiseDoc [] fun L =>
  checked L && variance? L "Promise" == some [.co] && variance? L "PromiseLike" == some [.co] &&
  variance? L "Promise.\"catch\"" == some [.co]

-- The primitive values' heads come first, as `LabelStore.Labels` requires.
#guard run promiseDoc [] fun L => L.names.toList.take 4 == ["null", "true", "false", "undefined"]

-- `widen(p: Promise<number>): Promise<number | string>`: its annotations are
-- applications of the one `Promise` head.
#guard run promiseDoc [] fun L =>
  match head? L "Promise", head? L "number", head? L "string" with
  | some p, some n, some s =>
    annotation? L "/functions/0/params/0/type" == some [mkApp p [[mkApp n []]]] &&
    annotation? L "/functions/0/retType" == some [mkApp p [normUnion [mkApp n [], mkApp s []]]]
  | _, _, _ => false

-- Source-claims labels (§9.1): a `decl` application, and a `meet` as one
-- meet label of its two parts.
def promiseNever : Json := Json.mkObj [("decl", 0), ("args", Json.arr #[Json.arr #[]])]
def promiseLikeNever : Json := Json.mkObj [("decl", 1), ("args", Json.arr #[Json.arr #[]])]
#guard run promiseDoc [.arr #[promiseNever],
    .arr #[Json.mkObj [("meet", Json.arr #[.arr #[promiseNever], .arr #[promiseLikeNever]])]]] fun L =>
  match head? L "Promise", head? L "PromiseLike" with
  | some p, some q =>
    L.claims.map trees == [[mkApp p [[]]], [canonMeet [mkApp p [[]], mkApp q [[]]]]]
  | _, _ => false

-- A claim naming a declaration at the wrong arity is refused.
#guard (lower promiseDoc [.arr #[Json.mkObj [("decl", 0)]]]).toOption.isNone

/-! ### `Pair<[T, U]>` -/

-- `push<U>(u: U): Pair<[T, U]>` is `Pair.push(arg 0)` binding `U`, whose
-- result applies `Pair` to the tuple head lifted over `T` and `U`: the family
-- grows by application, and the heads stay finitely many. `Pair` is
-- invariant through the mutable tuple, as its declaration checks.
#guard run pairDoc [] fun L =>
  L.equations.signature.length == 51 && checked L &&
  variance? L "Pair" == some [.inv] &&
  (header? L "Pair.\"push\"").map (fun h => (h.parameters, h.binders.map (·.name))) == some (1, ["U"])

/-! ### `Box<T> = {v: T; next: Box<[T]>}` -/

-- The recursive alias's body is guarded by its object type: one `Box` head,
-- whose `next` applies it to the tuple `[T]`. `Box<Box<never>>` from a claim
-- is an application of that head.
def boxIndex : Nat := 2
def boxNever : Json := Json.mkObj [("decl", boxIndex), ("args", Json.arr #[Json.arr #[]])]
#guard run boxDoc [.arr #[Json.mkObj [("decl", boxIndex), ("args", Json.arr #[.arr #[boxNever]])]]] fun L =>
  match head? L "Box" with
  | some b => checked L && variance? L "Box" == some [.inv] &&
    L.claims.map trees == [[mkApp b [[mkApp b [[]]]]]]
  | none => false

/-! ### Unguarded aliases -/

-- `type T<X> = X | T<[X]>`: the recursive reference is under no constructor,
-- so inlining would not end; it is refused, located at the using unit.
def unguardedDoc : Json := parse r#"{
  "declarations": {"roots": [], "values": [], "symbols": [], "definitions": [
    {"declaration": {"module": "t.ts", "name": "T", "span": [0, 0]},
     "parameters": [{"name": "X", "span": [0, 0], "bound": null, "default": null}], "bases": [],
     "expression": {"k": "union", "span": [0, 0], "parts": [
       {"k": "parameter", "index": 0, "span": [0, 0]},
       {"k": "reference", "span": [0, 0],
        "reference": {"name": "T", "span": [0, 0], "arguments": [],
          "target": {"module": "t.ts", "name": "T", "span": [0, 0]}},
        "args": [{"k": "tuple", "readonly": false, "presence": "dense", "span": [0, 0],
          "required": [{"k": "parameter", "index": 0, "span": [0, 0]}], "optional": [], "rest": null}]}]}}]},
  "functions": [{"name": "f", "typeParams": [], "body": [],
    "params": [{"name": "x", "type": {"k": "reference", "span": [0, 0],
      "reference": {"name": "T", "span": [0, 0], "arguments": [],
        "target": {"module": "t.ts", "name": "T", "span": [0, 0]}},
      "args": [{"k": "atom", "name": "number", "span": [0, 0]}]}}],
    "retType": {"k": "atom", "name": "number", "span": [0, 0]}}],
  "init": []}"#

#guard refusal unguardedDoc ==
  "/functions/0/params/0/type: unguarded alias cycle through T: a recursive alias must reach itself through an object, array, tuple or function type"

/-! ### A class's generic methods -/

-- `pick<V>` and `run<U>` are heads `Helper.pick` and `Helper.run`; the
-- prototype closure's binder, spelled `"pick"#0:null^0` by the parser, is
-- the owned binder `bound(Helper.pick, [], 0)`.
#guard run classDoc [] fun L =>
  match head? L "Helper.\"pick\"" with
  | some m => checked L &&
    annotation? L "/init/0/bindings/0/init/params/0/type" == some [mkBound m [] 0] &&
    annotation? L "/init/0/bindings/0/init/result" == some [mkBound m [] 0]
  | none => false

/-! ### An upstream Skip runtime document -/

-- `sum-collections`' declarations lower, their declared bounds checked. The
-- variance check refuses the heads whose templates meet a parameter with a
-- type (`T & DepSafe`): a family entry relates `meet(x, B) ≤ meet(y, B)`
-- only through a table pair, and a meet target is read part by part without
-- the entry's hypotheses (`MeetTarget`), so none is valid even as
-- invariant. This is a kernel gap, not a lowering one.
#guard run sumDoc [] fun L =>
  !checked L && (refused L).contains "Values" && (refused L).contains "Reducer"

end Verification.Model.EquationLoweringTests
