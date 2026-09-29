import Verification.Model.Source.EquationStore

/-! Lowering source declarations to recursive equations (RECURSIVE-EQUATIONS
§8), on parser output: the upstream `Promise` and `PromiseLike`, the growing
`Pair`, the recursive alias `Box`, a class's generic methods and an upstream
Skip runtime document. The fixtures are the parser's documents for pipeline
cases, spans zeroed. What a pipeline case cannot show is kept here: the
number of heads (no family is enumerated), the variances the checker
computes for them, and the refusals no source reaches alone. -/
namespace Verification.Model.EquationLoweringTests
open Lean EquationGraphs EquationLowering

def parse (text : String) : Json := (Json.parse text).toOption.getD .null

def promiseDoc : Json := parse (include_str "EquationLowering/promise-covariance.json")
def pairDoc : Json := parse (include_str "EquationLowering/generic-growing-application.json")
def boxDoc : Json := parse (include_str "EquationLowering/box.json")
def classDoc : Json := parse (include_str "EquationLowering/class-generic-method.json")
def sumDoc : Json := parse (include_str "EquationLowering/sum-collections.json")

/-- A claims document whose one function's parameters are claimed at the
given label lists. -/
def claimsDoc (labels : List Json) : Json :=
  Json.mkObj [("types", toJson SourceTypes.initial),
    ("functions", Json.arr #[Json.mkObj [("name", "f"), ("namePos", toJson [0, 1]),
      ("params", Json.arr (labels.zipIdx.map fun (A, i) =>
        Json.mkObj [("name", toJson s!"x{i}"), ("type", A), ("current", .null)]).toArray),
      ("result", toJson [3]), ("entries", Json.arr #[]), ("expressions", Json.arr #[])]])]

def head? (L : SourceLowering) (name : String) : Option Nat :=
  (L.store.heads.toList.map (·.name)).idxOf? name

/-- The variance the checker computes for a head of the frozen equations. -/
def variance? (L : SourceLowering) (name : String) : Option (List Variance) :=
  match EquationStore.freeze L.store with
  | .ok F => (head? L name).bind fun h => F.equations.variances.of h
  | .error _ => none

def binders? (L : SourceLowering) (name : String) : Option (List String) :=
  (head? L name).bind fun h => (L.store.heads[h]?).map (·.binders.map (·.name))

def annotation? (L : SourceLowering) (path : String) : Option (List Tree) := L.annotations.lookup path

/-- The claimed parameters' labels, read back from the lowered document. -/
def claimed (L : SourceLowering) : List (List Tree) :=
  match (L.claims.getObjValAs? (Array Json) "functions").toOption.bind (·[0]?) with
  | some f => ((f.getObjValAs? (Array Json) "params").toOption.getD #[]).toList.filterMap fun p =>
      ((p.getObjValAs? (Array Json) "type").toOption.bind fun A => (A.toList.mapM Tree.fromJson).toOption)
  | none => []

def run (doc : Json) (claims : List Json := []) (f : SourceLowering → Bool) : Bool :=
  match source doc (claimsDoc claims) with
  | .ok L => f L
  | .error _ => false

def refusal (doc : Json) : String := match source doc (claimsDoc []) with
  | .ok _ => ""
  | .error e => e

/-! ### `Promise` and `PromiseLike` -/

-- Finitely many heads: `Promise`, `PromiseLike`, their generic methods, the
-- callbacks' literal heads and primitives. `catch`'s `Promise<T | R>` is an
-- application in the method's template, not a new head.
#guard run promiseDoc [] fun L =>
  L.store.heads.size == 21 &&
  (head? L "Promise.\"then\"").isSome && (head? L "Promise.\"catch\"").isSome &&
  (head? L "PromiseLike.\"then\"").isSome &&
  binders? L "Promise.\"then\"" == some ["TResult1", "TResult2"]

-- The computed variances: `Promise` and `PromiseLike` covariant.
#guard run promiseDoc [] fun L =>
  variance? L "Promise" == some [.co] && variance? L "PromiseLike" == some [.co] &&
  variance? L "Promise.\"catch\"" == some [.co]

-- The primitive values' heads come first, as `LabelStore.Labels` requires.
#guard run promiseDoc [] fun L => (L.store.heads.toList.map (·.name)).take 4 == ["null", "true", "false", "undefined"]

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
  | some p, some q => claimed L == [[mkApp p [[]]], [canonMeet [mkApp p [[]], mkApp q [[]]]]]
  | _, _ => false

-- A claim naming a declaration at the wrong arity is refused.
#guard (source promiseDoc (claimsDoc [.arr #[Json.mkObj [("decl", 0)]]])).toOption.isNone

/-! ### `Pair<[T, U]>` -/

-- `push<U>(u: U): Pair<[T, U]>` is `Pair.push(arg 0)` binding `U`, whose
-- result applies `Pair` to the tuple head lifted over `T` and `U`: the family
-- grows by application, and the heads stay finitely many. `Pair` is
-- invariant through the mutable tuple.
#guard run pairDoc [] fun L =>
  L.store.heads.size == 51 &&
  variance? L "Pair" == some [.inv] &&
  (head? L "Pair.\"push\"").bind (fun h => L.store.heads[h]?.map fun d =>
    (d.kinds.length, d.binders.map (·.name))) == some (1, ["U"])

/-! ### `Box<T> = {v: T; next: Box<[T]>}` -/

-- The recursive alias's body is guarded by its object type: one `Box` head,
-- whose `next` applies it to the tuple `[T]`. `Box<Box<never>>` from a claim
-- is an application of that head.
def boxIndex : Nat := 2
def boxNever : Json := Json.mkObj [("decl", boxIndex), ("args", Json.arr #[Json.arr #[]])]
#guard run boxDoc [.arr #[Json.mkObj [("decl", boxIndex), ("args", Json.arr #[.arr #[boxNever]])]]] fun L =>
  match head? L "Box" with
  | some b => variance? L "Box" == some [.inv] && claimed L == [[mkApp b [[mkApp b [[]]]]]]
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

-- `pick<V>` and `run<U>` are heads `Helper.pick` and `Helper.run` binding
-- their own `V` and `U`; the prototype closure's binder, spelled
-- `"pick"#0` by the parser, is its name's placeholder, which the
-- closure's scheme binds when the unit is extracted.
#guard run classDoc [] fun L =>
  match head? L "Helper.\"pick\"" with
  | some _ => binders? L "Helper.\"pick\"" == some ["V"] &&
    (match annotation? L "/init/0/bindings/0/init/params/0/type" with
      | some [t] => isPlaceholder t && annotation? L "/init/0/bindings/0/init/result" == some [t]
      | _ => false)
  | none => false

/-! ### An upstream Skip runtime document -/

-- `sum-collections`' declarations lower, their declared bounds checked, and
-- their variances are computed. The heads whose templates meet a parameter
-- with a type (`T & DepSafe`) relate `x & B` to `y & B` through the entry's
-- hypotheses: a meet reads its parameter parts through them (`meetBelow`,
-- `PartCovers`), in a pair and in a premise (`MeetHyp`).
#guard run sumDoc [] fun L =>
  variance? L "Values" == some [.inv] &&
  variance? L "Reducer" == some [.contra, .inv] &&
  variance? L "EagerCollection" == some [.inv, .inv] &&
  variance? L "LazyCollection" == some [.contra, .inv]

end Verification.Model.EquationLoweringTests
