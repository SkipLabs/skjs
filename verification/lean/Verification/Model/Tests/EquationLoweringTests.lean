import Verification.Model.Source.EquationStore

/-! Lowering source declarations to recursive equations (RECURSIVE-EQUATIONS
§8), on parser output, spans zeroed: annotations over the upstream `Promise`,
the non-regular recursive alias `Box`, and an unguarded alias no source
reaches. -/
namespace Verification.Model.EquationLoweringTests
open Lean EquationGraphs EquationLowering

def parse (text : String) : Json := (Json.parse text).toOption.getD .null

def promiseDoc : Json := parse (include_str "EquationLowering/promise-covariance.json")
def boxDoc : Json := parse (include_str "EquationLowering/box.json")

/-- A claims document whose one function's parameters are claimed at the
given label lists. -/
def claimsDoc (labels : List Json) : Json :=
  Json.mkObj [("types", toJson ([[.nul], [.boolLit true], [.boolLit false], [.undef]] :
      List (List (PositiveNormalization.Clause (List Nat))))),
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

-- `widen(p: Promise<number>): Promise<number | string>`: its annotations are
-- applications of the one `Promise` head.
#guard run promiseDoc [] fun L =>
  match head? L "Promise", head? L "number", head? L "string" with
  | some p, some n, some s =>
    annotation? L "/functions/0/params/0/type" == some [mkApp p [[mkApp n []]]] &&
    annotation? L "/functions/0/retType" == some [mkApp p [normUnion [mkApp n [], mkApp s []]]]
  | _, _, _ => false

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

end Verification.Model.EquationLoweringTests
