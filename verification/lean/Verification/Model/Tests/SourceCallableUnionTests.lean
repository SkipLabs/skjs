import Verification.Model.Source.SourceExtraction

namespace Verification.Model.SourceCallableUnionTests
open Lean SourceExtraction ProgramTyping

private def primitive (a : String) : Json := Json.mkObj [("top",toJson false),
  ("atoms",toJson [Json.mkObj [("a",toJson a)]])]
private def literal (b : Bool) : Json := Json.mkObj [("top",toJson false),
  ("atoms",toJson [Json.mkObj [("a",toJson "booleanlit"),("v",toJson (if b then "true" else "false"))]])]
/-- A signature indifferent to its receiver states `unknown` for it. -/
private def unknown : Json := Json.mkObj [("top",toJson true),("atoms",toJson ([] : List Json))]
private def arrow (arg result : Json) : Json := Json.mkObj
  [("a",toJson "function"),("this",unknown),("params",toJson [arg]),("result",result),
   ("construct",toJson "unknown"),("array",toJson "unknown")]
private def union : Json := Json.mkObj [("top",toJson false),("atoms",toJson
  [arrow (primitive "null") (literal true),arrow (primitive "null") (literal false)])]
/-- Label 4 is unknown, every arrow's receiver. -/
private def table : SourceTypes.Table := SourceTypes.initial ++
  RequestJson.rows [[.top], [.arrs [⟨[4], [[0]], [1], .unrestricted⟩] []], [.arrs [⟨[4], [[0]], [2], .unrestricted⟩] []], [.arrs [⟨[4], [[0]], [1,2], .unrestricted⟩] []]]
private def source : Fragment.Fn :=
  ⟨"invoke",(0,1),[⟨"f",union,false⟩],primitive "boolean",
   [.ret (2,16) (.app (3,16)
     (.lam (3,12) "unit" (primitive "null") (primitive "boolean")
       (.app (7,12) (.var (7,8) "f") (.var (9,10) "unit")))
     (.lit (14,15) .vnull))]⟩
private def claims : SourceClaims.Function Nat :=
  ⟨"invoke",(0,1),[("f",.ok [5,6])],.ok [1,2],
   [(2,[("f",.ok [5,6])])],
   [((3,16),.ok [1,2]),((3,12),.ok [7]),((7,12),.ok [1,2]),
    ((7,8),.ok [5,6]),((9,10),.ok [0]),((14,15),.ok [0])],[],[],[]⟩

-- Primitive-only function unions decode and acquire direct recipes inside
-- closures, preserving all alternatives and the source consumer checks.
#guard ((Fragment.translate union).run' SourceTypes.initial).toOption == some [5,6]
#guard (extractNormalizedFn table source claims).toOption.isSome

-- Compiling this specializes the extraction at the finite table.
set_option maxHeartbeats 1000000 in
private def checkWith (T : SourceTypes.Table) (f : Fragment.Fn) (c : SourceClaims.Function Nat) : Except String Unit := do
  let r ← extractNormalizedFn T f c
  let proofs ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels (LabelStore.StoreView.valid r.types) (LabelStore.Store.projection r.types) 0 r.obligations
  let evidence ← RequestJson.produceJson RequestJson.Table (toJson r.toRequest) 8 [] proofs
    r.sourceMap (some r.searchLabels) r.assertions r.cuts
  let response ← RequestJson.decodeResponse r.toRequest evidence
  if !checkRequests [r] ⟨[response],[proofs]⟩ then throw "source consumer rejected evidence"
private def check := checkWith table
private def ok (x : Except String α) : Bool := match x with | .ok _ => true | .error _ => false
#guard ok (check source claims)
-- The union result cannot be silently narrowed to one alternative.
#guard !ok (check source {claims with exprs := claims.exprs.map fun (pos,c) =>
  if pos == (7,12) then (pos,.ok [1]) else (pos,c)})
-- Every possible callee must accept the argument.
private def wrongArgument : Fragment.Fn := {source with body :=
  [.ret (2,16) (.app (3,16)
    (.lam (3,12) "unit" (primitive "null") (primitive "boolean")
      (.app (7,12) (.var (7,8) "f") (.lit (9,10) (.vbool true))))
    (.lit (14,15) .vnull))]}
#guard !ok (check wrongArgument {claims with exprs := claims.exprs.map fun (pos,c) =>
  if pos == (9,10) then (pos,.ok [1]) else (pos,c)})
-- Saving both operands explicitly keeps source name lookup and evaluation
-- order correct after adding the anonymous callee slot. Inside the closure,
-- slot 0 is its receiver, slot 1 its parameter and the captured `f` slot 2.
-- The closure's graph code: the captured `f` (slot 2), then the parameter,
-- each bound, then the call of the saved callee on the saved actual.
#guard match extractNormalizedFn table source claims with
  | .error _ => false
  | .ok r => r.codes.any fun (q : RequestJson.CodeRequest Nat) =>
      q.entry.exprs == [.var 0, .invoke (.var 1) .undef [.var 0], .var 2, .var 2] &&
        q.entry.captures == [[5,6]]

-- One successful alternative does not excuse another incompatible domain.
private def mixedDomain : Json := Json.mkObj [("top",toJson false),("atoms",toJson
  [arrow (primitive "null") (literal true),arrow (primitive "boolean") (literal false)])]
#guard (extractNormalizedFn (table.set 6 (PositiveGraphs.GraphRow.clauses [.arrs [⟨[4], [[1,2]], [2], .unrestricted⟩] []]))
  {source with params := [⟨"f", mixedDomain, false⟩]} claims).toOption.isSome
#guard !ok (checkWith (table.set 6 (PositiveGraphs.GraphRow.clauses [.arrs [⟨[4], [[1,2]], [2], .unrestricted⟩] []]))
  {source with params := [⟨"f", mixedDomain, false⟩]} claims)

-- A source-level nullable function remains gated until a guard establishes
-- callability; it cannot borrow the callable union branch's signature.
private def nullable : Json := Json.mkObj [("top",toJson false),("atoms",toJson
  [Json.mkObj [("a",toJson "null")],arrow (primitive "null") (literal true)])]
#guard !ok (check {source with params := [⟨"f", nullable, false⟩]}
  {claims with
    params := [("f",.ok [0,5])]
    envs := [(2,[("f",.ok [0,5])])]
    exprs := claims.exprs.map fun (pos,c) => if pos == (7,8) then (pos,.ok [0,5]) else (pos,c)})

-- Guard polarity, nullable captures and narrowed guarded results are covered
-- through actual producer claims in tests/callables.mts and tests/null-tests.mts.
-- Explicit source claims isolate verifier coverage from SKJS's documented
-- collapse of incomparable arrow intersections to never. Each union alternative
-- must select its own applicable overload; the useful signature is not always
-- first, and Boolean arguments reverse which signature is selected.
private def overloaded (D R D' R' : Json) : Json := Json.mkObj
  [("a",toJson "function"),("this",unknown),("params",toJson [D]),("result",R),
   ("construct",toJson "unknown"),("array",toJson "unknown"),
   ("and",toJson [arrow D' R'])]
private def overloadUnion (missingNull : Bool := false) : Json := Json.mkObj
  [("top",toJson false),("atoms",toJson
    [overloaded (primitive "null") (literal true) (primitive "boolean") (literal false),
     if missingNull then arrow (primitive "boolean") (literal true)
     else overloaded (primitive "boolean") (literal true) (primitive "null") (literal false)])]
private def overloadTable : SourceTypes.Table :=
  (table.set 5 (PositiveGraphs.GraphRow.clauses [.arrs [⟨[4], [[0]], [1], .unrestricted⟩,⟨[4], [[1,2]], [2], .unrestricted⟩] []])).set 6
    (PositiveGraphs.GraphRow.clauses [.arrs [⟨[4], [[1,2]], [1], .unrestricted⟩,⟨[4], [[0]], [2], .unrestricted⟩] []])
private def overloadSource (booleanArg : Bool) : Fragment.Fn :=
  {(if booleanArg then wrongArgument else source) with params := [⟨"f", overloadUnion, false⟩]}
private def overloadClaims (booleanArg : Bool) : SourceClaims.Function Nat :=
  {claims with exprs := claims.exprs.map fun (pos,c) =>
    if booleanArg && pos == (9,10) then (pos,.ok [1]) else (pos,c)}
#guard [false,true].all fun booleanArg =>
  ok (checkWith overloadTable (overloadSource booleanArg) (overloadClaims booleanArg))
#guard [false,true].all fun booleanArg =>
  !ok (checkWith overloadTable (overloadSource booleanArg)
    {(overloadClaims booleanArg) with exprs := (overloadClaims booleanArg).exprs.map fun (pos,c) =>
      if pos == (7,12) then (pos,.ok [1]) else (pos,c)})
-- A sibling's null overload cannot rescue a Boolean-only alternative.
private def incompleteOverloadSource : Fragment.Fn :=
  {source with params := [⟨"f",overloadUnion true,false⟩]}
private def incompleteOverloadTable := overloadTable.set 6 (PositiveGraphs.GraphRow.clauses [.arrs [⟨[4], [[1,2]], [1], .unrestricted⟩] []])
#guard (extractNormalizedFn incompleteOverloadTable incompleteOverloadSource claims).toOption.isSome
#guard !ok (checkWith incompleteOverloadTable incompleteOverloadSource claims)
end Verification.Model.SourceCallableUnionTests
