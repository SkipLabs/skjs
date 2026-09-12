import Verification.ExperimentState.SourceExtraction

namespace Verification.ExperimentState.SourceCallableUnionTests
open Lean SourceExtraction ProgramTyping

private def primitive (a : String) : Json := Json.mkObj [("top",toJson false),
  ("atoms",toJson [Json.mkObj [("a",toJson a)]])]
private def literal (b : Bool) : Json := Json.mkObj [("top",toJson false),
  ("atoms",toJson [Json.mkObj [("a",toJson "booleanlit"),("v",toJson (if b then "true" else "false"))]])]
private def arrow (arg result : Json) : Json := Json.mkObj
  [("a",toJson "function"),("params",toJson [arg]),("result",result),
   ("construct",toJson "unknown"),("array",toJson "unknown")]
private def union : Json := Json.mkObj [("top",toJson false),("atoms",toJson
  [arrow (primitive "null") (literal true),arrow (primitive "null") (literal false)])]
private def table : SourceTypes.Table := SourceTypes.initial ++
  [[.arrs [([0],[1])]], [.arrs [([0],[2])]], [.arrs [([0],[1,2])]]]
private def source : SourceInput.Fn :=
  ⟨"invoke",(0,1),[⟨"f",union⟩],primitive "boolean",
   [.ret (2,16) (.app (3,16)
     (.lam (3,12) "unit" (primitive "null") (primitive "boolean")
       (.app (7,12) (.var (7,8) "f") (.lit (9,10) .vnull)))
     (.lit (14,15) .vnull))]⟩
private def claims : SourceClaims.Function :=
  ⟨"invoke",(0,1),[("f",.ok [4,5])],.ok [1,2],
   [(2,[("f",.ok [4,5])])],
   [((3,16),.ok [1,2]),((3,12),.ok [6]),((7,12),.ok [1,2]),
    ((7,8),.ok [4,5]),((9,10),.ok [0]),((14,15),.ok [0])],[],[]⟩

-- Baseline: primitive-only unions decode, but source call extraction requires
-- one arrow clause even though the graph consumer can justify each alternative.
#guard ((SourceInput.translate union).run' SourceTypes.initial).toOption == some [4,5]
#guard match extractNormalizedFn table source claims with
  | .error e => e == "callee must name a source arrow"
  | .ok _ => false

private def check (f : SourceInput.Fn) (c : SourceClaims.Function) : Except String Unit := do
  let r ← extractNormalizedFn table f c
  let proofs ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  let evidence ← RequestJson.produceJson (toJson r.toRequest) 8 [] proofs
    r.sourceMap (some r.searchLabels) r.assertions r.cuts
  let response ← RequestJson.decodeResponse r.toRequest evidence
  if !checkRequests [r] ⟨[response],[proofs]⟩ then throw "source consumer rejected evidence"
private def ok (x : Except String α) : Bool := match x with | .ok _ => true | .error _ => false
#guard !ok (check source claims)
-- The union result cannot be silently narrowed to one alternative.
#guard !ok (check source {claims with exprs := claims.exprs.map fun (pos,c) =>
  if pos == (7,12) then (pos,.ok [1]) else (pos,c)})
-- Every possible callee must accept the argument.
private def wrongArgument : SourceInput.Fn := {source with body :=
  [.ret (2,16) (.app (3,16)
    (.lam (3,12) "unit" (primitive "null") (primitive "boolean")
      (.app (7,12) (.var (7,8) "f") (.lit (9,10) (.vbool true))))
    (.lit (14,15) .vnull))]}
#guard !ok (check wrongArgument {claims with exprs := claims.exprs.map fun (pos,c) =>
  if pos == (9,10) then (pos,.ok [1]) else (pos,c)})
end Verification.ExperimentState.SourceCallableUnionTests
