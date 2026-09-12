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
       (.app (7,12) (.var (7,8) "f") (.var (9,10) "unit")))
     (.lit (14,15) .vnull))]⟩
private def claims : SourceClaims.Function :=
  ⟨"invoke",(0,1),[("f",.ok [4,5])],.ok [1,2],
   [(2,[("f",.ok [4,5])])],
   [((3,16),.ok [1,2]),((3,12),.ok [6]),((7,12),.ok [1,2]),
    ((7,8),.ok [4,5]),((9,10),.ok [0]),((14,15),.ok [0])],[],[]⟩

-- Primitive-only function unions decode and acquire direct recipes inside
-- closures, preserving all alternatives and the source consumer checks.
#guard ((SourceInput.translate union).run' SourceTypes.initial).toOption == some [4,5]
#guard (extractNormalizedFn table source claims).toOption.isSome

private def checkWith (T : SourceTypes.Table) (f : SourceInput.Fn) (c : SourceClaims.Function) : Except String Unit := do
  let r ← extractNormalizedFn T f c
  let proofs ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  let evidence ← RequestJson.produceJson (toJson r.toRequest) 8 [] proofs
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
private def wrongArgument : SourceInput.Fn := {source with body :=
  [.ret (2,16) (.app (3,16)
    (.lam (3,12) "unit" (primitive "null") (primitive "boolean")
      (.app (7,12) (.var (7,8) "f") (.lit (9,10) (.vbool true))))
    (.lit (14,15) .vnull))]}
#guard !ok (check wrongArgument {claims with exprs := claims.exprs.map fun (pos,c) =>
  if pos == (9,10) then (pos,.ok [1]) else (pos,c)})
-- Saving both operands explicitly keeps source name lookup and evaluation
-- order correct after adding the anonymous callee slot.
#guard match extractNormalizedFn table source claims with
  | .error _ => false
  | .ok r => r.obligations.any fun q => q.pos == (7,12) &&
      q.sequent.term == .letE (.var 1) (.letE (.var 1) (.app (.var 1) (.var 0)))

-- One successful alternative does not excuse another incompatible domain.
private def mixedDomain : Json := Json.mkObj [("top",toJson false),("atoms",toJson
  [arrow (primitive "null") (literal true),arrow (primitive "boolean") (literal false)])]
#guard (extractNormalizedFn (table.set 5 [.arrs [([1,2],[2])]])
  {source with params := [⟨"f",mixedDomain⟩]} claims).toOption.isSome
#guard !ok (checkWith (table.set 5 [.arrs [([1,2],[2])]])
  {source with params := [⟨"f",mixedDomain⟩]} claims)

-- A source-level nullable function remains gated until a guard establishes
-- callability; it cannot borrow the callable union branch's signature.
private def nullable : Json := Json.mkObj [("top",toJson false),("atoms",toJson
  [Json.mkObj [("a",toJson "null")],arrow (primitive "null") (literal true)])]
#guard !ok (check {source with params := [⟨"f",nullable⟩]}
  {claims with
    params := [("f",.ok [0,4])]
    envs := [(2,[("f",.ok [0,4])])]
    exprs := claims.exprs.map fun (pos,c) => if pos == (7,8) then (pos,.ok [0,4]) else (pos,c)})

-- Null guards preserve both callable alternatives. Exercise both comparison
-- polarities and operand orders through closure lowering and the full consumer.
private def guardedType : Json := Json.mkObj [("top",toJson false),("atoms",toJson
  [Json.mkObj [("a",toJson "null")],
   arrow (primitive "null") (literal true),arrow (primitive "null") (literal false)])]
private def guarded (equal testLeft wrongBranch : Bool) : SourceInput.Fn :=
  let left := if testLeft then SourceInput.Expr.var (11,12) "f" else .lit (11,12) .vnull
  let right := if testLeft then SourceInput.Expr.lit (16,17) .vnull else .var (16,17) "f"
  let cond := SourceInput.Expr.unitTest (10,18) .isNul equal testLeft left right
  let call := SourceInput.Expr.app (30,38) (.var (30,31) "f") (.var (34,35) "unit")
  let fallback := SourceInput.Expr.lit (20,21) (.vbool false)
  let callOnYes := equal == wrongBranch
  ⟨"guarded",(0,1),[⟨"f",guardedType⟩],primitive "boolean",
   [.ret (2,50) (.app (3,50)
     (.lam (3,47) "unit" (primitive "null") (primitive "boolean")
       (.ifBody (8,46) none cond
         (if callOnYes then call else fallback) (if callOnYes then fallback else call)))
     (.lit (48,49) .vnull))]⟩
private def guardedClaims (testLeft : Bool) : SourceClaims.Function :=
  ⟨"guarded",(0,1),[("f",.ok [0,4,5])],.ok [1,2],
   [(2,[("f",.ok [0,4,5])])],
   [((3,50),.ok [1,2]),((3,47),.ok [6]),((8,46),.ok [1,2]),
    ((10,18),.ok [1,2]),((11,12),.ok (if testLeft then [0,4,5] else [0])),
    ((16,17),.ok (if testLeft then [0] else [0,4,5])),
    ((20,21),.ok [2]),((30,38),.ok [1,2]),((30,31),.ok [4,5]),
    ((34,35),.ok [0]),((48,49),.ok [0])],[],[]⟩
#guard [false,true].all fun equal => [false,true].all fun testLeft =>
  ok (check (guarded equal testLeft false) (guardedClaims testLeft))
-- A callee claim cannot move the call to the null branch or discard a possible
-- return value after the guard has established only non-nullness.
#guard [false,true].all fun equal => [false,true].all fun testLeft =>
  (extractNormalizedFn table (guarded equal testLeft true) (guardedClaims testLeft)).toOption.isSome &&
  !ok (check (guarded equal testLeft true) (guardedClaims testLeft))
#guard !ok (check (guarded true true false)
  {(guardedClaims true) with exprs := (guardedClaims true).exprs.map fun (pos,c) =>
    if pos == (30,38) then (pos,.ok [1]) else (pos,c)})
end Verification.ExperimentState.SourceCallableUnionTests
