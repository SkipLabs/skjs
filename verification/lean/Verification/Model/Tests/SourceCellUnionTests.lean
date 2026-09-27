import Verification.Model.Source.SourceExtraction

namespace Verification.Model.SourceCellUnionTests
open Lean SourceExtraction ProgramTyping

private def null : Json := Json.mkObj [("top",toJson false),
  ("atoms",toJson [Json.mkObj [("a",toJson "null")]])]
private def result : Json := Json.mkObj [("top",toJson false),
  ("atoms",toJson [Json.mkObj [("a",toJson "null")],Json.mkObj [("a",toJson "boolean")]])]
private def record (T : Json) : Json := Json.mkObj
  [("a",toJson "record"),("fields",toJson [Json.mkObj [("name",toJson "value"),
    ("optional",toJson false),("read",T),("write",T)]]),
   ("indexes",Json.mkObj [("string",toJson "absent"),("number",toJson "absent"),("symbol",toJson "absent")]),
   ("call",toJson "unknown"),("construct",toJson "unknown"),("array",toJson "unknown")]
private def union : Json := Json.mkObj [("top",toJson false),("atoms",toJson [record result,record null])]
private def table : SourceTypes.Table := SourceTypes.initial ++
  RequestJson.rows [[.refs [("value", [0,1,2])] [] []],[.refs [("value", [0])] [] []],[.arrs [⟨[7], [[0]], [0,1,2], .unrestricted⟩] []],
   [.top]]
private def read : Fragment.Expr := .read (24,27) "value" (.var (24,25) "cell")
private def write : Fragment.Expr := .write (12,20) "value" (.var (12,13) "cell") (.var (19,20) "unit")
private def withBody (body : Fragment.Expr) : Fragment.Fn :=
  ⟨"cells",(0,1),[],result,
   [.cst (2,3) "cell" (some union) (.alloc (4,7) ["value"] [(.lit (5,6) .vnull)]),
    .ret (8,30) (.app (9,30)
      (.lam (9,27) "unit" null result body)
      (.lit (29,30) .vnull))]⟩
private def source (mutate : Bool) : Fragment.Fn :=
  withBody (if mutate then .comma (12,27) write read else read)
private def claims : SourceClaims.Function :=
  ⟨"cells",(0,1),[],.ok [0,1,2],[(2,[]),(8,[("cell",.ok [4,5])])],
   [((4,7),.ok [4]),((5,6),.ok [0]),((9,30),.ok [0,1,2]),((9,27),.ok [6]),((12,27),.ok [0,1,2]),
    ((12,20),.ok [0]),((12,13),.ok [4,5]),((19,20),.ok [0]),
    ((24,27),.ok [0,1,2]),((24,25),.ok [4,5]),((29,30),.ok [0])],[],[],[]⟩

-- Both alternatives are locally allocated invariant cells. Closure recipes
-- eliminate the saved receiver's union while retaining all operand checks.
#guard ((Fragment.translate union).run' SourceTypes.initial).toOption == some [4,5]
#guard [false,true].all fun mutate => (extractNormalizedFn table (source mutate) claims).toOption.isSome

private def check (f : Fragment.Fn) (c : SourceClaims.Function) : Except String Unit := do
  let r ← extractNormalizedFn table f c
  let proofs ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  let j ← RequestJson.produceJson (toJson r.toRequest) 10 [] proofs
    r.sourceMap (some r.searchLabels) r.assertions r.cuts r.codeHints
  let response ← RequestJson.decodeResponse r.toRequest j
  if !checkRequests [r] ⟨[response],[proofs]⟩ then throw "source consumer rejected evidence"
  -- Removing observation evidence must invalidate an otherwise valid bundle.
  if r.obligations.any (·.role == "heap-observation") then
    let omitted := (r.obligations.zip proofs).filterMap fun (q,e) =>
      if q.role == "heap-observation" then none else some e
    if checkRequests [r] ⟨[response],[omitted]⟩ then
      throw "source consumer ignored missing observation evidence"
private def ok (x : Except String α) : Bool := match x with | .ok _ => true | .error _ => false
#guard [false,true].all fun mutate => ok (check (source mutate) claims)
-- An observation implied by every invariant survives capture, with a located
-- obligation over the union of possible stored values.
private def observed (R : Ty Nat) : SourceClaims.Function :=
  {claims with exprCurrent := [((24,25),[("value",R)])]}
#guard [false,true].all fun mutate =>
  ok (check (source mutate) (observed [0,1,2]))
#guard match extractNormalizedFn table (source false) (observed [0,1,2]) with
  | .error _ => false
  | .ok r => r.obligations.any fun q => q.pos == (24,25) &&
      q.role == "heap-observation" && q.sequent.context == [[0,1,2]] &&
      q.sequent.term == .var 0 && q.sequent.type == [0,1,2] &&
      q.context == [⟨"",some (24,25)⟩]
-- The allocation's initial null value cannot justify a persistent null-only
-- observation: one alternative permits later Boolean writes.
#guard !ok (check (source false) (observed [0]))
#guard (extractNormalizedFn table (source false) (observed [0])).toOption.isSome
-- Possible read contents must not be narrowed to null by a supplied claim.
#guard !ok (check (source false) {claims with exprs := claims.exprs.map fun (pos,c) =>
  if pos == (24,27) then (pos,.ok [0]) else (pos,c)})
-- An externally supplied cell union is admitted at its annotation.
#guard match extractNormalizedFn table {(source false) with params := [⟨"external",union,false⟩]}
    {claims with params := [("external",.ok [4,5])]
                 envs := claims.envs.map fun pv => (pv.1,("external",Except.ok [4,5]) :: pv.2)} with
  | .ok _ => true
  | .error _ => false
-- A Boolean write fits the first cell but not the null-only alternative.
-- Extraction succeeds; its independently checked write obligation must fail.
private def wrongWrite := withBody (.comma (12,27)
  (.write (12,20) "value" (.var (12,13) "cell") (.lit (19,20) (.vbool true))) read)
private def wrongClaims : SourceClaims.Function := {claims with
  exprs := claims.exprs.map fun (pos,c) =>
    if pos == (12,20) || pos == (19,20) then (pos,.ok [1]) else (pos,c)}
#guard (extractNormalizedFn table wrongWrite wrongClaims).toOption.isSome
#guard !ok (check wrongWrite wrongClaims)

-- The read's graph code: the captured cell (slot 2), bound, then its field
-- read from the bound slot, then returned; the capture at the cell union.
#guard match extractNormalizedFn table (source false) claims with
  | .error _ => false
  | .ok r => r.codes.any fun (q : RequestJson.CodeRequest) =>
      q.entry.exprs == [.var 0, .readAt valueField (.var 0), .var 2] && q.entry.captures == [[4,5]]

-- Statement-entry observations name the captured binding. Nested closures and
-- preceding expression statements add parameter and anonymous evaluation slots;
-- projecting the named environment must preserve both kinds of slot.
private def entrySource (mutate nested : Bool) : Fragment.Fn :=
  let body := Fragment.Expr.block (23,28) [.ret (23,28) read]
  let returned := if nested then
    Fragment.Expr.app (14,28)
      (.lam (15,28) "inner" null result body) (.lit (21,22) .vnull)
    else read
  withBody (if mutate then .block (12,28) [.effect (12,20) write,
      if nested then .ret (14,28) returned else .ret (23,28) returned]
    else if nested then returned else body)
private def entryClaims (nested : Bool) (R : Ty Nat) : SourceClaims.Function :=
  {claims with
    envs := claims.envs ++ [(23,
      (if nested then [("inner",.ok [0])] else []) ++
      [("unit",.ok [0]),("cell",.ok [4,5])]),
      (12,[("unit",.ok [0]),("cell",.ok [4,5])]),
      (14,[("unit",.ok [0]),("cell",.ok [4,5])])]
    exprs := claims.exprs ++ [((14,28),.ok [0,1,2]),((15,28),.ok [6]),((21,22),.ok [0])]
    entryCurrent := [(23,[("cell",[("value",R)])])]}
#guard [false,true].all fun mutate => [false,true].all fun nested =>
  ok (check (entrySource mutate nested) (entryClaims nested [0,1,2]))
-- A null-only observation holds after the closure writes the parameter's null
-- into the cell, and nowhere a closure's entry, which knows nothing of the
-- heap, reaches it.
#guard [false,true].all fun mutate => [false,true].all fun nested =>
  (extractNormalizedFn table (entrySource mutate nested) (entryClaims nested [0])).toOption.isSome &&
  ok (check (entrySource mutate nested) (entryClaims nested [0])) == (mutate && !nested)
-- The program this pins was the term-closure lowering's; closures are graph code now,
-- and the pipeline cases check what the lowering produces.
-- A false entry environment cannot erase the Boolean-capable alternative,
-- even when its separate contents observation is valid for the narrowed type.
private def narrowedEntry : SourceClaims.Function :=
  let c := entryClaims true [0]
  {c with envs := c.envs.map fun (pos,env) =>
    (pos, if pos == 23 then env.map (fun (name,A) =>
      (name,if name == "cell" then .ok [5] else A)) else env)}
#guard (extractNormalizedFn table (entrySource true true) narrowedEntry).toOption.isSome
#guard !ok (check (entrySource true true) narrowedEntry)
#guard match extractNormalizedFn table (entrySource true true) narrowedEntry with
  | .error _ => false
  | .ok r =>
    let proveRole := fun role => ExpressionClaims.produce (RequestJson.graph r.toRequest)
      r.searchLabels r.types.length 0 (r.obligations.filter (·.role == role))
    (proveRole "heap-observation").toOption.isSome
end Verification.Model.SourceCellUnionTests
