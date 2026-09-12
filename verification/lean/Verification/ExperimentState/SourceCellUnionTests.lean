import Verification.ExperimentState.SourceExtraction

namespace Verification.ExperimentState.SourceCellUnionTests
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
  [[.refs [0,1,2] []],[.refs [0] []],[.arrs [([0],[0,1,2])]]]
private def read : SourceInput.Expr := .read (24,27) (.var (24,25) "cell")
private def write : SourceInput.Expr := .write (12,20) (.var (12,13) "cell") (.var (19,20) "unit")
private def withBody (body : SourceInput.Expr) : SourceInput.Fn :=
  ⟨"cells",(0,1),[],result,
   [.cst (2,3) "cell" (some union) (.alloc (4,7) (.lit (5,6) .vnull)),
    .ret (8,30) (.app (9,30)
      (.lam (9,27) "unit" null result body)
      (.lit (29,30) .vnull))]⟩
private def source (mutate : Bool) : SourceInput.Fn :=
  withBody (if mutate then .seqBody (12,27) write read else read)
private def claims : SourceClaims.Function :=
  ⟨"cells",(0,1),[],.ok [0,1,2],[(2,[]),(8,[("cell",.ok [4,5])])],
   [((4,7),.ok [4]),((5,6),.ok [0]),((9,30),.ok [0,1,2]),((9,27),.ok [6]),
    ((12,20),.ok [0]),((12,13),.ok [4,5]),((19,20),.ok [0]),
    ((24,27),.ok [0,1,2]),((24,25),.ok [4,5]),((29,30),.ok [0])],[],[]⟩

-- Both alternatives are locally allocated invariant cells. Closure recipes
-- eliminate the saved receiver's union while retaining all operand checks.
#guard ((SourceInput.translate union).run' SourceTypes.initial).toOption == some [4,5]
#guard [false,true].all fun mutate => (extractNormalizedFn table (source mutate) claims).toOption.isSome

private def check (f : SourceInput.Fn) (c : SourceClaims.Function) : Except String Unit := do
  let r ← extractNormalizedFn table f c
  let proofs ← ExpressionClaims.produce (RequestJson.graph r.toRequest)
    r.searchLabels r.types.length 0 r.obligations
  let j ← RequestJson.produceJson (toJson r.toRequest) 10 [] proofs
    r.sourceMap (some r.searchLabels) r.assertions r.cuts
  let response ← RequestJson.decodeResponse r.toRequest j
  if !checkRequests [r] ⟨[response],[proofs]⟩ then throw "source consumer rejected evidence"
private def ok (x : Except String α) : Bool := match x with | .ok _ => true | .error _ => false
#guard [false,true].all fun mutate => ok (check (source mutate) claims)
-- Possible read contents must not be narrowed to null by a supplied claim.
#guard !ok (check (source false) {claims with exprs := claims.exprs.map fun (pos,c) =>
  if pos == (24,27) then (pos,.ok [0]) else (pos,c)})
-- The source parameter boundary must still reject externally supplied cells.
#guard match extractNormalizedFn table {(source false) with params := [⟨"external",union⟩]}
    {claims with params := [("external",.ok [4,5])]} with
  | .error e => e == "cell parameters need an external-value boundary, which is outside the source slice"
  | .ok _ => false
-- A Boolean write fits the first cell but not the null-only alternative.
-- Extraction succeeds; its independently checked write obligation must fail.
private def wrongWrite := withBody (.seqBody (12,27)
  (.write (12,20) (.var (12,13) "cell") (.lit (19,20) (.vbool true))) read)
private def wrongClaims : SourceClaims.Function := {claims with
  exprs := claims.exprs.map fun (pos,c) =>
    if pos == (12,20) || pos == (19,20) then (pos,.ok [1]) else (pos,c)}
#guard (extractNormalizedFn table wrongWrite wrongClaims).toOption.isSome
#guard !ok (check wrongWrite wrongClaims)

-- The anonymous receiver slot shifts the named RHS parameter correctly. The
-- assignment evaluates each operand once and returns its saved RHS value.
#guard match extractNormalizedFn table (source true) claims with
  | .error _ => false
  | .ok r => r.obligations.any fun q => q.pos == (12,20) &&
      q.sequent.term == .letE (.var 1) (.letE (.var 1)
        (.letE (.write (.var 1) (.var 0)) (.var 1)))
#guard match extractNormalizedFn table (source false) claims with
  | .error _ => false
  | .ok r => r.obligations.any fun q => q.pos == (24,27) &&
      q.sequent.term == .letE (.var 1) (.read (.var 0))
end Verification.ExperimentState.SourceCellUnionTests
