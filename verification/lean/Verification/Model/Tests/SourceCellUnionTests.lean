import Verification.Model.Source.SourceClaimJson

/-! Cells holding a union of records, captured by closures, on the pipeline's
own documents: `SourceExtraction/cell-union-capture.*.json` are the parser's
fragment and the OCaml producer's claims for
`ocaml-producer/examples/cell-union-capture.ts`, whose pipeline case verifies
them. The producer states no contents observation at these points; the
observations below are added to its claims, and extraction must attach each
to its point and obligation. -/
namespace Verification.Model.SourceCellUnionTests
open Lean SourceExtraction ProgramTyping

private def file : String := "verification/ocaml-producer/examples/cell-union-capture.ts"
private def ast : Json :=
  (Json.parse (include_str "SourceExtraction/cell-union-capture.fragment.json")).toOption.getD .null
private def claims : Json :=
  (Json.parse (include_str "SourceExtraction/cell-union-capture.claims.json")).toOption.getD .null

private def ok (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

private def withFunction (name : String) (f : Json → Json) (c : Json) : Json :=
  match c.getObjValD "functions" with
  | .arr fs => c.setObjVal! "functions" (.arr (fs.map fun g =>
      if g.getObjValD "name" == Json.str name then f g else g))
  | _ => c
private def mapEach (key : String) (f : Json → Json) (j : Json) : Json :=
  match j.getObjValD key with
  | .arr xs => j.setObjVal! key (.arr (xs.map f))
  | _ => j
/-- The contents observation `value: labels`. -/
private def observing (labels : List Nat) (j : Json) : Json :=
  j.setObjVal! "current" (Json.arr #[toJson [toJson "value", toJson labels]])
/-- The expression at `pos` observes `value: labels`. -/
private def observedAt (fn : String) (pos : List Nat) (labels : List Nat) : Json :=
  withFunction fn (mapEach "expressions" fun e =>
    if e.getObjValD "pos" == toJson pos then observing labels e else e) claims
/-- At the statement entry `start`, the binding `cell` observes `value: labels`,
and has type `cellType`. -/
private def enteredAt (fn : String) (start : Nat) (labels : List Nat) (cellType : List Nat := [4, 5]) : Json :=
  withFunction fn (mapEach "entries" fun e =>
    if e.getObjValD "start" == toJson start then
      mapEach "bindings" (fun b => if b.getObjValD "name" == Json.str "cell" then
        observing labels (b.setObjVal! "type" (toJson cellType)) else b) e
    else e) claims

/-- Refused, for the reason named. -/
private def refuses (r : Except String α) (reason : String) : Bool := match r with
  | .ok _ => false
  | .error e => (e.splitOn reason).length > 1

-- The read's graph code: the captured cell bound, its field read from the
-- bound slot, then returned.
#guard match SourceClaimJson.extractGraphRequests ast claims file with
  | .ok (r :: _) => r.codes.any fun q =>
      q.entry.exprs == [.var 0, .readAt (.str "value") (.var 0), .var 2]
  | _ => false

-- An observation every arm's invariant implies survives capture, with an
-- obligation located at the read of the captured cell. The allocation's
-- initial null cannot justify a null-only observation: one arm admits later
-- Boolean writes.
private def observed : Json := observedAt "readLater" [520, 524] [0, 1, 2]
#guard ok (SourceClaimJson.produceJson ast observed file 10)
#guard match SourceClaimJson.extractGraphRequests ast observed file with
  | .ok (r :: _) => r.obligations.any fun q => q.pos == (520, 524) &&
      q.role == "heap-observation" && q.sequent.term == .var 0 &&
      q.context.map (·.2) == [some (520, 524)]
  | _ => false
#guard refuses (SourceClaimJson.produceJson ast (observedAt "readLater" [520, 524] [0]) file 10)
  "source incoming edge obligation at [520,524)"

-- Removing the observation's evidence invalidates an otherwise valid bundle.
private def observedEvidence : Json := (SourceClaimJson.produceJson ast observed file 10).toOption.getD .null
private def withoutObservations : Json :=
  match SourceClaimJson.extractGraphRequests ast observed file, observedEvidence.getObjValD "obligations" with
  | .ok (r :: _), .arr os => match os.toList with
    | .arr es :: rest =>
      let keep := (r.obligations.zip es.toList).filterMap fun (q, e) =>
        if q.role == "heap-observation" then none else some e
      observedEvidence.setObjVal! "obligations" (.arr (.arr keep.toArray :: rest).toArray)
    | _ => .null
  | _, _ => .null
#guard refuses (SourceClaimJson.checkJson ast observed file withoutObservations)
  "source evidence does not justify"

-- A statement entry's null-only observation holds after the closure writes
-- the parameter's null into the cell, and not where nothing wrote it; one
-- every arm implies holds anywhere.
#guard ok (SourceClaimJson.produceJson ast (enteredAt "writeThenRead" 1014 [0]) file 10)
#guard refuses (SourceClaimJson.produceJson ast (enteredAt "readBlock" 739 [0]) file 10)
  "source incoming edge obligation at [739,757)"
-- An entry environment narrowed to the null-only arm cannot erase the
-- Boolean-capable one, though its contents observation holds.
#guard refuses (SourceClaimJson.produceJson ast (enteredAt "writeThenRead" 1014 [0] [4]) file 10)
  "source incoming edge obligation at [1021,1025)"

end Verification.Model.SourceCellUnionTests
