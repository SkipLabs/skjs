import Verification.Model.Source.SourceClaimJson

/-! A union of functions captured by a closure and called there, on the
pipeline's own documents: `SourceExtraction/callable-union-capture.*.json`
are the parser's fragment and the OCaml producer's claims for
`ocaml-producer/examples/callable-union-capture.ts`, whose pipeline case
verifies them. -/
namespace Verification.Model.SourceCallableUnionTests
open Lean SourceExtraction ProgramTyping

private def file : String := "verification/ocaml-producer/examples/callable-union-capture.ts"
private def ast : Json :=
  (Json.parse (include_str "SourceExtraction/callable-union-capture.fragment.json")).toOption.getD .null
private def claims : Json :=
  (Json.parse (include_str "SourceExtraction/callable-union-capture.claims.json")).toOption.getD .null

-- Saving both operands keeps name lookup and evaluation order past the
-- anonymous callee slot. Inside the closure, slot 0 is its receiver, slot 1
-- its parameter and the captured `f` slot 2: the closure's graph code binds
-- the captured `f`, then the parameter, then calls the saved callee on the
-- saved actual.
#guard match SourceClaimJson.extractGraphRequests ast claims file with
  | .ok (r :: _) => r.codes.any fun q =>
      q.entry.exprs == [.var 0, .invoke (.var 1) .undef [.var 0], .var 2, .var 2]
  | _ => false

-- The union's result is not narrowed to one alternative's: a claim that the
-- call returns `true` is refused.
private def narrowed : Json :=
  match claims.getObjValD "functions" with
  | .arr fs => claims.setObjVal! "functions" (.arr (fs.map fun f =>
      match f.getObjValD "expressions" with
      | .arr es => f.setObjVal! "expressions" (.arr (es.map fun e =>
          if e.getObjValD "pos" == toJson [312, 319] then e.setObjVal! "type" (toJson [1]) else e))
      | _ => f))
  | _ => claims
#guard match SourceClaimJson.produceJson ast narrowed file 10 with
  | .ok _ => false
  | .error e => (e.splitOn "at [312,319)").length > 1

end Verification.Model.SourceCallableUnionTests
