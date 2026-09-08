import Verification.ExperimentState.SourceExtraction

/-! Audit actual exported witnesses, not hand-built copies of their graphs.
Every expression and ordinary edge must check. Exactly one heap edge may fail,
and it must enter the source return immediately after the invalidating action.
Run by refinement-witnesses.js against the fresh raw exports. -/
open Lean Verification.ExperimentState
open SourceExtraction CertificateProducer RequestJson ControlFlow

private def require (p : Bool) (message : String) : Except String Unit :=
  if p then pure () else throw message

private def audit (ast claims : Json) (file : String) : Except String (List String) := do
  let fs ← SourceInput.decodeAst ast
  let rs ← extract ast claims file
  (fs.zip rs).mapM fun pair => do
    let f : SourceInput.Fn := pair.1
    let r : SourceRequest := pair.2
    let arm : List SourceInput.Stmt ← match f.body[2]?, f.body[1]? with
      | some (SourceInput.Stmt.ite _ _ thn _), _ => pure thn
      | _, some (SourceInput.Stmt.loop _ _ body) => pure body
      | _, _ => throw "unexpected witness structure"
    let some (.ret pos (.read ..)) := arm.getLast?
      | throw "expected stale cell read as the guarded return"
    let G := graph r.toRequest
    let es ← ExpressionClaims.produce G r.searchLabels r.types.length 10 r.obligations
    let C ← (produceRaw G (vocabulary G r.searchLabels r.claims r.inputs) 10
      r.program r.claims [] es r.start r.assertions).mapError reprStr
    let response := Response.mk 4 C
    require (validRequest r.toRequest && validResponse r.toRequest response &&
      decide (C.map signature = r.claims) && checkAssertions r response)
      s!"{f.name}: request or supplied-claim mismatch"
    let some initial := C[r.start]? | throw "missing entry"
    require (decide (entry initial = r.inputs ∧ initial.knowledge = ⟨[],[],[]⟩))
      s!"{f.name}: external entry mismatch"
    -- Suppress only destination heap requirements to inspect ordinary obligations.
    -- Each expression still uses its actual input knowledge and checked effect.
    let destinations := C.map fun c => {c with knowledge := ⟨[],[],[]⟩}
    let mut failures : List Nat := []
    for (node,l) in r.program.zipIdx do
      let some c := C[l]? | throw "missing certificate node"
      require (checkNode G r.result r.program destinations node c)
        s!"{f.name}: ordinary expression/edge failure at {l}"
      for (target,index) in (successors node.continuation).zipIdx do
        let some dest := C[target.label]? | throw "missing target node"
        let facts := edgeKnowledge c.output node.continuation index
        if !HeapKnowledge.check facts dest.knowledge target.mapping then
          failures := target.label :: failures
    let [failed] := failures | throw s!"{f.name}: expected exactly one failing heap edge, got {failures.length}"
    let some origin := (r.origins[failed]?).join | throw "unlocated heap edge"
    require (origin.environmentStart == some pos.1 && origin.role == "heap-observation")
      s!"{f.name}: failed before reaching the post-mutation return"
    require (!(accept G r.result r.program r.claims C r.start r.inputs))
      s!"{f.name}: consumer accepted the bad graph"
    return s!"  {f.name}: every ordinary obligation and all earlier heap edges check; only the post-mutation assertion fails"

def main (args : List String) : IO UInt32 := do
  let [ap,cp,file] := args | IO.eprintln "expected ast, claims, file"; return 1
  let a ← IO.FS.readFile ap
  let c ← IO.FS.readFile cp
  let result : Except String (List String) := do
    audit (← Json.parse a) (← Json.parse c) file
  match result with
  | .error e => IO.eprintln e; return 1
  | .ok lines =>
    for line in lines do IO.println line
    return 0
