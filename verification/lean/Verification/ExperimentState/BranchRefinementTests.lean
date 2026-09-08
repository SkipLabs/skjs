import Verification.ExperimentState.SourceTypes

namespace Verification.ExperimentState.BranchRefinementTests
open Lean ProgramTyping ControlFlow RequestJson BranchRefinement

private def ok (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false

-- Slot zero is justified by the branch observation. Slot one is not refined.
#guard checkRefined SourceTypes.graph [[1,2],[1,2]] [[1],[1,2]] 0 true
  (some [0,1]) [.subset,.subset]
#guard !checkRefined SourceTypes.graph [[1,2],[1,2]] [[2],[1,2]] 0 true
  (some [0,1]) [.subset,.subset]
#guard !checkRefined SourceTypes.graph [[1,2],[1,2]] [[1],[1]] 0 true
  (some [0,1]) [.subset,.subset]
#guard !checkRefined SourceTypes.graph [[1,2],[1,2]] [[1],[1,2]] 0 true
  (some [1,0]) [.subset,.subset]
#guard !checkRefined SourceTypes.graph [[1,2]] [[1]] 0 true (some [9]) [.subset]
#guard !checkRefined SourceTypes.graph [[1,2]] [[1]] 0 true (some [0]) []
#guard !checkRefined SourceTypes.graph [[1,2]] [[1]] 0 true (some [0,0]) [.subset]

private def request (v : Tm) : Request :=
  ⟨2, SourceTypes.types,
    [⟨v,.bind 1⟩, ⟨.var 0,.branchBind ⟨2,some [0,1]⟩ ⟨3,some [0,1]⟩⟩,
     ⟨.var 0,.ret⟩, ⟨.var 0,.ret⟩],
    [⟨[],[1,2]⟩,⟨[[1,2]],[1,2]⟩,⟨[[1],[1,2]],[1,2]⟩,⟨[[2],[1,2]],[1,2]⟩],
    [1,2],0,[]⟩

private def roundtrip (r : Request) : Except String Unit := do
  let input ← Json.parse (toJson r).compress
  let evidence ← RequestJson.produceJson input 8
  verifyJson input (← Json.parse evidence.compress)

#guard ok (roundtrip (request .tru))
#guard ok (roundtrip (request .fls))
#guard !ok (roundtrip { request .tru with program := ((request .tru).program.set 1
  ⟨.var 0,.branchBind ⟨3,some [0,1]⟩ ⟨2,some [0,1]⟩⟩) })
#guard !ok (roundtrip { request .tru with claims := (request .tru).claims.set 3 ⟨[[1],[1,2]],[1,2]⟩ })
#guard !ok (roundtrip { request .tru with claims := (request .tru).claims.set 2 ⟨[[1],[1]],[1,2]⟩ })
#guard !ok (roundtrip { request .tru with program := ((request .tru).program.set 1
  ⟨.var 0,.branchBind ⟨2,some [1,0]⟩ ⟨3,some [0,1]⟩⟩) })
#guard !ok (roundtrip { request .tru with program := ((request .tru).program.set 1
  ⟨.var 0,.branchBind ⟨2,some [0,1]⟩ 99⟩) })
-- A possibly-null result is not accepted as a Boolean dispatch, even when this
-- particular source expression happens to evaluate to true.
#guard !ok (roundtrip { request .tru with claims := (request .tru).claims.set 1 ⟨[[1,2]],[0,1,2]⟩ })
-- Refining transfers also participate in cycles; checking requires no iteration.
#guard ok (roundtrip ⟨2,SourceTypes.types,
  [⟨.tru,.bind 1⟩,⟨.var 0,.branchBind ⟨1,some [0]⟩ ⟨2,some [0]⟩⟩,⟨.var 0,.ret⟩],
  [⟨[],[1,2]⟩,⟨[[1,2]],[1,2]⟩,⟨[[2]],[1,2]⟩],[1,2],0,[]⟩)
end Verification.ExperimentState.BranchRefinementTests
