import Verification.ExperimentState.RequestJson

namespace Verification.ExperimentState.NumericEqualityTests
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules BranchRefinement

-- IEEE encodings: both zero signs compare equal, every NaN compares unequal,
-- infinities compare by sign, and distinct finite doubles stay distinct.
#guard numberEqual 0 0x8000000000000000
#guard numberEqual 0x8000000000000000 0
#guard !(numberEqual 0x7ff8000000000000 0x7ff8000000000000)
#guard !(numberEqual 0x7ff0000000000001 0)
#guard !(numberEqual 0 0xfff8000000000000)
#guard numberEqual 0x7ff0000000000000 0x7ff0000000000000
#guard !(numberEqual 0x7ff0000000000000 0xfff0000000000000)
#guard !(numberEqual 0x3ff0000000000000 0x3ff0000000000001)

private def G : NormalGraph Nat := fun i =>
  if i == 0 then [.numLit 0] else if i == 1 then [.numLit 0x3ff0000000000000]
  else if i == 2 then [.num] else [.numLit 0x8000000000000000]
#guard tagSlice G [0,1,3] (.numEq 0) true == [0,3]
#guard tagSlice G [0,1,3] (.numEq 0) false == [1]
-- Unknown does not mean false: the number family remains on either branch.
#guard tagSlice G [2] (.numEq 0) true == [2]
#guard tagSlice G [2] (.numEq 0) false == [2]
#guard !(decide (Answers G [2] (.numEq 0) true))
#guard !(decide (Answers G [2] (.numEq 0) false))
#guard tagHolds (.numEq 0) .nul == false

end Verification.ExperimentState.NumericEqualityTests
