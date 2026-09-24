import Verification.Model.Source.RequestJson

namespace Verification.Model.StringEqualityTests
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules BranchRefinement

-- A string equality tag holds exactly on that string; on anything else it is
-- false, including numbers and the other kinds of value.
#guard tagHolds (.strEq "a") (.str "a") == true
#guard tagHolds (.strEq "a") (.str "b") == false
#guard tagHolds (.strEq "a") (.num 0) == false
#guard tagHolds (.strEq "a") .nul == false
#guard tagHolds .isStr (.str "") == true
#guard tagHolds .isStr .undef == false

private def G : NormalGraph Nat := .ofRows fun i =>
  if i == 0 then [.strLit "a"] else if i == 1 then [.strLit "b"]
  else if i == 2 then [.str] else [.nul]
#guard tagSlice G [0,1,3] (.strEq "a") true == [0]
#guard tagSlice G [0,1,3] (.strEq "a") false == [1,3]
-- Unknown does not mean false: the string family remains on either branch.
#guard tagSlice G [2] (.strEq "a") true == [2]
#guard tagSlice G [2] (.strEq "a") false == [2]
#guard !(decide (Answers G [2] (.strEq "a") true))
#guard !(decide (Answers G [2] (.strEq "a") false))
#guard decide (Answers G [0] (.strEq "a") true)
#guard decide (Answers G [1] (.strEq "a") false)

-- A broad string observation cannot disappear from either equality edge.
private def observed : HeapKnowledge.Knowledge := ⟨[],[⟨0,[.str,.nul],valueField⟩],[]⟩
#guard (HeapKnowledge.observeTag observed 0 (.strEq "a") true).values.head?.map (·.contents) == some [.str]
#guard (HeapKnowledge.observeTag observed 0 (.strEq "a") false).values.head?.map (·.contents) == some [.str,.nul]
#guard (HeapKnowledge.observeTag observed 0 .isNul false).values.head?.map (·.contents) == some [.str]

end Verification.Model.StringEqualityTests
