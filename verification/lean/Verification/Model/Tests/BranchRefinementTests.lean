import Verification.Model.Source.SourceTypes

namespace Verification.Model.BranchRefinementTests
open Lean ProgramTyping ControlFlow RequestJson BranchRefinement

-- `key in o` reads the prototype chain: a class instance holds its
-- prototype, whose method it lacks as an own key, and `in` finds it there.
private def protoHeap : List Tm := [.objAt [("m", 1)] .absent, .num 0, .num 1]
private def instanceWithProto : Tm := .objAt [("x", 2), ("[[proto]]", 0)] .absent
#guard tagHoldsIn protoHeap (.hasKey "m") instanceWithProto

end Verification.Model.BranchRefinementTests
