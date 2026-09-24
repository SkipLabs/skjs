import Verification.Model.Source.SourceClaimJson

namespace Verification.Model.LoopTransferTests
open Lean ProgramTyping SourceExtraction SourceClaimJson ControlFlow
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"nestedBreak\",\"namePos\":[598,609],\"typeParams\":[],\"params\":[{\"name\":\"flag\",\"pos\":[610,614],\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]}}],\"retType\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":[{\"k\":\"while\",\"pos\":[638,746],\"cond\":{\"k\":\"id\",\"pos\":[645,649],\"name\":\"flag\"},\"body\":[{\"k\":\"while\",\"pos\":[657,725],\"cond\":{\"k\":\"id\",\"pos\":[664,668],\"name\":\"flag\"},\"body\":[{\"k\":\"const\",\"pos\":[678,706],\"bindings\":[{\"name\":\"local\",\"namePos\":[684,689],\"annot\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[701,705],\"name\":\"flag\"}}]},{\"k\":\"break\",\"pos\":[713,719]}]},{\"k\":\"return\",\"pos\":[730,742],\"e\":{\"k\":\"lit\",\"pos\":[737,741],\"lit\":{\"a\":\"booleanlit\",\"v\":\"true\"}}}]},{\"k\":\"return\",\"pos\":[749,762],\"e\":{\"k\":\"lit\",\"pos\":[756,761],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"functions\":[{\"entries\":[{\"bindings\":[{\"name\":\"flag\",\"type\":[1,2],\"current\":null}],\"start\":638},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null}],\"start\":657},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null}],\"start\":678},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null},{\"name\":\"local\",\"type\":[1,2],\"current\":null}],\"start\":713},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null}],\"start\":730},{\"bindings\":[{\"name\":\"flag\",\"type\":[1,2],\"current\":null}],\"start\":749}],\"expressions\":[{\"pos\":[645,649],\"type\":[1,2],\"current\":null},{\"pos\":[664,668],\"type\":[1],\"current\":null},{\"pos\":[701,705],\"type\":[1],\"current\":null},{\"pos\":[737,741],\"type\":[1],\"current\":null},{\"pos\":[756,761],\"type\":[2],\"current\":null}],\"name\":\"nestedBreak\",\"namePos\":[598,609],\"params\":[{\"name\":\"flag\",\"type\":[1,2],\"current\":null}],\"result\":[1,2]}],\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[{\"refs\":{\"first\":[[\"value\",[1,2]]],\"rest\":[],\"views\":[]}}],[{\"arrs\":{\"arrows\":[[[6],[[[0]],[1,2]]]]}}],[\"top\"]],\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\"}").toOption.getD .null
private def extracted := SourceClaimJson.extractGraphRequests ast claims "verification/tests/stateful-source/loop-transfers.ts"
#guard extracted.toOption.isSome
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0
#guard (SourceClaimJson.produceJson ast claims "verification/tests/stateful-source/loop-transfers.ts" 10).toOption.isSome
private def expected : Program :=
  [⟨.nul,.effect 12⟩,⟨.var 0,.ret⟩,⟨.fls,.bind 1⟩,
   ⟨.nul,.effect 10⟩,⟨.var 0,.ret⟩,⟨.tru,.bind 4⟩,
   ⟨.nul,.effect ⟨5,some [1]⟩⟩,⟨.var 0,.effect 6⟩,⟨.var 0,.bind 7⟩,
   ⟨.var 0,.branchBind ⟨8,some [2]⟩ ⟨5,some [2]⟩⟩,
   ⟨.var 0,.bind 9⟩,⟨.var 0,.branchBind ⟨3,some [0]⟩ ⟨2,some [0]⟩⟩,
   ⟨.var 0,.bind 11⟩,⟨.nul,.effect 0⟩]
#guard program == expected
#guard start == 13

-- Breaking the inner loop reaches the outer body's return true, rather than
-- the outer loop's false exit. The inner local is dropped at the transfer.
theorem nearest_break (b : Bool) : Execution expected (if b then 24 else 12) []
    (.at 13 (fun _ => if b then .tru else .fls)) [] (.done (if b then .tru else .fls)) := by
  cases b <;> repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next .yesBind
    | apply Execution.next .noBind
    | apply Execution.next (.ret rfl)

#print axioms nearest_break

private def continueAst : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"continueAfterWrite\",\"namePos\":[300,318],\"typeParams\":[],\"params\":[],\"retType\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":[{\"k\":\"const\",\"pos\":[334,383],\"bindings\":[{\"name\":\"cell\",\"namePos\":[340,344],\"annot\":{\"k\":\"object\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"readonly\":false,\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]}],\"stringIndex\":null,\"calls\":[],\"span\":[0,0]},\"init\":{\"k\":\"alloc\",\"pos\":[367,382],\"fields\":[{\"name\":\"value\",\"e\":{\"k\":\"lit\",\"pos\":[376,380],\"lit\":{\"a\":\"booleanlit\",\"v\":\"true\"}}}]}}]},{\"k\":\"const\",\"pos\":[386,454],\"bindings\":[{\"name\":\"test\",\"namePos\":[392,396],\"annot\":{\"k\":\"function\",\"receiver\":null,\"params\":[{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"rest\":null,\"result\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]},\"init\":{\"k\":\"lambda\",\"pos\":[421,453],\"result\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":{\"k\":\"read\",\"pos\":[443,453],\"e\":{\"k\":\"id\",\"pos\":[443,447],\"name\":\"cell\"},\"field\":\"value\"},\"params\":[{\"name\":\"x\",\"type\":{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}}]}}]},{\"k\":\"while\",\"pos\":[457,564],\"cond\":{\"k\":\"apply\",\"pos\":[464,474],\"callee\":{\"k\":\"id\",\"pos\":[464,468],\"name\":\"test\"},\"args\":[{\"k\":\"lit\",\"pos\":[469,473],\"lit\":{\"a\":\"null\"}}]},\"body\":[{\"k\":\"const\",\"pos\":[482,521],\"bindings\":[{\"name\":\"alias\",\"namePos\":[488,493],\"annot\":{\"k\":\"object\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"readonly\":false,\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]}],\"stringIndex\":null,\"calls\":[],\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[516,520],\"name\":\"cell\"}}]},{\"k\":\"effect\",\"pos\":[526,546],\"e\":{\"k\":\"write\",\"pos\":[526,545],\"receiver\":{\"k\":\"id\",\"pos\":[526,531],\"name\":\"alias\"},\"rhs\":{\"k\":\"lit\",\"pos\":[540,545],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}},\"field\":\"value\"}},{\"k\":\"continue\",\"pos\":[551,560]}]},{\"k\":\"return\",\"pos\":[567,585],\"e\":{\"k\":\"read\",\"pos\":[574,584],\"e\":{\"k\":\"id\",\"pos\":[574,578],\"name\":\"cell\"},\"field\":\"value\"}}]}]}").toOption.getD .null
private def continueClaims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"functions\":[{\"entries\":[{\"bindings\":[],\"start\":334},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null}],\"start\":386},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":457},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":482},{\"bindings\":[{\"name\":\"alias\",\"type\":[4],\"current\":null},{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":526},{\"bindings\":[{\"name\":\"alias\",\"type\":[4],\"current\":null},{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":551},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":567}],\"expressions\":[{\"pos\":[367,382],\"type\":[4],\"current\":null},{\"pos\":[376,380],\"type\":[1],\"current\":null},{\"pos\":[421,453],\"type\":[5],\"current\":null},{\"pos\":[443,447],\"type\":[4],\"current\":null},{\"pos\":[443,453],\"type\":[1,2],\"current\":null},{\"pos\":[464,468],\"type\":[5],\"current\":null},{\"pos\":[464,474],\"type\":[1,2],\"current\":null},{\"pos\":[469,473],\"type\":[0],\"current\":null},{\"pos\":[516,520],\"type\":[4],\"current\":null},{\"pos\":[526,531],\"type\":[4],\"current\":null},{\"pos\":[526,545],\"type\":[1,2],\"current\":null},{\"pos\":[540,545],\"type\":[1,2],\"current\":null},{\"pos\":[574,578],\"type\":[4],\"current\":null},{\"pos\":[574,584],\"type\":[1,2],\"current\":null}],\"name\":\"continueAfterWrite\",\"namePos\":[300,318],\"params\":[],\"result\":[1,2]}],\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[{\"refs\":{\"first\":[[\"value\",[1,2]]],\"rest\":[],\"views\":[]}}],[{\"arrs\":{\"arrows\":[[[6],[[[0]],[1,2]]]]}}],[\"top\"]],\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\"}").toOption.getD .null
private def continued := SourceClaimJson.extractGraphRequests continueAst continueClaims "verification/tests/stateful-source/loop-transfers.ts"
private def continueProgram : Program := [
  ⟨.nul,.effect 14⟩,
  ⟨.var 0,.ret⟩,
  ⟨.read (.var 0),.bind ⟨1,some [0, 2, 3]⟩⟩,
  ⟨.var 1,.bind 2⟩,
  ⟨.nul,.effect ⟨0,some [1, 2]⟩⟩,
  ⟨.var 0,.bind ⟨4,some [3, 4, 5]⟩⟩,
  ⟨.write (.var 1) (.var 0),.effect 5⟩,
  ⟨.fls,.bind 6⟩,
  ⟨.var 0,.bind 7⟩,
  ⟨.var 0,.effect 8⟩,
  ⟨.var 1,.bind 9⟩,
  ⟨.var 0,.branchBind ⟨10,some [2, 3]⟩ ⟨3,some [2, 3]⟩⟩,
  ⟨.app (.var 1) (.var 0),.bind ⟨11,some [0, 3, 4]⟩⟩,
  ⟨.nul,.bind 12⟩,
  ⟨.var 0,.bind 13⟩,
  ⟨.var 0,.effect 0⟩,
  ⟨.funE (.read (.var 2)),.bind 15⟩,
  ⟨.var 0,.effect 16⟩,
  ⟨.alloc (.var 0),.bind ⟨17,some [0]⟩⟩,
  ⟨.tru,.bind 18⟩,
  ⟨.nul,.effect 19⟩]
#guard ((continued.toOption.getD []).map (·.program)).headD [] == continueProgram
#guard ((continued.toOption.getD []).map (·.start)).headD 0 == 20
#guard (SourceClaimJson.produceJson continueAst continueClaims "verification/tests/stateful-source/loop-transfers.ts" 10).toOption.isSome

-- Continue drops the alias and returns to condition evaluation after the write.
theorem continue_retests : Execution continueProgram 60 []
    (.at 20 (fun _ => .nul)) [.fls,.nul] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.writeV rfl (by decide)))
    | apply Execution.next (.expr (.beta rfl))
    | apply Execution.next (.expr (.readV rfl))
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next .yesBind
    | apply Execution.next .noBind
    | apply Execution.next (.ret rfl)
#print axioms continue_retests

end Verification.Model.LoopTransferTests
