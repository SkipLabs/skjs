import Verification.ExperimentState.SourceClaimJson

namespace Verification.ExperimentState.WhileSourceTests
open Lean ProgramTyping SourceExtraction SourceClaimJson ControlFlow

-- Captured from the real source fixture, after conversion to calculus labels.
-- Extraction and evidence checking below do not run SKJS.
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loops.ts\",\"sourceSha256\":\"f891442e6d46faf1d517584d6d1824899f4bc43d07304b743b57fd71077982de\",\"functions\":[{\"name\":\"oneWrite\",\"namePos\":[126,134],\"params\":[],\"retType\":{\"top\":false,\"atoms\":[{\"a\":\"boolean\"}]},\"body\":[{\"k\":\"const\",\"pos\":[150,199],\"name\":\"cell\",\"namePos\":[156,160],\"annot\":{\"top\":false,\"atoms\":[{\"a\":\"record\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"read\":{\"top\":false,\"atoms\":[{\"a\":\"boolean\"}]},\"write\":{\"top\":false,\"atoms\":[{\"a\":\"boolean\"}]}}],\"indexes\":{\"string\":\"absent\",\"number\":\"absent\",\"symbol\":\"absent\"},\"call\":\"unknown\",\"construct\":\"unknown\",\"array\":\"unknown\"}]},\"init\":{\"k\":\"alloc\",\"pos\":[183,198],\"e\":{\"k\":\"lit\",\"pos\":[192,196],\"lit\":{\"a\":\"booleanlit\",\"v\":\"true\"}}}},{\"k\":\"const\",\"pos\":[202,270],\"name\":\"test\",\"namePos\":[208,212],\"annot\":{\"top\":false,\"atoms\":[{\"a\":\"function\",\"params\":[{\"top\":false,\"atoms\":[{\"a\":\"null\"}]}],\"result\":{\"top\":false,\"atoms\":[{\"a\":\"boolean\"}]},\"construct\":\"unknown\",\"array\":\"unknown\"}]},\"init\":{\"k\":\"lambda\",\"pos\":[237,269],\"name\":\"x\",\"arg\":{\"top\":false,\"atoms\":[{\"a\":\"null\"}]},\"result\":{\"top\":false,\"atoms\":[{\"a\":\"boolean\"}]},\"body\":{\"k\":\"read\",\"pos\":[259,269],\"e\":{\"k\":\"id\",\"pos\":[259,263],\"name\":\"cell\"}}}},{\"k\":\"while\",\"pos\":[273,366],\"cond\":{\"k\":\"apply\",\"pos\":[280,290],\"callee\":{\"k\":\"id\",\"pos\":[280,284],\"name\":\"test\"},\"arg\":{\"k\":\"lit\",\"pos\":[285,289],\"lit\":{\"a\":\"null\"}}},\"body\":[{\"k\":\"const\",\"pos\":[298,337],\"name\":\"alias\",\"namePos\":[304,309],\"annot\":{\"top\":false,\"atoms\":[{\"a\":\"record\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"read\":{\"top\":false,\"atoms\":[{\"a\":\"boolean\"}]},\"write\":{\"top\":false,\"atoms\":[{\"a\":\"boolean\"}]}}],\"indexes\":{\"string\":\"absent\",\"number\":\"absent\",\"symbol\":\"absent\"},\"call\":\"unknown\",\"construct\":\"unknown\",\"array\":\"unknown\"}]},\"init\":{\"k\":\"id\",\"pos\":[332,336],\"name\":\"cell\"}},{\"k\":\"effect\",\"pos\":[342,362],\"e\":{\"k\":\"write\",\"pos\":[342,361],\"receiver\":{\"k\":\"id\",\"pos\":[342,347],\"name\":\"alias\"},\"rhs\":{\"k\":\"lit\",\"pos\":[356,361],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}}}}]},{\"k\":\"return\",\"pos\":[369,387],\"e\":{\"k\":\"read\",\"pos\":[376,386],\"e\":{\"k\":\"id\",\"pos\":[376,380],\"name\":\"cell\"}}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loops.ts\",\"functions\":[{\"entries\":[{\"bindings\":[],\"start\":150},{\"bindings\":[{\"name\":\"cell\",\"type\":[9]}],\"start\":202},{\"bindings\":[{\"name\":\"cell\",\"type\":[9]},{\"name\":\"test\",\"type\":[17]}],\"start\":273},{\"bindings\":[{\"name\":\"cell\",\"type\":[9]},{\"name\":\"test\",\"type\":[17]}],\"start\":298},{\"bindings\":[{\"name\":\"alias\",\"type\":[9]},{\"name\":\"cell\",\"type\":[9]},{\"name\":\"test\",\"type\":[17]}],\"start\":342},{\"bindings\":[{\"name\":\"cell\",\"type\":[9]},{\"name\":\"test\",\"type\":[17]}],\"start\":369}],\"expressions\":[{\"pos\":[183,198],\"type\":[9]},{\"pos\":[192,196],\"type\":[1]},{\"pos\":[237,269],\"type\":[17]},{\"pos\":[259,263],\"type\":[9]},{\"pos\":[259,269],\"type\":[1,2]},{\"pos\":[280,284],\"type\":[17]},{\"pos\":[280,290],\"type\":[1,2]},{\"pos\":[285,289],\"type\":[0]},{\"pos\":[332,336],\"type\":[9]},{\"pos\":[342,347],\"type\":[9]},{\"pos\":[342,361],\"type\":[1,2]},{\"pos\":[356,361],\"type\":[1,2]},{\"pos\":[376,380],\"type\":[9]},{\"pos\":[376,386],\"type\":[1,2]}],\"name\":\"oneWrite\",\"namePos\":[126,134],\"params\":[],\"result\":[1,2]}],\"profile\":\"stateful-source-19-v1\",\"sourceSha256\":\"f891442e6d46faf1d517584d6d1824899f4bc43d07304b743b57fd71077982de\",\"version\":1}").toOption.getD .null
private def extracted := SourceClaimJson.extract ast claims "verification/tests/stateful-source/loops.ts"
#guard extracted.toOption.isSome
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0
#guard (SourceClaimJson.produceJson ast claims "verification/tests/stateful-source/loops.ts" 10).toOption.isSome
private def expected : Program :=
  [⟨.nul,.effect 13⟩,⟨.var 0,.ret⟩,
   ⟨.read (.var 0),.bind ⟨1,some [0,2,3]⟩⟩,⟨.var 1,.bind 2⟩,
   ⟨.var 0,.bind ⟨0,some [4,5]⟩⟩,
   ⟨.write (.var 1) (.var 0),.effect 4⟩,⟨.fls,.bind 5⟩,
   ⟨.var 0,.bind 6⟩,⟨.var 0,.effect 7⟩,⟨.var 1,.bind 8⟩,
   ⟨.var 0,.branchBind ⟨9,some [2,3]⟩ ⟨3,some [2,3]⟩⟩,
   ⟨.app (.var 1) (.var 0),.bind ⟨10,some [0,3,4]⟩⟩,
   ⟨.nul,.bind 11⟩,⟨.var 0,.bind 12⟩,⟨.var 0,.effect 0⟩,
   ⟨.lam (.read (.var 1)),.bind 14⟩,⟨.var 0,.effect 15⟩,
   ⟨.alloc (.var 0),.bind ⟨16,some [0]⟩⟩,⟨.tru,.bind 17⟩,⟨.nul,.effect 18⟩]
#guard program == expected
#guard start == 19

-- The condition is called twice: true before the write and false afterwards.
-- The alias local is dropped on the back edge; the original closure and cell
-- remain in the correct slots. This is a trace, not a general compiler proof.
theorem one_iteration : ∃ n, Execution expected n []
    (.at 19 (fun _ => .nul)) [.fls] (.done .fls) := by
  refine ⟨57,?_⟩
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.allocV rfl))
    | apply Execution.next (.expr (.writeV rfl (by decide)))
    | apply Execution.next (.expr (.beta rfl))
    | apply Execution.next (.expr (.readV rfl))
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next .yesBind
    | apply Execution.next .noBind
    | apply Execution.next (.ret rfl)

#print axioms one_iteration
end Verification.ExperimentState.WhileSourceTests
