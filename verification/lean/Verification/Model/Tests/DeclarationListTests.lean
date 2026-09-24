import Verification.Model.Source.SourceClaimJson

namespace Verification.Model.DeclarationListTests
open Lean ProgramTyping SourceExtraction SourceClaimJson ControlFlow

-- `laterWriteStaysSeparate` from tests/stateful-source/declaration-list.ts,
-- captured with its tsc claims after conversion to calculus labels. Extraction
-- and evidence checking below do not run a producer. What the suite's source
-- executions cannot show is checked here on the lowered program itself: the
-- `let` list allocates one cell per declarator, in source order, under one
-- entry, and the write to the first cell leaves the second cell as it was.
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/declaration-list.ts\",\"sourceSha256\":\"bdb1525a9aeb0f18e065db0cde90ee47e0d345b10bc09aab99bb5a14fc9a242e\",\"declarations\":{\"roots\":[],\"definitions\":[]},\"init\":[],\"functions\":[{\"name\":\"laterWriteStaysSeparate\",\"namePos\":[469,492],\"typeParams\":[],\"params\":[{\"name\":\"seed\",\"pos\":[493,497],\"type\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]}}],\"retType\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":[{\"k\":\"let\",\"pos\":[528,597],\"bindings\":[{\"name\":\"first\",\"namePos\":[532,537],\"annot\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[556,560],\"name\":\"seed\"}},{\"name\":\"second\",\"namePos\":[566,572],\"annot\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[591,596],\"name\":\"first\"}}]},{\"k\":\"effect\",\"pos\":[600,613],\"e\":{\"k\":\"assign\",\"pos\":[600,612],\"name\":\"first\",\"namePos\":[600,605],\"rhs\":{\"k\":\"lit\",\"pos\":[608,612],\"lit\":{\"a\":\"null\"}}}},{\"k\":\"if\",\"pos\":[616,651],\"cond\":{\"k\":\"bin\",\"pos\":[620,635],\"op\":\"!==\",\"l\":{\"k\":\"id\",\"pos\":[620,626],\"name\":\"second\"},\"r\":{\"k\":\"lit\",\"pos\":[631,635],\"lit\":{\"a\":\"null\"}}},\"then\":[{\"k\":\"return\",\"pos\":[637,651],\"e\":{\"k\":\"id\",\"pos\":[644,650],\"name\":\"second\"}}],\"else_\":null},{\"k\":\"return\",\"pos\":[654,667],\"e\":{\"k\":\"lit\",\"pos\":[661,666],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/declaration-list.ts\",\"sourceSha256\":\"bdb1525a9aeb0f18e065db0cde90ee47e0d345b10bc09aab99bb5a14fc9a242e\",\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[\"num\"],[{\"numLit\":{\"bits\":\"4611686018427387904\"}}],[{\"numLit\":{\"bits\":\"4607182418800017408\"}}]],\"functions\":[{\"name\":\"laterWriteStaysSeparate\",\"namePos\":[469,492],\"params\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null}],\"result\":[1,2],\"entries\":[{\"start\":528,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null}]},{\"start\":600,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[0,1,2],\"current\":null}]},{\"start\":616,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[0,1,2],\"current\":null}]},{\"start\":637,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[1,2],\"current\":null}]},{\"start\":654,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[0,1,2],\"current\":null}]}],\"expressions\":[{\"pos\":[556,560],\"type\":[0,1,2],\"current\":null},{\"pos\":[591,596],\"type\":[0,1,2],\"current\":null},{\"pos\":[600,612],\"type\":[0],\"current\":null},{\"pos\":[608,612],\"type\":[0],\"current\":null},{\"pos\":[620,635],\"type\":[1,2],\"current\":null},{\"pos\":[620,626],\"type\":[0,1,2],\"current\":null},{\"pos\":[631,635],\"type\":[0],\"current\":null},{\"pos\":[644,650],\"type\":[1,2],\"current\":null},{\"pos\":[661,666],\"type\":[2],\"current\":null}]}]}").toOption.getD .null
private def file := "verification/tests/stateful-source/declaration-list.ts"
private def extracted := SourceClaimJson.extractGraphRequests ast claims file
#guard extracted.toOption.isSome
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0
#guard (SourceClaimJson.produceJson ast claims file 10).toOption.isSome

-- From the entry (19): the seed is checked against the first contract and
-- allocated (16); the first cell is read (14) and that value allocated as the
-- second cell (12); only then is null written to the first cell (10), the
-- second cell read and tested (9, 5), and its contents or false returned.
private def expected : Program :=
  [
   ⟨.var 0,.ret⟩,
   ⟨.fls,.bind 0⟩,
   ⟨.nul,.effect 1⟩,
   ⟨.var 0,.ret⟩,
   ⟨.readAt "value" (.var 0),.bind 3⟩,
   ⟨.nul,.effect 4⟩,
   ⟨.var 1,.tagBind .isNul ⟨2,some [3, 4, 5]⟩ ⟨5,some [3, 4, 5]⟩⟩,
   ⟨.ite (.test .isNul (.var 1)) (.fls) (.tru),.bind ⟨6,some [0, 3, 4, 5, 6]⟩⟩,
   ⟨.nul,.bind 7⟩,
   ⟨.var 0,.bind 8⟩,
   ⟨.readAt "value" (.var 0),.bind 9⟩,
   ⟨.nul,.effect 10⟩,
   ⟨.var 0,.bind ⟨11,some [2, 3, 4]⟩⟩,
   ⟨.writeAt "value" (.var 2) (.var 0),.effect 12⟩,
   ⟨.nul,.bind 13⟩,
   ⟨.nul,.effect 14⟩,
   ⟨.makeAt .absent ["value"] [.var 0],.bind ⟨15,some [0, 2, 3]⟩⟩,
   ⟨.var 0,.effect 16⟩,
   ⟨.readAt "value" (.var 0),.bind 17⟩,
   ⟨.makeAt .absent ["value"] [.var 0],.bind ⟨18,some [0, 2]⟩⟩,
   ⟨.var 0,.effect 19⟩,
   ⟨.var 0,.bind 20⟩,
   ⟨.nul,.effect 21⟩]
#guard program == expected
#guard start == 22

/-- The seed in slot zero, nothing else bound. -/
private def seeded (v : Tm) : Env := fun i => if i == 0 then v else .nul

-- The heap holds the first cell then the second. After the run the first cell
-- is null and the second still holds the seed, which a non-null seed returns.
-- This is a trace of the lowered program, not a general compiler proof.
theorem separate_cells (b : Bool) : Execution expected 48 []
    (.at 22 (seeded (if b then .tru else .fls)))
    [.nul, if b then .tru else .fls] (.done (if b then .tru else .fls)) := by
  cases b <;> repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeFields (by decide) rfl))
    | apply Execution.next (.expr (.readField rfl rfl))
    | apply Execution.next (.expr (.writeField rfl rfl (by decide)))
    | apply Execution.next (.expr (.iteC (.testV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.tagBind rfl)
    | apply Execution.next (.ret rfl)

-- A null seed copies null into the second cell and returns false.
theorem null_seed : Execution expected 47 []
    (.at 22 (seeded .nul)) [.nul, .nul] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeFields (by decide) rfl))
    | apply Execution.next (.expr (.readField rfl rfl))
    | apply Execution.next (.expr (.writeField rfl rfl (by decide)))
    | apply Execution.next (.expr (.iteC (.testV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.tagBind rfl)
    | apply Execution.next (.ret rfl)

#print axioms separate_cells
#print axioms null_seed
end Verification.Model.DeclarationListTests
