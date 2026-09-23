import Verification.Model.Source.SourceClaimJson

namespace Verification.Model.ObjectPatternTests
open Lean ProgramTyping SourceExtraction SourceClaimJson ControlFlow

-- `orderedDefaults` from tests/stateful-source/object-patterns.ts, captured
-- with its tsc claims after conversion to calculus labels. Extraction and
-- evidence checking below do not run a producer. The suite's source executions
-- cannot show what the lowering does; this traces the lowered program itself.
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/object-patterns.ts\",\"sourceSha256\":\"d72feb07e3ddd0aa162704a86dd42ed9e69531b6db8356dad19911a9e5d60567\",\"imports\":{\"roots\":[],\"definitions\":[]},\"functions\":[{\"name\":\"orderedDefaults\",\"namePos\":[853,868],\"typeParams\":[],\"params\":[{\"name\":\"seed\",\"pos\":[869,873],\"type\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"number\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"undefined\",\"span\":[0,0]}],\"span\":[0,0]}}],\"retType\":{\"k\":\"atom\",\"name\":\"number\",\"span\":[0,0]},\"body\":[{\"k\":\"let\",\"pos\":[907,939],\"bindings\":[{\"name\":\"state\",\"namePos\":[911,916],\"annot\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"number\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]},\"init\":{\"k\":\"lit\",\"pos\":[934,938],\"lit\":{\"a\":\"null\"}}}]},{\"k\":\"const\",\"pos\":[942,975],\"bindings\":[{\"name\":\"box\",\"namePos\":[948,951],\"annot\":null,\"init\":{\"k\":\"alloc\",\"pos\":[954,974],\"fields\":[{\"name\":\"a\",\"e\":{\"k\":\"id\",\"pos\":[959,963],\"name\":\"seed\"}},{\"name\":\"b\",\"e\":{\"k\":\"id\",\"pos\":[968,972],\"name\":\"seed\"}}]}}]},{\"k\":\"pattern\",\"pos\":[978,1034],\"props\":[{\"field\":\"a\",\"name\":\"first\",\"namePos\":[989,994],\"default_\":{\"k\":\"assign\",\"pos\":[997,1008],\"name\":\"state\",\"namePos\":[998,1003],\"rhs\":{\"k\":\"lit\",\"pos\":[1006,1007],\"lit\":{\"a\":\"numberlit\",\"v\":\"1\"}}}},{\"field\":\"b\",\"name\":\"b\",\"namePos\":[1010,1011],\"default_\":{\"k\":\"assign\",\"pos\":[1014,1025],\"name\":\"state\",\"namePos\":[1015,1020],\"rhs\":{\"k\":\"lit\",\"pos\":[1023,1024],\"lit\":{\"a\":\"numberlit\",\"v\":\"2\"}}}}],\"init\":{\"k\":\"id\",\"pos\":[1030,1033],\"name\":\"box\"}},{\"k\":\"return\",\"pos\":[1037,1055],\"e\":{\"k\":\"coalesce\",\"pos\":[1044,1054],\"left\":{\"k\":\"id\",\"pos\":[1044,1049],\"name\":\"state\"},\"right\":{\"k\":\"id\",\"pos\":[1053,1054],\"name\":\"b\"}}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/object-patterns.ts\",\"sourceSha256\":\"d72feb07e3ddd0aa162704a86dd42ed9e69531b6db8356dad19911a9e5d60567\",\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[\"num\"],[{\"refs\":{\"first\":[[\"value\",[3,4]]],\"rest\":[],\"views\":[]}}],[{\"numLit\":{\"bits\":\"0\"}}],[{\"refs\":{\"first\":[[\"value\",[4]]],\"rest\":[],\"views\":[]}}],[{\"refs\":{\"first\":[[\"a\",[3,4]],[\"b\",[3,4]]],\"rest\":[],\"views\":[]}}],[{\"numLit\":{\"bits\":\"4607182418800017408\"}}],[{\"numLit\":{\"bits\":\"4611686018427387904\"}}]],\"functions\":[{\"name\":\"orderedDefaults\",\"namePos\":[853,868],\"params\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null}],\"result\":[4],\"entries\":[{\"start\":907,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null}]},{\"start\":942,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null},{\"name\":\"state\",\"type\":[0,4],\"current\":null}]},{\"start\":978,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null},{\"name\":\"state\",\"type\":[0,4],\"current\":null},{\"name\":\"box\",\"type\":[8],\"current\":null}]},{\"start\":1037,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null},{\"name\":\"state\",\"type\":[0,4],\"current\":null},{\"name\":\"box\",\"type\":[8],\"current\":null},{\"name\":\"first\",\"type\":[4],\"current\":null},{\"name\":\"b\",\"type\":[4],\"current\":null}]}],\"expressions\":[{\"pos\":[934,938],\"type\":[0],\"current\":null},{\"pos\":[954,974],\"type\":[8],\"current\":null},{\"pos\":[959,963],\"type\":[3,4],\"current\":null},{\"pos\":[968,972],\"type\":[3,4],\"current\":null},{\"pos\":[997,1008],\"type\":[9],\"current\":null},{\"pos\":[1006,1007],\"type\":[9],\"current\":null},{\"pos\":[1014,1025],\"type\":[10],\"current\":null},{\"pos\":[1023,1024],\"type\":[10],\"current\":null},{\"pos\":[1030,1033],\"type\":[8],\"current\":null},{\"pos\":[1044,1054],\"type\":[4],\"current\":null},{\"pos\":[1044,1049],\"type\":[0,4],\"current\":null},{\"pos\":[1053,1054],\"type\":[4],\"current\":null}]}]}").toOption.getD .null
private def file := "verification/tests/stateful-source/object-patterns.ts"
private def extracted := SourceClaimJson.extractGraphRequests ast claims file
#guard extracted.toOption.isSome
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0
#guard (SourceClaimJson.produceJson ast claims file 10).toOption.isSome

-- From the entry (22): the state cell is allocated (18), then the box with
-- its two fields (15). Field `a` is read (12) and tested for undefined: only
-- an undefined read runs its default, which writes 1 to the state cell (10),
-- and both arms join (8). Field `b` is then read (7) and handled the same way,
-- its default writing 2 (4), joining at (2). The return reads the state cell
-- and falls back to `b` (1).
private def expected : Program :=
  [
   ⟨.var 0,.ret⟩,
   ⟨.letE (.readAt "value" (.var 3)) (.ite (.test .isNullish (.var 0)) (.var 1) (.var 0)),.bind 0⟩,
   ⟨.nul,.effect 1⟩,
   ⟨.nul,.effect ⟨2,some [0, 1, 3, 4, 5]⟩⟩,
   ⟨.var 0,.bind ⟨3,some [0, 2, 3, 4, 5, 6]⟩⟩,
   ⟨.writeAt "value" (.var 4) (.var 0),.effect 4⟩,
   ⟨.num 4611686018427387904,.bind 5⟩,
   ⟨.var 0,.tagBind .isUndef ⟨6,some [2, 3, 4, 5, 6]⟩ ⟨3,some [0, 2, 3, 4, 5, 6]⟩⟩,
   ⟨.readAt "b" (.var 1),.bind 7⟩,
   ⟨.nul,.effect 8⟩,
   ⟨.var 0,.bind ⟨9,some [0, 2, 3, 4, 5]⟩⟩,
   ⟨.writeAt "value" (.var 3) (.var 0),.effect 10⟩,
   ⟨.num 4607182418800017408,.bind 11⟩,
   ⟨.var 0,.tagBind .isUndef ⟨12,some [2, 3, 4, 5]⟩ ⟨9,some [0, 2, 3, 4, 5]⟩⟩,
   ⟨.readAt "a" (.var 0),.bind 13⟩,
   ⟨.var 0,.bind 14⟩,
   ⟨.nul,.effect 15⟩,
   ⟨.var 0,.effect 16⟩,
   ⟨.makeAt .absent ["a", "b"] [.var 1, .var 0],.bind ⟨17,some [0, 3, 4]⟩⟩,
   ⟨.var 2,.bind 18⟩,
   ⟨.var 1,.bind 19⟩,
   ⟨.makeAt .absent ["value"] [.var 0],.bind ⟨20,some [0, 2]⟩⟩,
   ⟨.var 0,.effect 21⟩,
   ⟨.nul,.bind 22⟩,
   ⟨.nul,.effect 23⟩]
#guard program == expected
#guard start == 24

/-- The seed in slot zero, nothing else bound. -/
private def seeded (v : Tm) : Env := fun i => if i == 0 then v else .nul

-- The heap holds the state cell, then the box's `a` and `b` locations. With
-- both fields undefined, both defaults run in pattern order: the state cell
-- ends at 2, which is returned. This is a trace of the lowered program, not
-- a general compiler proof.
theorem both_defaults_in_order : Execution expected 60 []
    (.at 24 (seeded .undef))
    [.num 4611686018427387904, .undef, .undef] (.done (.num 4611686018427387904)) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeFields (by decide) rfl))
    | apply Execution.next (.expr (.readField rfl rfl))
    | apply Execution.next (.expr (.writeField rfl rfl (by decide)))
    | apply Execution.next (.expr (.letC (.readField rfl rfl)))
    | apply Execution.next (.expr (.letV rfl))
    | apply Execution.next (.expr (.iteC (.testV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.tagBind rfl)
    | apply Execution.next (.ret rfl)

-- With both fields present neither default runs: the state cell stays null
-- and the read of `b`, the seed, is returned.
theorem no_default_runs : Execution expected 46 []
    (.at 24 (seeded (.num 4617315517961601024)))
    [.nul, .num 4617315517961601024, .num 4617315517961601024]
    (.done (.num 4617315517961601024)) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeFields (by decide) rfl))
    | apply Execution.next (.expr (.readField rfl rfl))
    | apply Execution.next (.expr (.writeField rfl rfl (by decide)))
    | apply Execution.next (.expr (.letC (.readField rfl rfl)))
    | apply Execution.next (.expr (.letV rfl))
    | apply Execution.next (.expr (.iteC (.testV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.tagBind rfl)
    | apply Execution.next (.ret rfl)

#print axioms both_defaults_in_order
#print axioms no_default_runs
end Verification.Model.ObjectPatternTests
