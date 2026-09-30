import Verification.Model.Source.SourceClaimJson
import Verification.Model.Tests.ExecutionModelTests

/-! Lowered programs run by the machine. Each fixture is a source function of
`tests/stateful-source`, its parser document and its claims converted to
calculus labels; extraction lowers it without a producer, the lowered program
is pinned, and a trace runs it to the value JavaScript returns. No
source-to-graph preservation theorem exists, and a pipeline case does not
show these: the claims the producer states read the bindings involved at
their declared contracts, which a lowering that changed the order or the
cells would still meet. Each trace is of one lowered program, not a general
compiler proof. -/
namespace Verification.Model.LoweringTraceTests
open Lean ProgramTyping SourceExtraction SourceClaimJson ControlFlow

/-! ## Declaration lists

A `let` list: one cell per declarator, in source order. -/
namespace DeclarationList
-- `laterWriteStaysSeparate` from tests/stateful-source/declaration-list.ts,
-- with its tsc claims converted to calculus labels.
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/declaration-list.ts\",\"sourceSha256\":\"bdb1525a9aeb0f18e065db0cde90ee47e0d345b10bc09aab99bb5a14fc9a242e\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"laterWriteStaysSeparate\",\"namePos\":[469,492],\"typeParams\":[],\"params\":[{\"name\":\"seed\",\"pos\":[493,497],\"type\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]}}],\"retType\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":[{\"k\":\"let\",\"pos\":[528,597],\"bindings\":[{\"name\":\"first\",\"namePos\":[532,537],\"annot\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[556,560],\"name\":\"seed\"}},{\"name\":\"second\",\"namePos\":[566,572],\"annot\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[591,596],\"name\":\"first\"}}]},{\"k\":\"effect\",\"pos\":[600,613],\"e\":{\"k\":\"assign\",\"pos\":[600,612],\"name\":\"first\",\"namePos\":[600,605],\"rhs\":{\"k\":\"lit\",\"pos\":[608,612],\"lit\":{\"a\":\"null\"}}}},{\"k\":\"if\",\"pos\":[616,651],\"cond\":{\"k\":\"bin\",\"pos\":[620,635],\"op\":\"!==\",\"l\":{\"k\":\"id\",\"pos\":[620,626],\"name\":\"second\"},\"r\":{\"k\":\"lit\",\"pos\":[631,635],\"lit\":{\"a\":\"null\"}}},\"then\":[{\"k\":\"return\",\"pos\":[637,651],\"e\":{\"k\":\"id\",\"pos\":[644,650],\"name\":\"second\"}}],\"else_\":null},{\"k\":\"return\",\"pos\":[654,667],\"e\":{\"k\":\"lit\",\"pos\":[661,666],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/declaration-list.ts\",\"sourceSha256\":\"bdb1525a9aeb0f18e065db0cde90ee47e0d345b10bc09aab99bb5a14fc9a242e\",\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[\"num\"],[{\"numLit\":{\"bits\":\"4611686018427387904\"}}],[{\"numLit\":{\"bits\":\"4607182418800017408\"}}]],\"functions\":[{\"name\":\"laterWriteStaysSeparate\",\"namePos\":[469,492],\"params\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null}],\"result\":[1,2],\"entries\":[{\"start\":528,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null}]},{\"start\":600,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[0,1,2],\"current\":null}]},{\"start\":616,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[0,1,2],\"current\":null}]},{\"start\":637,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[1,2],\"current\":null}]},{\"start\":654,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[0,1,2],\"current\":null}]}],\"expressions\":[{\"pos\":[556,560],\"type\":[0,1,2],\"current\":null},{\"pos\":[591,596],\"type\":[0,1,2],\"current\":null},{\"pos\":[600,612],\"type\":[0],\"current\":null},{\"pos\":[608,612],\"type\":[0],\"current\":null},{\"pos\":[620,635],\"type\":[1,2],\"current\":null},{\"pos\":[620,626],\"type\":[0,1,2],\"current\":null},{\"pos\":[631,635],\"type\":[0],\"current\":null},{\"pos\":[644,650],\"type\":[1,2],\"current\":null},{\"pos\":[661,666],\"type\":[2],\"current\":null}]}]}").toOption.getD .null
private def file := "verification/tests/stateful-source/declaration-list.ts"
private def extracted := SourceClaimJson.extractGraphRequests ast claims file
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0

-- From the entry (19): the seed is checked against the first contract and
-- allocated (16); the first cell is read (14) and that value allocated as the
-- second cell (12); only then is null written to the first cell (10), the
-- second cell read and tested (9, 5), and its contents or false returned.
private def expected : Program :=
  [
   ⟨.var 0,.ret,none⟩,
   ⟨.fls,.bind 0,none⟩,
   ⟨.nul,.effect 1,none⟩,
   ⟨.var 0,.ret,none⟩,
   ⟨.readAt "value" (.var 0),.bind 3,none⟩,
   ⟨.nul,.effect 4,none⟩,
   ⟨.var 1,.tagBind .isNul ⟨2,some [3, 4, 5]⟩ ⟨5,some [3, 4, 5]⟩,none⟩,
   ⟨.ite (.test .isNul (.var 1)) (.fls) (.tru),.bind ⟨6,some [0, 3, 4, 5, 6]⟩,none⟩,
   ⟨.nul,.bind 7,none⟩,
   ⟨.var 0,.bind 8,none⟩,
   ⟨.readAt "value" (.var 0),.bind 9,none⟩,
   ⟨.nul,.effect 10,none⟩,
   ⟨.var 0,.bind ⟨11,some [2, 3, 4]⟩,none⟩,
   ⟨.writeAt "value" (.var 2) (.var 0),.effect 12,none⟩,
   ⟨.nul,.bind 13,none⟩,
   ⟨.nul,.effect 14,none⟩,
   ⟨.makeAt .absent ["value"] [.var 0],.bind ⟨15,some [0, 2, 3]⟩,none⟩,
   ⟨.var 0,.effect 16,none⟩,
   ⟨.readAt "value" (.var 0),.bind 17,none⟩,
   ⟨.makeAt .absent ["value"] [.var 0],.bind ⟨18,some [0, 2]⟩,none⟩,
   ⟨.var 0,.effect 19,none⟩,
   ⟨.var 0,.bind 20,none⟩,
   ⟨.nul,.effect 21,none⟩]
#guard program == expected
#guard start == 22

/-- The seed in slot zero, nothing else bound. -/
private def seeded (v : Tm) : Env := fun i => if i == 0 then v else .nul

-- The heap holds the first cell then the second. After the run the first cell
-- is null and the second still holds the seed, which a non-null seed returns.
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

#print axioms separate_cells
end DeclarationList

/-! ## Object patterns

An object pattern: the initializer held once, properties read in order, defaults run in pattern order for missing properties only. -/
namespace ObjectPattern
-- `orderedDefaults` from tests/stateful-source/object-patterns.ts, with its
-- tsc claims converted to calculus labels.
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/object-patterns.ts\",\"sourceSha256\":\"d72feb07e3ddd0aa162704a86dd42ed9e69531b6db8356dad19911a9e5d60567\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"orderedDefaults\",\"namePos\":[853,868],\"typeParams\":[],\"params\":[{\"name\":\"seed\",\"pos\":[869,873],\"type\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"number\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"undefined\",\"span\":[0,0]}],\"span\":[0,0]}}],\"retType\":{\"k\":\"atom\",\"name\":\"number\",\"span\":[0,0]},\"body\":[{\"k\":\"let\",\"pos\":[907,939],\"bindings\":[{\"name\":\"state\",\"namePos\":[911,916],\"annot\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"number\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]},\"init\":{\"k\":\"lit\",\"pos\":[934,938],\"lit\":{\"a\":\"null\"}}}]},{\"k\":\"const\",\"pos\":[942,975],\"bindings\":[{\"name\":\"box\",\"namePos\":[948,951],\"annot\":null,\"init\":{\"k\":\"alloc\",\"pos\":[954,974],\"fields\":[{\"name\":\"a\",\"e\":{\"k\":\"id\",\"pos\":[959,963],\"name\":\"seed\"}},{\"name\":\"b\",\"e\":{\"k\":\"id\",\"pos\":[968,972],\"name\":\"seed\"}}]}}]},{\"k\":\"destructure\",\"pos\":[978,1034],\"target\":{\"k\":\"object\",\"pos\":[984,1027],\"props\":[{\"field\":\"a\",\"target\":{\"k\":\"name\",\"name\":\"first\",\"pos\":[989,994]},\"default_\":{\"k\":\"assign\",\"pos\":[997,1008],\"name\":\"state\",\"namePos\":[998,1003],\"rhs\":{\"k\":\"lit\",\"pos\":[1006,1007],\"lit\":{\"a\":\"numberlit\",\"v\":\"1\"}}}},{\"field\":\"b\",\"target\":{\"k\":\"name\",\"name\":\"b\",\"pos\":[1010,1011]},\"default_\":{\"k\":\"assign\",\"pos\":[1014,1025],\"name\":\"state\",\"namePos\":[1015,1020],\"rhs\":{\"k\":\"lit\",\"pos\":[1023,1024],\"lit\":{\"a\":\"numberlit\",\"v\":\"2\"}}}}],\"rest\":null},\"default_\":null,\"init\":{\"k\":\"id\",\"pos\":[1030,1033],\"name\":\"box\"}},{\"k\":\"return\",\"pos\":[1037,1055],\"e\":{\"k\":\"coalesce\",\"pos\":[1044,1054],\"left\":{\"k\":\"id\",\"pos\":[1044,1049],\"name\":\"state\"},\"right\":{\"k\":\"id\",\"pos\":[1053,1054],\"name\":\"b\"}}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/object-patterns.ts\",\"sourceSha256\":\"d72feb07e3ddd0aa162704a86dd42ed9e69531b6db8356dad19911a9e5d60567\",\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[\"num\"],[{\"refs\":{\"first\":[[\"value\",[3,4]]],\"rest\":[],\"views\":[]}}],[{\"numLit\":{\"bits\":\"0\"}}],[{\"refs\":{\"first\":[[\"value\",[4]]],\"rest\":[],\"views\":[]}}],[{\"refs\":{\"first\":[[\"a\",[3,4]],[\"b\",[3,4]]],\"rest\":[],\"views\":[]}}],[{\"numLit\":{\"bits\":\"4607182418800017408\"}}],[{\"numLit\":{\"bits\":\"4611686018427387904\"}}]],\"functions\":[{\"name\":\"orderedDefaults\",\"namePos\":[853,868],\"params\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null}],\"result\":[4],\"entries\":[{\"start\":907,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null}]},{\"start\":942,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null},{\"name\":\"state\",\"type\":[0,4],\"current\":null}]},{\"start\":978,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null},{\"name\":\"state\",\"type\":[0,4],\"current\":null},{\"name\":\"box\",\"type\":[8],\"current\":null}]},{\"start\":1037,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null},{\"name\":\"state\",\"type\":[0,4],\"current\":null},{\"name\":\"box\",\"type\":[8],\"current\":null},{\"name\":\"first\",\"type\":[4],\"current\":null},{\"name\":\"b\",\"type\":[4],\"current\":null}]}],\"expressions\":[{\"pos\":[934,938],\"type\":[0],\"current\":null},{\"pos\":[954,974],\"type\":[8],\"current\":null},{\"pos\":[959,963],\"type\":[3,4],\"current\":null},{\"pos\":[968,972],\"type\":[3,4],\"current\":null},{\"pos\":[997,1008],\"type\":[9],\"current\":null},{\"pos\":[1006,1007],\"type\":[9],\"current\":null},{\"pos\":[1014,1025],\"type\":[10],\"current\":null},{\"pos\":[1023,1024],\"type\":[10],\"current\":null},{\"pos\":[1030,1033],\"type\":[8],\"current\":null},{\"pos\":[1044,1054],\"type\":[4],\"current\":null},{\"pos\":[1044,1049],\"type\":[0,4],\"current\":null},{\"pos\":[1053,1054],\"type\":[4],\"current\":null}]}]}").toOption.getD .null
private def file := "verification/tests/stateful-source/object-patterns.ts"
private def extracted := SourceClaimJson.extractGraphRequests ast claims file
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0

-- From the entry (22): the state cell is allocated (18), then the box with
-- its two fields (15). Field `a` is read (12) and tested for undefined: only
-- an undefined read runs its default, which writes 1 to the state cell (10),
-- and both arms join (8). Field `b` is then read (7) and handled the same way,
-- its default writing 2 (4), joining at (2). The return reads the state cell
-- and falls back to `b` (1).
private def expected : Program :=
  [
   ⟨.var 0,.ret,none⟩,
   ⟨.letE (.readAt "value" (.var 3)) (.ite (.test .isNullish (.var 0)) (.var 1) (.var 0)),.bind 0,none⟩,
   ⟨.nul,.effect 1,none⟩,
   ⟨.nul,.effect ⟨2,some [0, 1, 3, 4, 5]⟩,none⟩,
   ⟨.var 0,.bind ⟨3,some [0, 2, 3, 4, 5, 6]⟩,none⟩,
   ⟨.writeAt "value" (.var 4) (.var 0),.effect 4,none⟩,
   ⟨.num 4611686018427387904,.bind 5,none⟩,
   ⟨.var 0,.tagBind .isUndef ⟨6,some [2, 3, 4, 5, 6]⟩ ⟨3,some [0, 2, 3, 4, 5, 6]⟩,none⟩,
   ⟨.readAt "b" (.var 1),.bind 7,none⟩,
   ⟨.nul,.effect 8,none⟩,
   ⟨.var 0,.bind ⟨9,some [0, 2, 3, 4, 5]⟩,none⟩,
   ⟨.writeAt "value" (.var 3) (.var 0),.effect 10,none⟩,
   ⟨.num 4607182418800017408,.bind 11,none⟩,
   ⟨.var 0,.tagBind .isUndef ⟨12,some [2, 3, 4, 5]⟩ ⟨9,some [0, 2, 3, 4, 5]⟩,none⟩,
   ⟨.readAt "a" (.var 0),.bind 13,none⟩,
   ⟨.var 0,.bind 14,none⟩,
   ⟨.nul,.effect 15,none⟩,
   ⟨.var 0,.effect 16,none⟩,
   ⟨.makeAt .absent ["a", "b"] [.var 1, .var 0],.bind ⟨17,some [0, 3, 4]⟩,none⟩,
   ⟨.var 2,.bind 18,none⟩,
   ⟨.var 1,.bind 19,none⟩,
   ⟨.makeAt .absent ["value"] [.var 0],.bind ⟨20,some [0, 2]⟩,none⟩,
   ⟨.var 0,.effect 21,none⟩,
   ⟨.nul,.bind 22,none⟩,
   ⟨.nul,.effect 23,none⟩]
#guard program == expected
#guard start == 24

/-- The seed in slot zero, nothing else bound. -/
private def seeded (v : Tm) : Env := fun i => if i == 0 then v else .nul

-- The heap holds the state cell, then the box's `a` and `b` locations. With
-- both fields undefined, both defaults run in pattern order: the state cell
-- ends at 2, which is returned.
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
end ObjectPattern

/-! ## `while`

A `while` loop: the back edge drops the alias local and keeps the closure and cell in place. -/
namespace While
-- `oneWrite` from tests/stateful-source/loops.ts, with its tsc claims
-- converted to calculus labels.
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loops.ts\",\"sourceSha256\":\"f891442e6d46faf1d517584d6d1824899f4bc43d07304b743b57fd71077982de\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"oneWrite\",\"namePos\":[126,134],\"typeParams\":[],\"params\":[],\"retType\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":[{\"k\":\"const\",\"pos\":[150,199],\"bindings\":[{\"name\":\"cell\",\"namePos\":[156,160],\"annot\":{\"k\":\"object\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"readonly\":false,\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]}],\"stringIndex\":null,\"calls\":[],\"span\":[0,0]},\"init\":{\"k\":\"alloc\",\"pos\":[183,198],\"fields\":[{\"name\":\"value\",\"e\":{\"k\":\"lit\",\"pos\":[192,196],\"lit\":{\"a\":\"booleanlit\",\"v\":\"true\"}}}]}}]},{\"k\":\"const\",\"pos\":[202,270],\"bindings\":[{\"name\":\"test\",\"namePos\":[208,212],\"annot\":{\"k\":\"function\",\"effect\":\"unrestricted\",\"receiver\":null,\"params\":[{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"rest\":null,\"result\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]},\"init\":{\"k\":\"lambda\",\"pos\":[237,269],\"result\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":{\"k\":\"read\",\"pos\":[259,269],\"e\":{\"k\":\"id\",\"pos\":[259,263],\"name\":\"cell\"},\"field\":\"value\"},\"params\":[{\"name\":\"x\",\"type\":{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}}]}}]},{\"k\":\"while\",\"pos\":[273,366],\"cond\":{\"k\":\"apply\",\"pos\":[280,290],\"callee\":{\"k\":\"id\",\"pos\":[280,284],\"name\":\"test\"},\"args\":[{\"k\":\"lit\",\"pos\":[285,289],\"lit\":{\"a\":\"null\"}}]},\"body\":[{\"k\":\"const\",\"pos\":[298,337],\"bindings\":[{\"name\":\"alias\",\"namePos\":[304,309],\"annot\":{\"k\":\"object\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"readonly\":false,\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]}],\"stringIndex\":null,\"calls\":[],\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[332,336],\"name\":\"cell\"}}]},{\"k\":\"effect\",\"pos\":[342,362],\"e\":{\"k\":\"write\",\"pos\":[342,361],\"receiver\":{\"k\":\"id\",\"pos\":[342,347],\"name\":\"alias\"},\"rhs\":{\"k\":\"lit\",\"pos\":[356,361],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}},\"field\":\"value\"}}],\"update\":[]},{\"k\":\"return\",\"pos\":[369,387],\"e\":{\"k\":\"read\",\"pos\":[376,386],\"e\":{\"k\":\"id\",\"pos\":[376,380],\"name\":\"cell\"},\"field\":\"value\"}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loops.ts\",\"functions\":[{\"entries\":[{\"bindings\":[],\"start\":150},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null}],\"start\":202},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":273},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":298},{\"bindings\":[{\"name\":\"alias\",\"type\":[4],\"current\":null},{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":342},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":369}],\"expressions\":[{\"pos\":[183,198],\"type\":[4],\"current\":null},{\"pos\":[192,196],\"type\":[1],\"current\":null},{\"pos\":[237,269],\"type\":[5],\"current\":null},{\"pos\":[259,263],\"type\":[4],\"current\":null},{\"pos\":[259,269],\"type\":[1,2],\"current\":null},{\"pos\":[280,284],\"type\":[5],\"current\":null},{\"pos\":[280,290],\"type\":[1,2],\"current\":null},{\"pos\":[285,289],\"type\":[0],\"current\":null},{\"pos\":[332,336],\"type\":[4],\"current\":null},{\"pos\":[342,347],\"type\":[4],\"current\":null},{\"pos\":[342,361],\"type\":[1,2],\"current\":null},{\"pos\":[356,361],\"type\":[1,2],\"current\":null},{\"pos\":[376,380],\"type\":[4],\"current\":null},{\"pos\":[376,386],\"type\":[1,2],\"current\":null}],\"name\":\"oneWrite\",\"namePos\":[126,134],\"params\":[],\"result\":[1,2]}],\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[{\"refs\":{\"first\":[[\"value\",[1,2]]],\"rest\":[],\"views\":[]}}],[{\"arrs\":{\"arrows\":[{\"receiver\":[6],\"arguments\":[[0]],\"result\":[1,2],\"effect\":\"unrestricted\"}]}}],[\"top\"]],\"sourceSha256\":\"f891442e6d46faf1d517584d6d1824899f4bc43d07304b743b57fd71077982de\"}").toOption.getD .null
private def extracted := SourceClaimJson.extractGraphRequests ast claims "verification/tests/stateful-source/loops.ts"
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0
private def expected : Program :=
  [⟨.nul,.effect 13,none⟩,⟨.var 0,.ret,none⟩,
   ⟨.read (.var 0),.bind ⟨1,some [0,2,3]⟩,none⟩,⟨.var 1,.bind 2,none⟩,
   ⟨.var 0,.bind ⟨0,some [4,5]⟩,none⟩,
   ⟨.write (.var 1) (.var 0),.effect 4,none⟩,⟨.fls,.bind 5,none⟩,
   ⟨.var 0,.bind 6,none⟩,⟨.var 0,.effect 7,none⟩,⟨.var 1,.bind 8,none⟩,
   ⟨.var 0,.branchBind ⟨9,some [2,3]⟩ ⟨3,some [2,3]⟩,none⟩,
   ⟨.app (.var 1) (.var 0),.bind ⟨10,some [0,3,4]⟩,none⟩,
   ⟨.nul,.bind 11,none⟩,⟨.var 0,.bind 12,none⟩,⟨.var 0,.effect 0,none⟩,
   ⟨.makeAt (.graph 1 [.var 0, .read (.var 0), .var 2]
      [(.ret, none), (.bind ⟨0, some [0, 2, 3, 4]⟩, none), (.bind ⟨1, none⟩, none)] 2 [.var 0])
      [codeField] [.nul],.bind 14,none⟩,
   ⟨.var 0,.effect 15,none⟩,
   ⟨.alloc (.var 0),.bind ⟨16,some [0]⟩,none⟩,⟨.tru,.bind 17,none⟩,⟨.nul,.effect 18,none⟩]
#guard program == expected
#guard start == 19

-- The condition is called twice: true before the write and false afterwards.
-- The alias local is dropped on the back edge; the original closure and cell
-- remain in the correct slots.
theorem one_iteration : ∃ n, Execution expected n []
    (.at 19 (fun _ => .nul)) [.fls,.nul] (.done .fls) := by
  apply Exists.intro
  run_machine

#print axioms one_iteration
end While

/-! ## Loop transfers

`break` and `continue`: the nearest loop's exit, and the retest after the body's write. -/
namespace LoopTransfer
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"nestedBreak\",\"namePos\":[598,609],\"typeParams\":[],\"params\":[{\"name\":\"flag\",\"pos\":[610,614],\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]}}],\"retType\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":[{\"k\":\"while\",\"pos\":[638,746],\"cond\":{\"k\":\"id\",\"pos\":[645,649],\"name\":\"flag\"},\"body\":[{\"k\":\"while\",\"pos\":[657,725],\"cond\":{\"k\":\"id\",\"pos\":[664,668],\"name\":\"flag\"},\"body\":[{\"k\":\"const\",\"pos\":[678,706],\"bindings\":[{\"name\":\"local\",\"namePos\":[684,689],\"annot\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[701,705],\"name\":\"flag\"}}]},{\"k\":\"break\",\"pos\":[713,719],\"label\":null}],\"update\":[]},{\"k\":\"return\",\"pos\":[730,742],\"e\":{\"k\":\"lit\",\"pos\":[737,741],\"lit\":{\"a\":\"booleanlit\",\"v\":\"true\"}}}],\"update\":[]},{\"k\":\"return\",\"pos\":[749,762],\"e\":{\"k\":\"lit\",\"pos\":[756,761],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"functions\":[{\"entries\":[{\"bindings\":[{\"name\":\"flag\",\"type\":[1,2],\"current\":null}],\"start\":638},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null}],\"start\":657},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null}],\"start\":678},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null},{\"name\":\"local\",\"type\":[1,2],\"current\":null}],\"start\":713},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null}],\"start\":730},{\"bindings\":[{\"name\":\"flag\",\"type\":[1,2],\"current\":null}],\"start\":749}],\"expressions\":[{\"pos\":[645,649],\"type\":[1,2],\"current\":null},{\"pos\":[664,668],\"type\":[1],\"current\":null},{\"pos\":[701,705],\"type\":[1],\"current\":null},{\"pos\":[737,741],\"type\":[1],\"current\":null},{\"pos\":[756,761],\"type\":[2],\"current\":null}],\"name\":\"nestedBreak\",\"namePos\":[598,609],\"params\":[{\"name\":\"flag\",\"type\":[1,2],\"current\":null}],\"result\":[1,2]}],\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[{\"refs\":{\"first\":[[\"value\",[1,2]]],\"rest\":[],\"views\":[]}}],[{\"arrs\":{\"arrows\":[{\"receiver\":[6],\"arguments\":[[0]],\"result\":[1,2],\"effect\":\"unrestricted\"}]}}],[\"top\"]],\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\"}").toOption.getD .null
private def extracted := SourceClaimJson.extractGraphRequests ast claims "verification/tests/stateful-source/loop-transfers.ts"
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0
private def expected : Program :=
  [⟨.nul,.effect 12,none⟩,⟨.var 0,.ret,none⟩,⟨.fls,.bind 1,none⟩,
   ⟨.nul,.effect 10,none⟩,⟨.var 0,.ret,none⟩,⟨.tru,.bind 4,none⟩,
   ⟨.nul,.effect ⟨5,some [1]⟩,none⟩,⟨.var 0,.effect 6,none⟩,⟨.var 0,.bind 7,none⟩,
   ⟨.var 0,.branchBind ⟨8,some [2]⟩ ⟨5,some [2]⟩,none⟩,
   ⟨.var 0,.bind 9,none⟩,⟨.var 0,.branchBind ⟨3,some [0]⟩ ⟨2,some [0]⟩,none⟩,
   ⟨.var 0,.bind 11,none⟩,⟨.nul,.effect 0,none⟩]
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

private def continueAst : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"continueAfterWrite\",\"namePos\":[300,318],\"typeParams\":[],\"params\":[],\"retType\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":[{\"k\":\"const\",\"pos\":[334,383],\"bindings\":[{\"name\":\"cell\",\"namePos\":[340,344],\"annot\":{\"k\":\"object\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"readonly\":false,\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]}],\"stringIndex\":null,\"calls\":[],\"span\":[0,0]},\"init\":{\"k\":\"alloc\",\"pos\":[367,382],\"fields\":[{\"name\":\"value\",\"e\":{\"k\":\"lit\",\"pos\":[376,380],\"lit\":{\"a\":\"booleanlit\",\"v\":\"true\"}}}]}}]},{\"k\":\"const\",\"pos\":[386,454],\"bindings\":[{\"name\":\"test\",\"namePos\":[392,396],\"annot\":{\"k\":\"function\",\"effect\":\"unrestricted\",\"receiver\":null,\"params\":[{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"rest\":null,\"result\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]},\"init\":{\"k\":\"lambda\",\"pos\":[421,453],\"result\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":{\"k\":\"read\",\"pos\":[443,453],\"e\":{\"k\":\"id\",\"pos\":[443,447],\"name\":\"cell\"},\"field\":\"value\"},\"params\":[{\"name\":\"x\",\"type\":{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}}]}}]},{\"k\":\"while\",\"pos\":[457,564],\"cond\":{\"k\":\"apply\",\"pos\":[464,474],\"callee\":{\"k\":\"id\",\"pos\":[464,468],\"name\":\"test\"},\"args\":[{\"k\":\"lit\",\"pos\":[469,473],\"lit\":{\"a\":\"null\"}}]},\"body\":[{\"k\":\"const\",\"pos\":[482,521],\"bindings\":[{\"name\":\"alias\",\"namePos\":[488,493],\"annot\":{\"k\":\"object\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"readonly\":false,\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]}],\"stringIndex\":null,\"calls\":[],\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[516,520],\"name\":\"cell\"}}]},{\"k\":\"effect\",\"pos\":[526,546],\"e\":{\"k\":\"write\",\"pos\":[526,545],\"receiver\":{\"k\":\"id\",\"pos\":[526,531],\"name\":\"alias\"},\"rhs\":{\"k\":\"lit\",\"pos\":[540,545],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}},\"field\":\"value\"}},{\"k\":\"continue\",\"pos\":[551,560]}],\"update\":[]},{\"k\":\"return\",\"pos\":[567,585],\"e\":{\"k\":\"read\",\"pos\":[574,584],\"e\":{\"k\":\"id\",\"pos\":[574,578],\"name\":\"cell\"},\"field\":\"value\"}}]}]}").toOption.getD .null
private def continueClaims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"functions\":[{\"entries\":[{\"bindings\":[],\"start\":334},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null}],\"start\":386},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":457},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":482},{\"bindings\":[{\"name\":\"alias\",\"type\":[4],\"current\":null},{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":526},{\"bindings\":[{\"name\":\"alias\",\"type\":[4],\"current\":null},{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":551},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":567}],\"expressions\":[{\"pos\":[367,382],\"type\":[4],\"current\":null},{\"pos\":[376,380],\"type\":[1],\"current\":null},{\"pos\":[421,453],\"type\":[5],\"current\":null},{\"pos\":[443,447],\"type\":[4],\"current\":null},{\"pos\":[443,453],\"type\":[1,2],\"current\":null},{\"pos\":[464,468],\"type\":[5],\"current\":null},{\"pos\":[464,474],\"type\":[1,2],\"current\":null},{\"pos\":[469,473],\"type\":[0],\"current\":null},{\"pos\":[516,520],\"type\":[4],\"current\":null},{\"pos\":[526,531],\"type\":[4],\"current\":null},{\"pos\":[526,545],\"type\":[1,2],\"current\":null},{\"pos\":[540,545],\"type\":[1,2],\"current\":null},{\"pos\":[574,578],\"type\":[4],\"current\":null},{\"pos\":[574,584],\"type\":[1,2],\"current\":null}],\"name\":\"continueAfterWrite\",\"namePos\":[300,318],\"params\":[],\"result\":[1,2]}],\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[{\"refs\":{\"first\":[[\"value\",[1,2]]],\"rest\":[],\"views\":[]}}],[{\"arrs\":{\"arrows\":[{\"receiver\":[6],\"arguments\":[[0]],\"result\":[1,2],\"effect\":\"unrestricted\"}]}}],[\"top\"]],\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\"}").toOption.getD .null
private def continued := SourceClaimJson.extractGraphRequests continueAst continueClaims "verification/tests/stateful-source/loop-transfers.ts"
private def continueProgram : Program := [
  ⟨.nul,.effect 14,none⟩,
  ⟨.var 0,.ret,none⟩,
  ⟨.read (.var 0),.bind ⟨1,some [0, 2, 3]⟩,none⟩,
  ⟨.var 1,.bind 2,none⟩,
  ⟨.nul,.effect ⟨0,some [1, 2]⟩,none⟩,
  ⟨.var 0,.bind ⟨4,some [3, 4, 5]⟩,none⟩,
  ⟨.write (.var 1) (.var 0),.effect 5,none⟩,
  ⟨.fls,.bind 6,none⟩,
  ⟨.var 0,.bind 7,none⟩,
  ⟨.var 0,.effect 8,none⟩,
  ⟨.var 1,.bind 9,none⟩,
  ⟨.var 0,.branchBind ⟨10,some [2, 3]⟩ ⟨3,some [2, 3]⟩,none⟩,
  ⟨.app (.var 1) (.var 0),.bind ⟨11,some [0, 3, 4]⟩,none⟩,
  ⟨.nul,.bind 12,none⟩,
  ⟨.var 0,.bind 13,none⟩,
  ⟨.var 0,.effect 0,none⟩,
  ⟨.makeAt (.graph 1 [.var 0, .read (.var 0), .var 2]
      [(.ret, none), (.bind ⟨0, some [0, 2, 3, 4]⟩, none), (.bind ⟨1, none⟩, none)] 2 [.var 0])
      [codeField] [.nul],.bind 15,none⟩,
  ⟨.var 0,.effect 16,none⟩,
  ⟨.alloc (.var 0),.bind ⟨17,some [0]⟩,none⟩,
  ⟨.tru,.bind 18,none⟩,
  ⟨.nul,.effect 19,none⟩]
#guard ((continued.toOption.getD []).map (·.program)).headD [] == continueProgram
#guard ((continued.toOption.getD []).map (·.start)).headD 0 == 20

-- Continue drops the alias and returns to condition evaluation after the write.
theorem continue_retests : ∃ n, Execution continueProgram n []
    (.at 20 (fun _ => .nul)) [.fls,.nul] (.done .fls) := by
  apply Exists.intro
  run_machine
#print axioms continue_retests
end LoopTransfer

end Verification.Model.LoweringTraceTests
