import Verification.Source.SourceClaimJson
import Verification.Tests.ExecutionModelTests

/-! Lowered programs run by the machine. Each fixture is a source function of
`tests/stateful-source`, its parser document and its claims converted to
calculus labels; extraction lowers it without a producer, the lowered program
is pinned, and a trace runs it to the value JavaScript returns. No
source-to-graph preservation theorem exists, and a pipeline case does not
show these: the claims the producer states read the bindings involved at
their declared contracts, which a lowering that changed the order or the
cells would still meet. Each trace is of one lowered program, not a general
compiler proof. -/
namespace Verification.LoweringTraceTests
open Lean ProgramTyping SourceExtraction SourceClaimJson ControlFlow

/-! ## Declaration lists

A `let` list: one slot per declarator, in source order. -/
namespace DeclarationList
-- `laterWriteStaysSeparate` from tests/stateful-source/declaration-list.ts,
-- with source claims in calculus labels.
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/declaration-list.ts\",\"sourceSha256\":\"bdb1525a9aeb0f18e065db0cde90ee47e0d345b10bc09aab99bb5a14fc9a242e\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"laterWriteStaysSeparate\",\"namePos\":[469,492],\"strict\":false,\"typeParams\":[],\"params\":[{\"name\":\"seed\",\"pos\":[493,497],\"type\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]}}],\"retType\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":[{\"k\":\"let\",\"pos\":[528,597],\"bindings\":[{\"name\":\"first\",\"namePos\":[532,537],\"annot\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[556,560],\"name\":\"seed\"}},{\"name\":\"second\",\"namePos\":[566,572],\"annot\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[591,596],\"name\":\"first\"}}]},{\"k\":\"effect\",\"pos\":[600,613],\"e\":{\"k\":\"assign\",\"pos\":[600,612],\"name\":\"first\",\"namePos\":[600,605],\"rhs\":{\"k\":\"lit\",\"pos\":[608,612],\"lit\":{\"a\":\"null\"}}}},{\"k\":\"if\",\"pos\":[616,651],\"cond\":{\"k\":\"bin\",\"pos\":[620,635],\"op\":\"!==\",\"l\":{\"k\":\"id\",\"pos\":[620,626],\"name\":\"second\"},\"r\":{\"k\":\"lit\",\"pos\":[631,635],\"lit\":{\"a\":\"null\"}}},\"then\":[{\"k\":\"return\",\"pos\":[637,651],\"e\":{\"k\":\"id\",\"pos\":[644,650],\"name\":\"second\"}}],\"else_\":null},{\"k\":\"return\",\"pos\":[654,667],\"e\":{\"k\":\"lit\",\"pos\":[661,666],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/declaration-list.ts\",\"sourceSha256\":\"bdb1525a9aeb0f18e065db0cde90ee47e0d345b10bc09aab99bb5a14fc9a242e\",\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[\"num\"],[{\"numLit\":{\"bits\":\"4611686018427387904\"}}],[{\"numLit\":{\"bits\":\"4607182418800017408\"}}]],\"functions\":[{\"name\":\"laterWriteStaysSeparate\",\"namePos\":[469,492],\"params\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null}],\"result\":[1,2],\"entries\":[{\"start\":528,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null}],\"point\":\"469:492:6\"},{\"start\":600,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[0,1,2],\"current\":null}],\"point\":\"469:492:4\"},{\"start\":616,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[0,1,2],\"current\":null}],\"point\":\"469:492:3\"},{\"start\":637,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[1,2],\"current\":null}],\"point\":\"469:492:2\"},{\"start\":654,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null},{\"name\":\"second\",\"type\":[0,1,2],\"current\":null}],\"point\":\"469:492:1\"},{\"start\":528,\"bindings\":[{\"name\":\"seed\",\"type\":[0,1,2],\"current\":null},{\"name\":\"first\",\"type\":[0,1,2],\"current\":null}],\"point\":\"469:492:5\"}],\"expressions\":[{\"pos\":[556,560],\"type\":[0,1,2],\"current\":null,\"point\":\"469:492:6\"},{\"pos\":[591,596],\"type\":[0,1,2],\"current\":null,\"point\":\"469:492:5\"},{\"pos\":[600,612],\"type\":[0],\"current\":null,\"point\":\"469:492:4\"},{\"pos\":[608,612],\"type\":[0],\"current\":null,\"point\":\"469:492:4\"},{\"pos\":[620,635],\"type\":[1,2],\"current\":null,\"point\":\"469:492:3\"},{\"pos\":[620,626],\"type\":[0,1,2],\"current\":null,\"point\":\"469:492:3\"},{\"pos\":[631,635],\"type\":[0],\"current\":null,\"point\":\"469:492:3\"},{\"pos\":[644,650],\"type\":[1,2],\"current\":null,\"point\":\"469:492:2\"},{\"pos\":[661,666],\"type\":[2],\"current\":null,\"point\":\"469:492:1\"}],\"contracts\":[{\"pos\":[556,560],\"name\":\"first\",\"type\":[0,1,2]},{\"pos\":[591,596],\"name\":\"second\",\"type\":[0,1,2]}]}]}").toOption.getD .null
private def file := "verification/tests/stateful-source/declaration-list.ts"
private def extracted := SourceClaimJson.extractGraphRequests ast claims file
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0

-- The seed is the first slot's value, then the second's. Writing null to the
-- first rebinds its slot only; the second's non-null value or false is
-- returned. No cell is allocated: no closure sees either binding.
private def expected : Program :=
  [⟨.nul, .effect ⟨44, none⟩, none⟩,
   ⟨.nul, .effect ⟨40, none⟩, none⟩,
   ⟨.nul, .effect ⟨36, none⟩, none⟩,
   ⟨.nul, .effect ⟨28, none⟩, none⟩,
   ⟨.nul, .effect ⟨8, none⟩, none⟩,
   ⟨.var 0, .ret, none⟩,
   ⟨.var 0, .effect ⟨5, some [0, 1, 2, 3]⟩, none⟩,
   ⟨.var 0, .bind ⟨6, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.var 0, .bind ⟨7, none⟩, none⟩,
   ⟨.nul, .effect ⟨13, none⟩, none⟩,
   ⟨.var 0, .ret, none⟩,
   ⟨.var 0, .effect ⟨10, some [0, 1, 2, 3]⟩, none⟩,
   ⟨.var 0, .bind ⟨11, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.fls, .bind ⟨12, none⟩, none⟩,
   ⟨.var 4, .tagBind (.isNul) ⟨9, some [0, 6, 7]⟩ ⟨4, some [0, 6, 7]⟩, none⟩,
   ⟨.ite (.test (.isNul) (.var 1)) (.fls) (.tru), .bind ⟨14, some [0, 3, 4, 5, 6, 7, 8]⟩, none⟩,
   ⟨.var 2, .bind ⟨15, none⟩, none⟩,
   ⟨.var 3, .bind ⟨16, none⟩, none⟩,
   ⟨.var 0, .effect ⟨17, none⟩, none⟩,
   ⟨.var 0, .bind ⟨18, some [0, 2, 3, 4, 5, 6]⟩, none⟩,
   ⟨.ite (.test (.isNul) (.var 1)) (.fls) (.tru), .bind ⟨19, some [0, 3, 4, 5, 6, 7]⟩, none⟩,
   ⟨.var 1, .bind ⟨20, none⟩, none⟩,
   ⟨.var 1, .bind ⟨21, none⟩, none⟩,
   ⟨.var 0, .effect ⟨22, none⟩, none⟩,
   ⟨.var 0, .bind ⟨23, some [0, 2, 3, 4, 5]⟩, none⟩,
   ⟨.nul, .bind ⟨24, none⟩, none⟩,
   ⟨.var 0, .effect ⟨25, none⟩, none⟩,
   ⟨.var 0, .bind ⟨26, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.var 0, .bind ⟨27, none⟩, none⟩,
   ⟨.nul, .effect ⟨3, some [2, 3, 4]⟩, none⟩,
   ⟨.var 0, .effect ⟨29, none⟩, none⟩,
   ⟨.var 0, .bind ⟨30, some [0, 2, 3, 0, 5]⟩, none⟩,
   ⟨.var 0, .effect ⟨31, none⟩, none⟩,
   ⟨.var 0, .bind ⟨32, none⟩, none⟩,
   ⟨.var 0, .effect ⟨33, none⟩, none⟩,
   ⟨.var 0, .bind ⟨34, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.nul, .bind ⟨35, none⟩, none⟩,
   ⟨.var 0, .effect ⟨2, some [0, 1, 2]⟩, none⟩,
   ⟨.var 0, .effect ⟨37, some [0, 1, 2]⟩, none⟩,
   ⟨.var 0, .bind ⟨38, some [0, 2, 3]⟩, none⟩,
   ⟨.var 0, .bind ⟨39, none⟩, none⟩,
   ⟨.var 0, .effect ⟨1, some [0, 1]⟩, none⟩,
   ⟨.var 0, .effect ⟨41, some [0, 1]⟩, none⟩,
   ⟨.var 0, .bind ⟨42, some [0, 2]⟩, none⟩,
   ⟨.var 0, .bind ⟨43, none⟩, none⟩,
   ⟨.nul, .effect ⟨0, some [0]⟩, none⟩]
#guard program == expected
#guard start == 45

/-- The seed in slot zero, nothing else bound. -/
private def seeded (v : Tm) : Env := fun i => if i == 0 then v else .nul

-- The heap stays empty. After the run the second slot still holds the seed,
-- which a non-null seed returns.
theorem separate_slots (b : Bool) : ∃ n, Execution expected n []
    (.at 45 (seeded (if b then .tru else .fls)))
    [] (.done (if b then .tru else .fls)) := by
  cases b <;> apply Exists.intro <;> repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.testV rfl))
    | apply Execution.next (.expr (.iteC (.testV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.tagBind rfl)
    | apply Execution.next (.ret rfl)

#print axioms separate_slots
end DeclarationList

/-! ## Object patterns

An object pattern: the initializer held once, properties read in order, defaults run in pattern order for missing properties only. -/
namespace ObjectPattern
-- `orderedDefaults` from tests/stateful-source/object-patterns.ts, with its
-- source claims in calculus labels.
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/object-patterns.ts\",\"sourceSha256\":\"d72feb07e3ddd0aa162704a86dd42ed9e69531b6db8356dad19911a9e5d60567\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"orderedDefaults\",\"namePos\":[853,868],\"strict\":false,\"typeParams\":[],\"params\":[{\"name\":\"seed\",\"pos\":[869,873],\"type\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"number\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"undefined\",\"span\":[0,0]}],\"span\":[0,0]}}],\"retType\":{\"k\":\"atom\",\"name\":\"number\",\"span\":[0,0]},\"body\":[{\"k\":\"let\",\"pos\":[907,939],\"bindings\":[{\"name\":\"state\",\"namePos\":[911,916],\"annot\":{\"k\":\"union\",\"parts\":[{\"k\":\"atom\",\"name\":\"number\",\"span\":[0,0]},{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"span\":[0,0]},\"init\":{\"k\":\"lit\",\"pos\":[934,938],\"lit\":{\"a\":\"null\"}}}]},{\"k\":\"const\",\"pos\":[942,975],\"bindings\":[{\"name\":\"box\",\"namePos\":[948,951],\"annot\":null,\"init\":{\"k\":\"alloc\",\"pos\":[954,974],\"fields\":[{\"name\":\"a\",\"e\":{\"k\":\"id\",\"pos\":[959,963],\"name\":\"seed\"}},{\"name\":\"b\",\"e\":{\"k\":\"id\",\"pos\":[968,972],\"name\":\"seed\"}}]}}]},{\"k\":\"destructure\",\"pos\":[978,1034],\"target\":{\"k\":\"object\",\"pos\":[984,1027],\"props\":[{\"field\":\"a\",\"target\":{\"k\":\"name\",\"name\":\"first\",\"pos\":[989,994]},\"default_\":{\"k\":\"assign\",\"pos\":[997,1008],\"name\":\"state\",\"namePos\":[998,1003],\"rhs\":{\"k\":\"lit\",\"pos\":[1006,1007],\"lit\":{\"a\":\"numberlit\",\"v\":\"1\"}}}},{\"field\":\"b\",\"target\":{\"k\":\"name\",\"name\":\"b\",\"pos\":[1010,1011]},\"default_\":{\"k\":\"assign\",\"pos\":[1014,1025],\"name\":\"state\",\"namePos\":[1015,1020],\"rhs\":{\"k\":\"lit\",\"pos\":[1023,1024],\"lit\":{\"a\":\"numberlit\",\"v\":\"2\"}}}}],\"rest\":null},\"default_\":null,\"init\":{\"k\":\"id\",\"pos\":[1030,1033],\"name\":\"box\"}},{\"k\":\"return\",\"pos\":[1037,1055],\"e\":{\"k\":\"coalesce\",\"pos\":[1044,1054],\"left\":{\"k\":\"id\",\"pos\":[1044,1049],\"name\":\"state\"},\"right\":{\"k\":\"id\",\"pos\":[1053,1054],\"name\":\"b\"}}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/object-patterns.ts\",\"sourceSha256\":\"d72feb07e3ddd0aa162704a86dd42ed9e69531b6db8356dad19911a9e5d60567\",\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[\"num\"],[{\"refs\":{\"first\":[[\"value\",[3,4]]],\"rest\":[],\"views\":[]}}],[{\"numLit\":{\"bits\":\"0\"}}],[{\"refs\":{\"first\":[[\"value\",[4]]],\"rest\":[],\"views\":[]}}],[{\"refs\":{\"first\":[[\"a\",[3,4]],[\"b\",[3,4]]],\"rest\":[],\"views\":[]}}],[{\"numLit\":{\"bits\":\"4607182418800017408\"}}],[{\"numLit\":{\"bits\":\"4611686018427387904\"}}]],\"functions\":[{\"name\":\"orderedDefaults\",\"namePos\":[853,868],\"params\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null}],\"result\":[4],\"entries\":[{\"start\":907,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null}],\"point\":\"853:868:4\"},{\"start\":942,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null},{\"name\":\"state\",\"type\":[0,4],\"current\":null}],\"point\":\"853:868:3\"},{\"start\":978,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null},{\"name\":\"state\",\"type\":[0,4],\"current\":null},{\"name\":\"box\",\"type\":[8],\"current\":null}],\"point\":\"853:868:2\"},{\"start\":1037,\"bindings\":[{\"name\":\"seed\",\"type\":[3,4],\"current\":null},{\"name\":\"state\",\"type\":[0,4],\"current\":null},{\"name\":\"box\",\"type\":[8],\"current\":null},{\"name\":\"first\",\"type\":[4],\"current\":null},{\"name\":\"b\",\"type\":[4],\"current\":null}],\"point\":\"853:868:1\"}],\"expressions\":[{\"pos\":[934,938],\"type\":[0],\"current\":null,\"point\":\"853:868:4\"},{\"pos\":[954,974],\"type\":[8],\"current\":null,\"point\":\"853:868:3\"},{\"pos\":[959,963],\"type\":[3,4],\"current\":null,\"point\":\"853:868:3\"},{\"pos\":[968,972],\"type\":[3,4],\"current\":null,\"point\":\"853:868:3\"},{\"pos\":[997,1008],\"type\":[9],\"current\":null,\"point\":\"853:868:2\"},{\"pos\":[1006,1007],\"type\":[9],\"current\":null,\"point\":\"853:868:2\"},{\"pos\":[1014,1025],\"type\":[10],\"current\":null,\"point\":\"853:868:2\"},{\"pos\":[1023,1024],\"type\":[10],\"current\":null,\"point\":\"853:868:2\"},{\"pos\":[1030,1033],\"type\":[8],\"current\":null,\"point\":\"853:868:2\"},{\"pos\":[1044,1054],\"type\":[4],\"current\":null,\"point\":\"853:868:1\"},{\"pos\":[1044,1049],\"type\":[0,4],\"current\":null,\"point\":\"853:868:1\"},{\"pos\":[1053,1054],\"type\":[4],\"current\":null,\"point\":\"853:868:1\"},{\"pos\":[989,994],\"type\":[3,4],\"current\":null,\"point\":\"853:868:2\"},{\"pos\":[1010,1011],\"type\":[3,4],\"current\":null,\"point\":\"853:868:2\"}],\"contracts\":[{\"pos\":[934,938],\"name\":\"state\",\"type\":[0,4]}]}]}").toOption.getD .null
private def file := "verification/tests/stateful-source/object-patterns.ts"
private def extracted := SourceClaimJson.extractGraphRequests ast claims file
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0

-- The state cell and box are allocated before the object pattern runs.
-- Each property is read once, and its default runs only when undefined,
-- in the pattern's source order.
private def expected : Program :=
  [⟨.nul, .effect ⟨62, none⟩, none⟩,
   ⟨.nul, .effect ⟨57, none⟩, none⟩,
   ⟨.nul, .effect ⟨45, none⟩, none⟩,
   ⟨.nul, .effect ⟨15, none⟩, none⟩,
   ⟨.var 0, .ret, none⟩,
   ⟨.var 0, .effect ⟨4, some [0, 2, 3, 4, 5, 6]⟩, none⟩,
   ⟨.var 0, .effect ⟨5, none⟩, none⟩,
   ⟨.var 0, .bind ⟨6, some [0, 2, 3, 4, 5, 6, 7]⟩, none⟩,
   ⟨.var 1, .bind ⟨7, none⟩, none⟩,
   ⟨.var 0, .effect ⟨4, some [0, 2, 3, 4, 5, 6]⟩, none⟩,
   ⟨.var 0, .effect ⟨9, some [0, 1, 2, 3, 4, 5, 6]⟩, none⟩,
   ⟨.var 0, .bind ⟨10, none⟩, none⟩,
   ⟨.var 0, .tagBind
                       (.isNullish)
                       ⟨8, some [0, 2, 3, 4, 5, 6]⟩
                       ⟨11, some [0, 2, 3, 4, 5, 6]⟩, none⟩,
   ⟨.var 0, .effect ⟨12, none⟩, none⟩,
   ⟨.var 0, .bind ⟨13, some [0, 2, 3, 4, 5, 6]⟩, none⟩,
   ⟨.readAt (Verification.PropKey.str "value") (.var 3), .bind ⟨14, none⟩, none⟩,
   ⟨.nul, .effect ⟨3, some [0, 3, 7, 8, 9]⟩, none⟩,
   ⟨.var 0, .bind ⟨16, none⟩, none⟩,
   ⟨.var 0, .bind
                       ⟨17, some [0, 2, 3, 4, 5, 6, 7, 8, 9]⟩, none⟩,
   ⟨.var 0, .bind
                       ⟨17, some [0, 4, 5, 6, 7, 8, 9, 10, 11]⟩, none⟩,
   ⟨.var 0, .effect ⟨19, none⟩, none⟩,
   ⟨.var 0, .bind
                       ⟨20, some [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]⟩, none⟩,
   ⟨.var 0, .bind
                       ⟨21, some [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]⟩, none⟩,
   ⟨.writeAt
                     (Verification.PropKey.str "value")
                     (.var 9)
                     (.var 0), .effect ⟨22, none⟩, none⟩,
   ⟨.var 0, .bind ⟨23, none⟩, none⟩,
   ⟨.var 0, .effect ⟨24, none⟩, none⟩,
   ⟨.var 0, .bind
                       ⟨25, some [0, 2, 3, 4, 5, 6, 7, 8, 9, 10]⟩, none⟩,
   ⟨.num 4611686018427387904, .bind ⟨26, none⟩, none⟩,
   ⟨.var 0, .tagBind
                       (.isUndef)
                       ⟨27, none⟩
                       ⟨18, none⟩, none⟩,
   ⟨.readAt (Verification.PropKey.str "b") (.var 3), .bind ⟨28, none⟩, none⟩,
   ⟨.var 0, .bind ⟨29, none⟩, none⟩,
   ⟨.var 0, .bind ⟨30, some [0, 2, 3, 4, 5, 6]⟩, none⟩,
   ⟨.var 0, .bind ⟨30, some [0, 4, 5, 6, 7, 8]⟩, none⟩,
   ⟨.var 0, .effect ⟨32, none⟩, none⟩,
   ⟨.var 0, .bind ⟨33, some [0, 2, 3, 4, 5, 6, 7, 8]⟩, none⟩,
   ⟨.var 0, .bind ⟨34, some [0, 2, 3, 4, 5, 6, 7, 8]⟩, none⟩,
   ⟨.writeAt
                     (Verification.PropKey.str "value")
                     (.var 6)
                     (.var 0), .effect ⟨35, none⟩, none⟩,
   ⟨.var 0, .bind ⟨36, none⟩, none⟩,
   ⟨.var 0, .effect ⟨37, none⟩, none⟩,
   ⟨.var 0, .bind ⟨38, some [0, 2, 3, 4, 5, 6, 7]⟩, none⟩,
   ⟨.num 4607182418800017408, .bind ⟨39, none⟩, none⟩,
   ⟨.var 0, .tagBind
                       (.isUndef)
                       ⟨40, none⟩
                       ⟨31, none⟩, none⟩,
   ⟨.readAt (Verification.PropKey.str "a") (.var 0), .bind ⟨41, none⟩, none⟩,
   ⟨.var 0, .effect ⟨42, none⟩, none⟩,
   ⟨.var 0, .bind ⟨43, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.var 0, .bind ⟨44, none⟩, none⟩,
   ⟨.var 0, .effect ⟨2, some [0, 1, 2]⟩, none⟩,
   ⟨.var 0, .effect ⟨46, some [0, 3, 4]⟩, none⟩,
   ⟨.var 0, .bind ⟨47, some [0, 2, 3, 4, 5]⟩, none⟩,
   ⟨.makeAt
                     (Verification.CallCode.absent)
                     [Verification.PropKey.str "a", Verification.PropKey.str "b"]
                     [.var 1, .var 0], .bind ⟨48, some [0, 3, 4, 5, 6]⟩, none⟩,
   ⟨.var 1, .bind ⟨49, none⟩, none⟩,
   ⟨.var 1, .bind ⟨50, none⟩, none⟩,
   ⟨.var 0, .effect ⟨51, none⟩, none⟩,
   ⟨.var 0, .bind ⟨52, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.var 2, .bind ⟨53, none⟩, none⟩,
   ⟨.var 0, .effect ⟨54, none⟩, none⟩,
   ⟨.var 0, .bind ⟨55, some [0, 2, 3]⟩, none⟩,
   ⟨.var 1, .bind ⟨56, none⟩, none⟩,
   ⟨.makeAt
                     (Verification.CallCode.absent)
                     [Verification.PropKey.str "value"]
                     [.var 0], .bind ⟨1, some [0, 2]⟩, none⟩,
   ⟨.var 0, .effect ⟨58, none⟩, none⟩,
   ⟨.var 0, .effect ⟨59, some [0, 1]⟩, none⟩,
   ⟨.var 0, .bind ⟨60, some [0, 2]⟩, none⟩,
   ⟨.nul, .bind ⟨61, none⟩, none⟩,
   ⟨.nul, .effect ⟨0, some [0]⟩, none⟩]
#guard program == expected
#guard start == 63

/-- The seed in slot zero, nothing else bound. -/
private def seeded (v : Tm) : Env := fun i => if i == 0 then v else .nul

-- The heap holds the state cell, then the box's `a` and `b` locations, each
-- object followed by its identity. With
-- both fields undefined, both defaults run in pattern order: the state cell
-- ends at 2, which is returned.
theorem both_defaults_in_order : ∃ n, Execution expected n []
    (.at 63 (seeded .undef))
    [.num 4611686018427387904, .nul, .undef, .undef, .nul] (.done (.num 4611686018427387904)) := by
  apply Exists.intro
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeFields (by decide) rfl))
    | apply Execution.next (.expr (.readField rfl rfl))
    | apply Execution.next (.expr (.writeField rfl rfl (by decide)))
    | apply Execution.next (.expr (.letC (.readField rfl rfl)))
    | apply Execution.next (.expr (.letV rfl))
    | apply Execution.next (.expr (.testV rfl))
    | apply Execution.next (.expr (.iteC (.testV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.tagBind rfl)
    | apply Execution.next (.ret rfl)

-- With both fields present neither default runs: the state cell stays null
-- and the read of `b`, the seed, is returned.
theorem no_default_runs : ∃ n, Execution expected n []
    (.at 63 (seeded (.num 4617315517961601024)))
    [.nul, .nul, .num 4617315517961601024, .num 4617315517961601024, .nul]
    (.done (.num 4617315517961601024)) := by
  apply Exists.intro
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeFields (by decide) rfl))
    | apply Execution.next (.expr (.readField rfl rfl))
    | apply Execution.next (.expr (.writeField rfl rfl (by decide)))
    | apply Execution.next (.expr (.letC (.readField rfl rfl)))
    | apply Execution.next (.expr (.letV rfl))
    | apply Execution.next (.expr (.testV rfl))
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
-- `oneWrite` from tests/stateful-source/loops.ts, with source claims
-- in calculus labels.
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loops.ts\",\"sourceSha256\":\"f891442e6d46faf1d517584d6d1824899f4bc43d07304b743b57fd71077982de\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"oneWrite\",\"namePos\":[126,134],\"strict\":false,\"typeParams\":[],\"params\":[],\"retType\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":[{\"k\":\"const\",\"pos\":[150,199],\"bindings\":[{\"name\":\"cell\",\"namePos\":[156,160],\"annot\":{\"k\":\"object\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"readonly\":false,\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]}],\"stringIndex\":null,\"calls\":[],\"span\":[0,0]},\"init\":{\"k\":\"alloc\",\"pos\":[183,198],\"fields\":[{\"name\":\"value\",\"e\":{\"k\":\"lit\",\"pos\":[192,196],\"lit\":{\"a\":\"booleanlit\",\"v\":\"true\"}}}]}}]},{\"k\":\"const\",\"pos\":[202,270],\"bindings\":[{\"name\":\"test\",\"namePos\":[208,212],\"annot\":{\"k\":\"function\",\"effect\":\"unrestricted\",\"receiver\":null,\"params\":[{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"rest\":null,\"result\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]},\"init\":{\"k\":\"lambda\",\"pos\":[237,269],\"result\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":{\"k\":\"read\",\"pos\":[259,269],\"e\":{\"k\":\"id\",\"pos\":[259,263],\"name\":\"cell\"},\"field\":\"value\"},\"params\":[{\"name\":\"x\",\"type\":{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}}]}}]},{\"k\":\"while\",\"pos\":[273,366],\"cond\":{\"k\":\"apply\",\"pos\":[280,290],\"callee\":{\"k\":\"id\",\"pos\":[280,284],\"name\":\"test\"},\"args\":[{\"k\":\"lit\",\"pos\":[285,289],\"lit\":{\"a\":\"null\"}}]},\"body\":[{\"k\":\"const\",\"pos\":[298,337],\"bindings\":[{\"name\":\"alias\",\"namePos\":[304,309],\"annot\":{\"k\":\"object\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"readonly\":false,\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]}],\"stringIndex\":null,\"calls\":[],\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[332,336],\"name\":\"cell\"}}]},{\"k\":\"effect\",\"pos\":[342,362],\"e\":{\"k\":\"write\",\"pos\":[342,361],\"receiver\":{\"k\":\"id\",\"pos\":[342,347],\"name\":\"alias\"},\"rhs\":{\"k\":\"lit\",\"pos\":[356,361],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}},\"field\":\"value\"}}],\"update\":[]},{\"k\":\"return\",\"pos\":[369,387],\"e\":{\"k\":\"read\",\"pos\":[376,386],\"e\":{\"k\":\"id\",\"pos\":[376,380],\"name\":\"cell\"},\"field\":\"value\"}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loops.ts\",\"functions\":[{\"entries\":[{\"bindings\":[],\"start\":150,\"point\":\"126:134:6\"},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null}],\"start\":202,\"point\":\"126:134:5\"},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":273,\"point\":\"126:134:2\"},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":298,\"point\":\"126:134:4\"},{\"bindings\":[{\"name\":\"alias\",\"type\":[4],\"current\":null},{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":342,\"point\":\"126:134:3\"},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":369,\"point\":\"126:134:1\"}],\"expressions\":[{\"pos\":[183,198],\"type\":[4],\"current\":null,\"point\":\"126:134:6\"},{\"pos\":[192,196],\"type\":[1],\"current\":null,\"point\":\"126:134:6\"},{\"pos\":[237,269],\"type\":[5],\"current\":null,\"point\":\"126:134:5\"},{\"pos\":[259,263],\"type\":[4],\"current\":null,\"point\":\"259:269:1\"},{\"pos\":[259,269],\"type\":[1,2],\"current\":null,\"point\":\"259:269:1\"},{\"pos\":[280,284],\"type\":[5],\"current\":null,\"point\":\"126:134:2\"},{\"pos\":[280,290],\"type\":[1,2],\"current\":null,\"point\":\"126:134:2\"},{\"pos\":[285,289],\"type\":[0],\"current\":null,\"point\":\"126:134:2\"},{\"pos\":[332,336],\"type\":[4],\"current\":null,\"point\":\"126:134:4\"},{\"pos\":[342,347],\"type\":[4],\"current\":null,\"point\":\"126:134:3\"},{\"pos\":[342,361],\"type\":[1,2],\"current\":null,\"point\":\"126:134:3\"},{\"pos\":[356,361],\"type\":[1,2],\"current\":null,\"point\":\"126:134:3\"},{\"pos\":[376,380],\"type\":[4],\"current\":null,\"point\":\"126:134:1\"},{\"pos\":[376,386],\"type\":[1,2],\"current\":null,\"point\":\"126:134:1\"}],\"name\":\"oneWrite\",\"namePos\":[126,134],\"params\":[],\"result\":[1,2],\"contracts\":[]}],\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[{\"refs\":{\"first\":[[\"value\",[1,2]]],\"rest\":[],\"views\":[]}}],[{\"arrs\":{\"arrows\":[{\"receiver\":[6],\"arguments\":[[0]],\"result\":[1,2],\"effect\":\"unrestricted\"}]}}],[\"top\"]],\"sourceSha256\":\"f891442e6d46faf1d517584d6d1824899f4bc43d07304b743b57fd71077982de\"}").toOption.getD .null
private def extracted := SourceClaimJson.extractGraphRequests ast claims "verification/tests/stateful-source/loops.ts"
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0
private def expected : Program :=
  [⟨.nul, .effect ⟨54, none⟩, none⟩,
   ⟨.nul, .effect ⟨46, none⟩, none⟩,
   ⟨.nul, .effect ⟨42, none⟩, none⟩,
   ⟨.nul, .effect ⟨21, none⟩, none⟩,
   ⟨.nul, .effect ⟨17, none⟩, none⟩,
   ⟨.nul, .effect ⟨2, some [4, 5]⟩, none⟩,
   ⟨.var 0, .effect ⟨5, none⟩, none⟩,
   ⟨.var 0, .bind ⟨6, some [0, 2, 3, 4, 5, 6]⟩, none⟩,
   ⟨.var 0, .bind ⟨7, some [0, 3, 4, 5, 6, 7]⟩, none⟩,
   ⟨.writeAt
                     (Verification.PropKey.str "value")
                     (.var 1)
                     (.var 0), .effect ⟨8, none⟩, none⟩,
   ⟨.var 1, .bind ⟨9, none⟩, none⟩,
   ⟨.var 1, .bind ⟨10, none⟩, none⟩,
   ⟨.var 0, .effect ⟨11, none⟩, none⟩,
   ⟨.var 0, .bind ⟨12, some [0, 2, 3, 4, 5]⟩, none⟩,
   ⟨.fls, .bind ⟨13, none⟩, none⟩,
   ⟨.var 0, .effect ⟨14, none⟩, none⟩,
   ⟨.var 0, .bind ⟨15, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.var 0, .bind ⟨16, none⟩, none⟩,
   ⟨.var 0, .effect ⟨4, some [0, 1, 2]⟩, none⟩,
   ⟨.var 0, .effect ⟨18, some [0, 1, 2]⟩, none⟩,
   ⟨.var 0, .bind ⟨19, some [0, 2, 3]⟩, none⟩,
   ⟨.var 1, .bind ⟨20, none⟩, none⟩,
   ⟨.nul, .effect ⟨30, none⟩, none⟩,
   ⟨.var 0, .ret, none⟩,
   ⟨.var 0, .effect ⟨23, some [0, 2, 3]⟩, none⟩,
   ⟨.var 0, .bind ⟨24, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.readAt (Verification.PropKey.str "value") (.var 0), .bind ⟨25, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.var 0, .bind ⟨26, none⟩, none⟩,
   ⟨.var 0, .effect ⟨27, none⟩, none⟩,
   ⟨.var 0, .bind ⟨28, some [0, 2, 3]⟩, none⟩,
   ⟨.var 1, .bind ⟨29, none⟩, none⟩,
   ⟨.var 0, .tagBind
                       (.truthy)
                       ⟨3, some [4, 5]⟩
                       ⟨22, some [4, 5]⟩, none⟩,
   ⟨.var 0, .effect ⟨31, none⟩, none⟩,
   ⟨.var 0, .bind ⟨32, some [0, 2, 3, 4, 5]⟩, none⟩,
   ⟨.invoke (.var 1) (.undef) [.var 0], .bind ⟨33, some [0, 3, 4, 5, 6]⟩, none⟩,
   ⟨.var 1, .bind ⟨34, none⟩, none⟩,
   ⟨.var 1, .bind ⟨35, none⟩, none⟩,
   ⟨.var 0, .effect ⟨36, none⟩, none⟩,
   ⟨.var 0, .bind ⟨37, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.nul, .bind ⟨38, none⟩, none⟩,
   ⟨.var 0, .effect ⟨39, none⟩, none⟩,
   ⟨.var 0, .bind ⟨40, some [0, 2, 3]⟩, none⟩,
   ⟨.var 0, .bind ⟨41, none⟩, none⟩,
   ⟨.var 0, .effect ⟨2, some [0, 1]⟩, none⟩,
   ⟨.var 0, .effect ⟨43, some [0, 1]⟩, none⟩,
   ⟨.var 0, .bind ⟨44, some [0, 2]⟩, none⟩,
   ⟨.makeAt
                     (Verification.CallCode.graph
                       1
                       [.var 0,
                        .var 0,
                        .var 0,
                        .readAt (Verification.PropKey.str "value") (.var 0),
                        .var 0,
                        .var 0,
                        .var 0,
                        .var 2]
                       [(.ret, none),
                        (.effect ⟨0, some [0, 2, 3, 4]⟩, none),
                        (.bind ⟨1, some [0, 2, 3, 4, 5]⟩,
                         none),
                        (.bind ⟨2, some [0, 2, 3, 4, 5]⟩,
                         none),
                        (.bind ⟨3, none⟩, none),
                        (.effect ⟨4, none⟩, none),
                        (.bind ⟨5, some [0, 2, 3, 4]⟩, none),
                        (.bind ⟨6, none⟩, none)]
                       7
                       [.var 0]
                       (Verification.Invoke.call)
                       false)
                     [Verification.PropKey.str "[[code]]"]
                     [.nul], .bind ⟨45, none⟩, none⟩,
   ⟨.var 0, .effect ⟨1, some [0]⟩, none⟩,
   ⟨.var 0, .effect ⟨47, some [0]⟩, none⟩,
   ⟨.var 0, .bind ⟨48, some [0, 2]⟩, none⟩,
   ⟨.makeAt
                     (Verification.CallCode.absent)
                     [Verification.PropKey.str "value"]
                     [.var 0], .bind ⟨49, some [0, 2]⟩, none⟩,
   ⟨.var 0, .bind ⟨50, none⟩, none⟩,
   ⟨.var 0, .effect ⟨51, none⟩, none⟩,
   ⟨.var 0, .bind ⟨52, some [0]⟩, none⟩,
   ⟨.tru, .bind ⟨53, none⟩, none⟩,
   ⟨.nul, .effect ⟨0, some []⟩, none⟩]
#guard program == expected
#guard start == 55

-- The condition is called twice: true before the write and false afterwards.
-- The alias local is dropped on the back edge; the original closure and cell
-- remain in the correct slots.
theorem one_iteration : ∃ n, Execution expected n []
    (.at 55 (fun _ => .nul)) [.fls,.nul,.nul,.nul] (.done .fls) := by
  apply Exists.intro
  run_machine

#print axioms one_iteration
end While

/-! ## Loop transfers

`break` and `continue`: the nearest loop's exit, and the retest after the body's write. -/
namespace LoopTransfer
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"nestedBreak\",\"namePos\":[598,609],\"strict\":false,\"typeParams\":[],\"params\":[{\"name\":\"flag\",\"pos\":[610,614],\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]}}],\"retType\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":[{\"k\":\"while\",\"pos\":[638,746],\"cond\":{\"k\":\"id\",\"pos\":[645,649],\"name\":\"flag\"},\"body\":[{\"k\":\"while\",\"pos\":[657,725],\"cond\":{\"k\":\"id\",\"pos\":[664,668],\"name\":\"flag\"},\"body\":[{\"k\":\"const\",\"pos\":[678,706],\"bindings\":[{\"name\":\"local\",\"namePos\":[684,689],\"annot\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[701,705],\"name\":\"flag\"}}]},{\"k\":\"break\",\"pos\":[713,719],\"label\":null}],\"update\":[]},{\"k\":\"return\",\"pos\":[730,742],\"e\":{\"k\":\"lit\",\"pos\":[737,741],\"lit\":{\"a\":\"booleanlit\",\"v\":\"true\"}}}],\"update\":[]},{\"k\":\"return\",\"pos\":[749,762],\"e\":{\"k\":\"lit\",\"pos\":[756,761],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"functions\":[{\"entries\":[{\"bindings\":[{\"name\":\"flag\",\"type\":[1,2],\"current\":null}],\"start\":638,\"point\":\"598:609:2\"},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null}],\"start\":657,\"point\":\"598:609:4\"},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null}],\"start\":678,\"point\":\"598:609:6\"},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null},{\"name\":\"local\",\"type\":[1,2],\"current\":null}],\"start\":713,\"point\":\"598:609:5\"},{\"bindings\":[{\"name\":\"flag\",\"type\":[1],\"current\":null}],\"start\":730,\"point\":\"598:609:3\"},{\"bindings\":[{\"name\":\"flag\",\"type\":[1,2],\"current\":null}],\"start\":749,\"point\":\"598:609:1\"}],\"expressions\":[{\"pos\":[645,649],\"type\":[1,2],\"current\":null,\"point\":\"598:609:2\"},{\"pos\":[664,668],\"type\":[1],\"current\":null,\"point\":\"598:609:4\"},{\"pos\":[701,705],\"type\":[1],\"current\":null,\"point\":\"598:609:6\"},{\"pos\":[737,741],\"type\":[1],\"current\":null,\"point\":\"598:609:3\"},{\"pos\":[756,761],\"type\":[2],\"current\":null,\"point\":\"598:609:1\"}],\"name\":\"nestedBreak\",\"namePos\":[598,609],\"params\":[{\"name\":\"flag\",\"type\":[1,2],\"current\":null}],\"result\":[1,2],\"contracts\":[]}],\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[{\"refs\":{\"first\":[[\"value\",[1,2]]],\"rest\":[],\"views\":[]}}],[{\"arrs\":{\"arrows\":[{\"receiver\":[6],\"arguments\":[[0]],\"result\":[1,2],\"effect\":\"unrestricted\"}]}}],[\"top\"]],\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\"}").toOption.getD .null
private def extracted := SourceClaimJson.extractGraphRequests ast claims "verification/tests/stateful-source/loop-transfers.ts"
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0
private def expected : Program :=
  [⟨.nul, .effect ⟨27, none⟩, none⟩,
   ⟨.nul, .effect ⟨17, none⟩, none⟩,
   ⟨.nul, .effect ⟨13, none⟩, none⟩,
   ⟨.nul, .effect ⟨9, none⟩, none⟩,
   ⟨.nul, .effect ⟨8, none⟩, none⟩,
   ⟨.var 0, .ret, none⟩,
   ⟨.var 0, .effect ⟨5, some [0, 1]⟩, none⟩,
   ⟨.var 0, .bind ⟨6, some [0, 2]⟩, none⟩,
   ⟨.tru, .bind ⟨7, none⟩, none⟩,
   ⟨.nul, .effect ⟨4, some [1]⟩, none⟩,
   ⟨.var 0, .effect ⟨3, some [0, 1]⟩, none⟩,
   ⟨.var 0, .effect ⟨10, some [0, 1]⟩, none⟩,
   ⟨.var 0, .bind ⟨11, some [0, 2]⟩, none⟩,
   ⟨.var 0, .bind ⟨12, none⟩, none⟩,
   ⟨.var 0, .effect ⟨2, some [1]⟩, none⟩,
   ⟨.var 0, .effect ⟨14, none⟩, none⟩,
   ⟨.var 0, .bind ⟨15, some [0, 2]⟩, none⟩,
   ⟨.var 0, .bind ⟨16, none⟩, none⟩,
   ⟨.nul, .effect ⟨22, none⟩, none⟩,
   ⟨.var 0, .ret, none⟩,
   ⟨.var 0, .effect ⟨19, some [0, 1]⟩, none⟩,
   ⟨.var 0, .bind ⟨20, some [0, 2]⟩, none⟩,
   ⟨.fls, .bind ⟨21, none⟩, none⟩,
   ⟨.var 0, .branchBind
                       ⟨1, some [0]⟩
                       ⟨18, some [0]⟩, none⟩,
   ⟨.var 1, .bind ⟨23, none⟩, none⟩,
   ⟨.var 0, .effect ⟨24, none⟩, none⟩,
   ⟨.var 0, .bind ⟨25, some [0, 2]⟩, none⟩,
   ⟨.var 0, .bind ⟨26, none⟩, none⟩,
   ⟨.nul, .effect ⟨0, some [0]⟩, none⟩]
#guard program == expected
#guard start == 28

-- Breaking the inner loop reaches the outer body's return true, rather than
-- the outer loop's false exit. The inner local is dropped at the transfer.
theorem nearest_break (b : Bool) : ∃ n, Execution expected n []
    (.at 28 (fun _ => if b then .tru else .fls)) [] (.done (if b then .tru else .fls)) := by
  cases b <;> apply Exists.intro <;> repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next .yesBind
    | apply Execution.next .noBind
    | apply Execution.next (.ret rfl)

#print axioms nearest_break

private def continueAst : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\",\"declarations\":{\"roots\":[],\"definitions\":[],\"values\":[],\"symbols\":[]},\"init\":[],\"functions\":[{\"name\":\"continueAfterWrite\",\"namePos\":[300,318],\"strict\":false,\"typeParams\":[],\"params\":[],\"retType\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":[{\"k\":\"const\",\"pos\":[334,383],\"bindings\":[{\"name\":\"cell\",\"namePos\":[340,344],\"annot\":{\"k\":\"object\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"readonly\":false,\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]}],\"stringIndex\":null,\"calls\":[],\"span\":[0,0]},\"init\":{\"k\":\"alloc\",\"pos\":[367,382],\"fields\":[{\"name\":\"value\",\"e\":{\"k\":\"lit\",\"pos\":[376,380],\"lit\":{\"a\":\"booleanlit\",\"v\":\"true\"}}}]}}]},{\"k\":\"const\",\"pos\":[386,454],\"bindings\":[{\"name\":\"test\",\"namePos\":[392,396],\"annot\":{\"k\":\"function\",\"effect\":\"unrestricted\",\"receiver\":null,\"params\":[{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}],\"rest\":null,\"result\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]},\"init\":{\"k\":\"lambda\",\"pos\":[421,453],\"result\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"body\":{\"k\":\"read\",\"pos\":[443,453],\"e\":{\"k\":\"id\",\"pos\":[443,447],\"name\":\"cell\"},\"field\":\"value\"},\"params\":[{\"name\":\"x\",\"type\":{\"k\":\"atom\",\"name\":\"null\",\"span\":[0,0]}}]}}]},{\"k\":\"while\",\"pos\":[457,564],\"cond\":{\"k\":\"apply\",\"pos\":[464,474],\"callee\":{\"k\":\"id\",\"pos\":[464,468],\"name\":\"test\"},\"args\":[{\"k\":\"lit\",\"pos\":[469,473],\"lit\":{\"a\":\"null\"}}]},\"body\":[{\"k\":\"const\",\"pos\":[482,521],\"bindings\":[{\"name\":\"alias\",\"namePos\":[488,493],\"annot\":{\"k\":\"object\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"readonly\":false,\"type\":{\"k\":\"atom\",\"name\":\"boolean\",\"span\":[0,0]},\"span\":[0,0]}],\"stringIndex\":null,\"calls\":[],\"span\":[0,0]},\"init\":{\"k\":\"id\",\"pos\":[516,520],\"name\":\"cell\"}}]},{\"k\":\"effect\",\"pos\":[526,546],\"e\":{\"k\":\"write\",\"pos\":[526,545],\"receiver\":{\"k\":\"id\",\"pos\":[526,531],\"name\":\"alias\"},\"rhs\":{\"k\":\"lit\",\"pos\":[540,545],\"lit\":{\"a\":\"booleanlit\",\"v\":\"false\"}},\"field\":\"value\"}},{\"k\":\"continue\",\"pos\":[551,560]}],\"update\":[]},{\"k\":\"return\",\"pos\":[567,585],\"e\":{\"k\":\"read\",\"pos\":[574,584],\"e\":{\"k\":\"id\",\"pos\":[574,578],\"name\":\"cell\"},\"field\":\"value\"}}]}]}").toOption.getD .null
private def continueClaims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/loop-transfers.ts\",\"functions\":[{\"entries\":[{\"bindings\":[],\"start\":334,\"point\":\"300:318:7\"},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null}],\"start\":386,\"point\":\"300:318:6\"},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":457,\"point\":\"300:318:2\"},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":482,\"point\":\"300:318:5\"},{\"bindings\":[{\"name\":\"alias\",\"type\":[4],\"current\":null},{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":526,\"point\":\"300:318:4\"},{\"bindings\":[{\"name\":\"alias\",\"type\":[4],\"current\":null},{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":551,\"point\":\"300:318:3\"},{\"bindings\":[{\"name\":\"cell\",\"type\":[4],\"current\":null},{\"name\":\"test\",\"type\":[5],\"current\":null}],\"start\":567,\"point\":\"300:318:1\"}],\"expressions\":[{\"pos\":[367,382],\"type\":[4],\"current\":null,\"point\":\"300:318:7\"},{\"pos\":[376,380],\"type\":[1],\"current\":null,\"point\":\"300:318:7\"},{\"pos\":[421,453],\"type\":[5],\"current\":null,\"point\":\"300:318:6\"},{\"pos\":[443,447],\"type\":[4],\"current\":null,\"point\":\"443:453:1\"},{\"pos\":[443,453],\"type\":[1,2],\"current\":null,\"point\":\"443:453:1\"},{\"pos\":[464,468],\"type\":[5],\"current\":null,\"point\":\"300:318:2\"},{\"pos\":[464,474],\"type\":[1,2],\"current\":null,\"point\":\"300:318:2\"},{\"pos\":[469,473],\"type\":[0],\"current\":null,\"point\":\"300:318:2\"},{\"pos\":[516,520],\"type\":[4],\"current\":null,\"point\":\"300:318:5\"},{\"pos\":[526,531],\"type\":[4],\"current\":null,\"point\":\"300:318:4\"},{\"pos\":[526,545],\"type\":[1,2],\"current\":null,\"point\":\"300:318:4\"},{\"pos\":[540,545],\"type\":[1,2],\"current\":null,\"point\":\"300:318:4\"},{\"pos\":[574,578],\"type\":[4],\"current\":null,\"point\":\"300:318:1\"},{\"pos\":[574,584],\"type\":[1,2],\"current\":null,\"point\":\"300:318:1\"}],\"name\":\"continueAfterWrite\",\"namePos\":[300,318],\"params\":[],\"result\":[1,2],\"contracts\":[]}],\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[{\"refs\":{\"first\":[[\"value\",[1,2]]],\"rest\":[],\"views\":[]}}],[{\"arrs\":{\"arrows\":[{\"receiver\":[6],\"arguments\":[[0]],\"result\":[1,2],\"effect\":\"unrestricted\"}]}}],[\"top\"]],\"sourceSha256\":\"3e7de21dc2e672fbff32a2035752cc08e68fb99770355c72a4b476b00950cdb9\"}").toOption.getD .null
private def continued := SourceClaimJson.extractGraphRequests continueAst continueClaims "verification/tests/stateful-source/loop-transfers.ts"
private def continueProgram : Program :=
  [⟨.nul, .effect ⟨56, none⟩, none⟩,
   ⟨.nul, .effect ⟨48, none⟩, none⟩,
   ⟨.nul, .effect ⟨44, none⟩, none⟩,
   ⟨.nul, .effect ⟨23, none⟩, none⟩,
   ⟨.nul, .effect ⟨19, none⟩, none⟩,
   ⟨.nul, .effect ⟨6, none⟩, none⟩,
   ⟨.nul, .effect ⟨2, some [1, 2]⟩, none⟩,
   ⟨.nul, .effect ⟨5, some [3, 4, 5]⟩, none⟩,
   ⟨.var 0, .effect ⟨7, none⟩, none⟩,
   ⟨.var 0, .bind ⟨8, some [0, 2, 3, 4, 5, 6]⟩, none⟩,
   ⟨.var 0, .bind ⟨9, some [0, 3, 4, 5, 6, 7]⟩, none⟩,
   ⟨.writeAt
                     (Verification.PropKey.str "value")
                     (.var 1)
                     (.var 0), .effect ⟨10, none⟩, none⟩,
   ⟨.var 1, .bind ⟨11, none⟩, none⟩,
   ⟨.var 1, .bind ⟨12, none⟩, none⟩,
   ⟨.var 0, .effect ⟨13, none⟩, none⟩,
   ⟨.var 0, .bind ⟨14, some [0, 2, 3, 4, 5]⟩, none⟩,
   ⟨.fls, .bind ⟨15, none⟩, none⟩,
   ⟨.var 0, .effect ⟨16, none⟩, none⟩,
   ⟨.var 0, .bind ⟨17, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.var 0, .bind ⟨18, none⟩, none⟩,
   ⟨.var 0, .effect ⟨4, some [0, 1, 2]⟩, none⟩,
   ⟨.var 0, .effect ⟨20, some [0, 1, 2]⟩, none⟩,
   ⟨.var 0, .bind ⟨21, some [0, 2, 3]⟩, none⟩,
   ⟨.var 1, .bind ⟨22, none⟩, none⟩,
   ⟨.nul, .effect ⟨32, none⟩, none⟩,
   ⟨.var 0, .ret, none⟩,
   ⟨.var 0, .effect ⟨25, some [0, 2, 3]⟩, none⟩,
   ⟨.var 0, .bind ⟨26, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.readAt (Verification.PropKey.str "value") (.var 0), .bind ⟨27, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.var 0, .bind ⟨28, none⟩, none⟩,
   ⟨.var 0, .effect ⟨29, none⟩, none⟩,
   ⟨.var 0, .bind ⟨30, some [0, 2, 3]⟩, none⟩,
   ⟨.var 1, .bind ⟨31, none⟩, none⟩,
   ⟨.var 0, .tagBind
                       (.truthy)
                       ⟨3, some [4, 5]⟩
                       ⟨24, some [4, 5]⟩, none⟩,
   ⟨.var 0, .effect ⟨33, none⟩, none⟩,
   ⟨.var 0, .bind ⟨34, some [0, 2, 3, 4, 5]⟩, none⟩,
   ⟨.invoke (.var 1) (.undef) [.var 0], .bind ⟨35, some [0, 3, 4, 5, 6]⟩, none⟩,
   ⟨.var 1, .bind ⟨36, none⟩, none⟩,
   ⟨.var 1, .bind ⟨37, none⟩, none⟩,
   ⟨.var 0, .effect ⟨38, none⟩, none⟩,
   ⟨.var 0, .bind ⟨39, some [0, 2, 3, 4]⟩, none⟩,
   ⟨.nul, .bind ⟨40, none⟩, none⟩,
   ⟨.var 0, .effect ⟨41, none⟩, none⟩,
   ⟨.var 0, .bind ⟨42, some [0, 2, 3]⟩, none⟩,
   ⟨.var 0, .bind ⟨43, none⟩, none⟩,
   ⟨.var 0, .effect ⟨2, some [0, 1]⟩, none⟩,
   ⟨.var 0, .effect ⟨45, some [0, 1]⟩, none⟩,
   ⟨.var 0, .bind ⟨46, some [0, 2]⟩, none⟩,
   ⟨.makeAt
                     (Verification.CallCode.graph
                       1
                       [.var 0,
                        .var 0,
                        .var 0,
                        .readAt (Verification.PropKey.str "value") (.var 0),
                        .var 0,
                        .var 0,
                        .var 0,
                        .var 2]
                       [(.ret, none),
                        (.effect ⟨0, some [0, 2, 3, 4]⟩, none),
                        (.bind ⟨1, some [0, 2, 3, 4, 5]⟩,
                         none),
                        (.bind ⟨2, some [0, 2, 3, 4, 5]⟩,
                         none),
                        (.bind ⟨3, none⟩, none),
                        (.effect ⟨4, none⟩, none),
                        (.bind ⟨5, some [0, 2, 3, 4]⟩, none),
                        (.bind ⟨6, none⟩, none)]
                       7
                       [.var 0]
                       (Verification.Invoke.call)
                       false)
                     [Verification.PropKey.str "[[code]]"]
                     [.nul], .bind ⟨47, none⟩, none⟩,
   ⟨.var 0, .effect ⟨1, some [0]⟩, none⟩,
   ⟨.var 0, .effect ⟨49, some [0]⟩, none⟩,
   ⟨.var 0, .bind ⟨50, some [0, 2]⟩, none⟩,
   ⟨.makeAt
                     (Verification.CallCode.absent)
                     [Verification.PropKey.str "value"]
                     [.var 0], .bind ⟨51, some [0, 2]⟩, none⟩,
   ⟨.var 0, .bind ⟨52, none⟩, none⟩,
   ⟨.var 0, .effect ⟨53, none⟩, none⟩,
   ⟨.var 0, .bind ⟨54, some [0]⟩, none⟩,
   ⟨.tru, .bind ⟨55, none⟩, none⟩,
   ⟨.nul, .effect ⟨0, some []⟩, none⟩]
#guard ((continued.toOption.getD []).map (·.program)).headD [] == continueProgram
#guard ((continued.toOption.getD []).map (·.start)).headD 0 == 57

-- Continue drops the alias and returns to condition evaluation after the write.
theorem continue_retests : ∃ n, Execution continueProgram n []
    (.at 57 (fun _ => .nul)) [.fls,.nul,.nul,.nul] (.done .fls) := by
  apply Exists.intro
  run_machine
#print axioms continue_retests
end LoopTransfer

end Verification.LoweringTraceTests
