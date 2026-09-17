import Verification.ExperimentState.SourceClaimJson

namespace Verification.ExperimentState.CastTests
open Lean ProgramTyping SourceExtraction SourceClaimJson ControlFlow

-- `assertedSnapshot` from tests/stateful-source/casts.ts, captured with its
-- tsc claims after conversion to calculus labels. The assertion lowers to a
-- node that returns its operand unchanged: no operation, no effect.
private def ast : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/casts.ts\",\"sourceSha256\":\"3a3ba180d973bb58a3d0f5d8bcfc76002bdd457f2ac1d9855e75ff95fda72473\",\"aliases\":[],\"functions\":[{\"name\":\"assertedSnapshot\",\"namePos\":[312,328],\"typeParams\":[],\"params\":[{\"name\":\"x\",\"pos\":[329,330],\"type\":{\"top\":false,\"atoms\":[{\"a\":\"record\",\"fields\":[{\"name\":\"value\",\"optional\":false,\"read\":{\"top\":false,\"atoms\":[{\"a\":\"number\"},{\"a\":\"null\"}]},\"write\":{\"top\":false,\"atoms\":[{\"a\":\"number\"},{\"a\":\"null\"}]}}],\"indexes\":{\"string\":\"absent\",\"number\":\"absent\",\"symbol\":\"absent\"},\"call\":\"unknown\",\"construct\":\"unknown\",\"array\":\"unknown\"}]}}],\"retType\":{\"top\":false,\"atoms\":[{\"a\":\"number\"}]},\"body\":[{\"k\":\"if\",\"pos\":[370,401],\"cond\":{\"k\":\"bin\",\"pos\":[374,390],\"op\":\"===\",\"l\":{\"k\":\"read\",\"pos\":[374,381],\"field\":\"value\",\"e\":{\"k\":\"id\",\"pos\":[374,375],\"name\":\"x\"}},\"r\":{\"k\":\"lit\",\"pos\":[386,390],\"lit\":{\"a\":\"null\"}}},\"then\":[{\"k\":\"return\",\"pos\":[392,401],\"e\":{\"k\":\"lit\",\"pos\":[399,400],\"lit\":{\"a\":\"numberlit\",\"v\":\"0\"}}}],\"else_\":null},{\"k\":\"const\",\"pos\":[404,436],\"bindings\":[{\"name\":\"value\",\"namePos\":[410,415],\"annot\":null,\"init\":{\"k\":\"cast\",\"pos\":[418,435],\"cast\":\"as\",\"annot\":{\"top\":false,\"atoms\":[{\"a\":\"number\"}]},\"e\":{\"k\":\"read\",\"pos\":[418,425],\"field\":\"value\",\"e\":{\"k\":\"id\",\"pos\":[418,419],\"name\":\"x\"}}}}]},{\"k\":\"effect\",\"pos\":[439,454],\"e\":{\"k\":\"write\",\"pos\":[439,453],\"field\":\"value\",\"receiver\":{\"k\":\"id\",\"pos\":[439,440],\"name\":\"x\"},\"rhs\":{\"k\":\"lit\",\"pos\":[449,453],\"lit\":{\"a\":\"null\"}}}},{\"k\":\"return\",\"pos\":[457,470],\"e\":{\"k\":\"id\",\"pos\":[464,469],\"name\":\"value\"}}]}]}").toOption.getD .null
private def claims : Json := (Json.parse "{\"file\":\"verification/tests/stateful-source/casts.ts\",\"sourceSha256\":\"3a3ba180d973bb58a3d0f5d8bcfc76002bdd457f2ac1d9855e75ff95fda72473\",\"types\":[[\"nul\"],[{\"boolLit\":{\"value\":true}}],[{\"boolLit\":{\"value\":false}}],[\"undef\"],[\"num\"],[{\"refs\":{\"first\":[[\"value\",[0,4]]],\"rest\":[]}}],[{\"numLit\":{\"bits\":\"0\"}}],[{\"numLit\":{\"bits\":\"4607182418800017408\"}}]],\"functions\":[{\"name\":\"assertedSnapshot\",\"namePos\":[312,328],\"params\":[{\"name\":\"x\",\"type\":[5],\"current\":null}],\"result\":[4],\"entries\":[{\"start\":370,\"bindings\":[{\"name\":\"x\",\"type\":[5],\"current\":null}]},{\"start\":392,\"bindings\":[{\"name\":\"x\",\"type\":[5],\"current\":null}]},{\"start\":404,\"bindings\":[{\"name\":\"x\",\"type\":[5],\"current\":[[\"value\",[4]]]}]},{\"start\":439,\"bindings\":[{\"name\":\"x\",\"type\":[5],\"current\":null},{\"name\":\"value\",\"type\":[4],\"current\":null}]},{\"start\":457,\"bindings\":[{\"name\":\"x\",\"type\":[5],\"current\":null},{\"name\":\"value\",\"type\":[4],\"current\":null}]}],\"expressions\":[{\"pos\":[374,390],\"type\":[1,2],\"current\":null},{\"pos\":[374,381],\"type\":[0,4],\"current\":null},{\"pos\":[374,375],\"type\":[5],\"current\":null},{\"pos\":[386,390],\"type\":[0],\"current\":null},{\"pos\":[399,400],\"type\":[6],\"current\":null},{\"pos\":[418,435],\"type\":[4],\"current\":null},{\"pos\":[418,425],\"type\":[4],\"current\":null},{\"pos\":[418,419],\"type\":[5],\"current\":null},{\"pos\":[439,453],\"type\":[0],\"current\":null},{\"pos\":[439,440],\"type\":[5],\"current\":null},{\"pos\":[449,453],\"type\":[0],\"current\":null},{\"pos\":[464,469],\"type\":[4],\"current\":null}]}]}").toOption.getD .null
private def file := "verification/tests/stateful-source/casts.ts"
private def extracted := SourceClaimJson.extract ast claims file
#guard extracted.toOption.isSome
private def program : Program := ((extracted.toOption.getD []).map (·.program)).headD []
private def start : Nat := ((extracted.toOption.getD []).map (·.start)).headD 0
#guard (SourceClaimJson.produceJson ast claims file 10).toOption.isSome

-- From the entry (19): the field is read (17) and tested for null (13); on
-- the non-null arm it is read again (8), the assertion (7) returns that
-- value unchanged, null is written to the field (3) and the saved value is
-- returned (0). The assertion is a `.var 0` node: no operation, no effect.
private def expected : Program :=
  [
   ⟨.var 0,.ret⟩,
   ⟨.var 0,.bind 0⟩,
   ⟨.var 0,.bind ⟨1,some [3, 4]⟩⟩,
   ⟨.writeAt "value" (.var 1) (.var 0),.effect 2⟩,
   ⟨.nul,.bind 3⟩,
   ⟨.var 1,.bind 4⟩,
   ⟨.var 0,.effect 5⟩,
   ⟨.var 0,.bind ⟨6,some [0, 2]⟩⟩,
   ⟨.readAt "value" (.var 0),.bind ⟨7,some [0, 2]⟩⟩,
   ⟨.var 0,.bind 8⟩,
   ⟨.nul,.effect 9⟩,
   ⟨.var 0,.ret⟩,
   ⟨.num 0,.bind 11⟩,
   ⟨.var 1,.tagBind .isNul ⟨12,some [3]⟩ ⟨10,some [3]⟩⟩,
   ⟨.ite (.test .isNul (.var 1)) (.tru) (.fls),.bind ⟨13,some [0, 3, 4]⟩⟩,
   ⟨.nul,.bind 14⟩,
   ⟨.var 0,.bind 15⟩,
   ⟨.readAt "value" (.var 0),.bind ⟨16,some [0, 2]⟩⟩,
   ⟨.var 0,.bind 17⟩,
   ⟨.nul,.effect 18⟩]
#guard program == expected
#guard start == 19

/-- The input object in slot zero, its one field at heap location zero. -/
private def input : Env := fun i => if i == 0 then .objAt [("value",0)] .absent else .nul

-- With the field holding 3 the guard falls through, the assertion returns 3,
-- the field is set to null, and 3 is returned. A trace of the lowered
-- program, not a general compiler proof.
theorem assertion_is_identity : Execution expected 41 [.num 4613937818241073152]
    (.at 19 input) [.nul] (.done (.num 4613937818241073152)) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.readField rfl rfl))
    | apply Execution.next (.expr (.writeField rfl rfl (by decide)))
    | apply Execution.next (.expr (.iteC (.testV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.tagBind rfl)
    | apply Execution.next (.ret rfl)

#print axioms assertion_is_identity
end Verification.ExperimentState.CastTests
