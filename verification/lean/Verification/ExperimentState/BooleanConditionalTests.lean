import Verification.ExperimentState.RequestJson
import Verification.ExperimentState.DirectProof

namespace Verification.ExperimentState.BooleanConditionalTests
open Lean ProgramTyping ProgramCertificates ControlFlow RequestJson PositiveGraphs

private def types : List (List (PositiveNormalization.Clause (List Nat))) :=
  [[.bool],[.nul],[.refs [0] []],[.arrs [([1],[0])]]]
private def ok (r : Except String α) : Bool := match r with | .ok _ => true | .error _ => false
private def roundtrip (r : Request) : Except String Unit := do
  let input ← Json.parse (toJson r).compress
  let evidence ← produceJson input 10
  verifyJson input (← Json.parse evidence.compress)

private def branch (c t e : Tm) : Request :=
  ⟨2,types,[⟨.ite c t e,.ret⟩],[⟨[[0]],[0]⟩],[0],0,[[0]]⟩
#guard ok (roundtrip (branch (.var 0) .tru .fls))
#guard !ok (roundtrip (branch .nul .tru .fls))
#guard !ok (roundtrip (branch (.var 0) (.read .nul) .fls))
#guard !ok (roundtrip (branch (.var 0) .tru (.read .nul)))

-- Boolean singleton unions are accepted; adding null to the input is not.
#guard ok (roundtrip ⟨2,[[.boolLit true],[.boolLit false]],
  [⟨.ite (.var 0) .tru .fls,.ret⟩],[⟨[[0,1]],[0,1]⟩],[0,1],0,[[0,1]]⟩)
#guard !ok (roundtrip { branch (.var 0) .tru .fls with inputs := [[0,1]], claims := [⟨[[0,1]],[0]⟩] })

-- The condition must be Boolean and both branch judgments must be present.
private def G : NormalGraph Nat := fun i => (types[i]?).getD []
private def cond : Evidence Nat := .node ⟨[[0]],.var 0,[0]⟩ .var []
private def yes : Evidence Nat := .node ⟨[[0]],.tru,[0]⟩ .tru []
private def no : Evidence Nat := .node ⟨[[0]],.fls,[0]⟩ .fls []
private def proof : Evidence Nat := .node ⟨[[0]],.ite (.var 0) .tru .fls,[0]⟩ .ifBool [cond,yes,no]
#guard checkTree G proof
#guard !checkTree G (.node ⟨[[0]],.ite (.var 0) .tru .fls,[0]⟩ .ifBool [cond,yes])
#guard !checkTree G (.node ⟨[[0]],.ite (.var 0) .tru .fls,[0]⟩ .ifBool [cond,no,yes])
#guard !checkTree G (.node ⟨[[0]],.ite .nul .tru .fls,[0]⟩ .ifBool
  [.node ⟨[[0]],.nul,[1]⟩ .nul [],yes,no])

private def recipe := DirectProof.node [[0]] (.ite (.var 0) .tru .fls) [0] .ifBool
  [DirectProof.var [[0]] 0 [0],DirectProof.node [[0]] .tru [0] .tru,
   DirectProof.node [[0]] .fls [0] .fls]
#guard ((DirectProof.render G [[0],[1]] [[0]] recipe).map (checkTree G)) == some true

-- A captured cell is read when the closure is called, after an alias write.
private def captureProgram (q : Bool) : Program :=
  [⟨.alloc .tru,.bind 1⟩,
   ⟨.lam (.ite (.read (.var 1)) .tru .fls),.bind 2⟩,
   ⟨.write (.var 1) (if q then .tru else .fls),.effect 3⟩,
   ⟨.app (.var 0) .nul,.ret⟩]
private def captureRequest (q : Bool) : Request :=
  ⟨2,types,captureProgram q,[⟨[],[2]⟩,⟨[[2]],[3]⟩,⟨[[3],[2]],[1]⟩,⟨[[3],[2]],[0]⟩],[0],0,[]⟩
#guard ok (roundtrip (captureRequest true))
#guard ok (roundtrip (captureRequest false))

theorem captured_branch_reads_latest (q : Bool) : Execution (captureProgram q) 13 []
    (.at 0 (fun _ => .nul)) [if q then .tru else .fls] (.done (if q then .tru else .fls)) := by
  cases q <;> repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.allocV rfl))
    | apply Execution.next (.expr (.writeV rfl (by decide)))
    | apply Execution.next (.expr (.beta rfl))
    | apply Execution.next (.expr (.iteC (.readV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.effect rfl)
    | apply Execution.next (.ret rfl)

private def effectfulProgram : Program :=
  [⟨.alloc .tru,.bind 1⟩,
   ⟨.ite (.app (.lam (.read (.var 1))) (.write (.var 0) .fls)) .tru .fls,.ret⟩]
#guard ok (roundtrip ⟨2,types,effectfulProgram,[⟨[],[2]⟩,⟨[[2]],[0]⟩],[0],0,[]⟩)

theorem condition_effects_preserved : Execution effectfulProgram 9 []
    (.at 0 (fun _ => .nul)) [.fls] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.allocV rfl))
    | apply Execution.next (.expr (.iteC (.appR rfl (.writeV rfl (by decide)))))
    | apply Execution.next (.expr (.iteC (.beta rfl)))
    | apply Execution.next (.expr (.iteC (.readV rfl)))
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.ret rfl)

#print axioms captured_branch_reads_latest
#print axioms condition_effects_preserved
end Verification.ExperimentState.BooleanConditionalTests
