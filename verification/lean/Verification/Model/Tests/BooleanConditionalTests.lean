import Verification.Model.Source.RequestJson
import Verification.Model.Programs.DirectProof

namespace Verification.Model.BooleanConditionalTests
open Lean ProgramTyping ProgramCertificates ControlFlow RequestJson PositiveGraphs

private def types : List (List (PositiveNormalization.Clause (List Nat))) :=
  [[.bool],[.nul],[.refs [(valueField, [0])] [] []],[.arrs [([4],[[1]],[0])] []],[.top],[.undef]]
private def ok (r : Except String α) : Bool := match r with | .ok _ => true | .error _ => false
private def roundtrip (r : Request) : Except String Unit := do
  let input ← Json.parse (toJson r).compress
  let evidence ← produceJson input 10
  verifyJson input (← Json.parse evidence.compress)

private def branch (c t e : Tm) : Request :=
  ⟨types,[⟨.ite c t e,.ret⟩],[⟨[[0]],[0]⟩],[0],0,[[0]]⟩
#guard ok (roundtrip (branch (.var 0) .tru .fls))
#guard !ok (roundtrip (branch .nul .tru .fls))
#guard !ok (roundtrip (branch (.var 0) (.read .nul) .fls))
#guard !ok (roundtrip (branch (.var 0) .tru (.read .nul)))

-- Boolean singleton unions are accepted; adding null to the input is not.
#guard ok (roundtrip ⟨[[.boolLit true],[.boolLit false]],
  [⟨.ite (.var 0) .tru .fls,.ret⟩],[⟨[[0,1]],[0,1]⟩],[0,1],0,[[0,1]]⟩)
#guard !ok (roundtrip { branch (.var 0) .tru .fls with inputs := [[0,1]], claims := [⟨[[0,1]],[0]⟩] })

-- The condition must be Boolean and both branch judgments must be present.
private def G : NormalGraph Nat := .ofRows fun i => (types[i]?).getD []
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

-- Refinement changes only the tested immutable slot. This result needs the
-- refined rule: the original Boolean input alone does not have type true.
private def refinedTypes : List (List (PositiveNormalization.Clause (List Nat))) :=
  [[.boolLit true],[.boolLit false],[.nul]]
private def RG : NormalGraph Nat := .ofRows fun i => (refinedTypes[i]?).getD []
private def refinedYes : Evidence Nat := .node ⟨[[0]],.var 0,[0]⟩ .var []
private def refinedNo : Evidence Nat := .node ⟨[[1]],.tru,[0]⟩ .truLit []
private def refinedProof : Evidence Nat :=
  .node ⟨[[0,1]],.ite (.var 0) (.var 0) .tru,[0]⟩ (.ifBoolVar [0] [1]) [refinedYes,refinedNo]
#guard checkTree RG refinedProof
#guard ok (roundtrip ⟨refinedTypes,[⟨.ite (.var 0) (.var 0) .tru,.ret⟩],
  [⟨[[0,1]],[0]⟩],[0],0,[[0,1]]⟩)
#guard !checkTree RG (.node ⟨[[0,1]],.ite (.var 0) (.var 0) .tru,[0]⟩
  (.ifBoolVar [1] [0]) [refinedYes,refinedNo])
#guard !checkTree RG (.node ⟨[[0,1]],.ite (.var 1) (.var 0) .tru,[0]⟩
  (.ifBoolVar [0] [1]) [refinedYes,refinedNo])
#guard !checkTree RG (.node ⟨[[0,1]],.ite (.var 0) (.var 0) .tru,[0]⟩
  (.ifBoolVar [0] [1]) [refinedYes])
#guard !checkTree RG (.node ⟨[[0,1],[0,1]],.ite (.var 0) (.var 1) .tru,[0]⟩
  (.ifBoolVar [0] [1]) [.node ⟨[[0],[0]],.var 1,[0]⟩ .var [],
    .node ⟨[[1],[0,1]],.tru,[0]⟩ .truLit []])
#guard !validEvidence 3 (.node ⟨[[0,1]],.ite (.var 0) (.var 0) .tru,[0]⟩
  (.ifBoolVar [3] [1]) [refinedYes,refinedNo])
private def refinedRecipe := DirectProof.node [[0,1]] (.ite (.var 0) (.var 0) .tru) [0]
  (.ifBoolVar [0] [1]) [DirectProof.var [[0]] 0 [0],DirectProof.node [[1]] .tru [0] .truLit]
#guard ((DirectProof.render RG [[0],[1],[0,1]] [[0,1]] refinedRecipe).map (checkTree RG)) == some true

-- A singleton condition checks its own evidence and only the reachable arm.
private def knownCond : Evidence Nat := .node ⟨[],.tru,[0]⟩ .truLit []
private def knownArm : Evidence Nat := .node ⟨[],.fls,[1]⟩ .flsLit []
private def knownTerm : Tm := .ite .tru .fls (.read .nul)
private def knownProof : Evidence Nat :=
  .node ⟨[],knownTerm,[1]⟩ (.ifKnown true) [knownCond,knownArm]
#guard checkTree RG knownProof
#guard ok (roundtrip ⟨refinedTypes,[⟨knownTerm,.ret⟩],[⟨[],[1]⟩],[1],0,[]⟩)
#guard !checkTree RG (.node ⟨[],knownTerm,[1]⟩ (.ifKnown false) [knownCond,knownArm])
#guard !checkTree RG (.node ⟨[],knownTerm,[1]⟩ (.ifKnown true) [knownArm])
#guard !checkTree RG (.node ⟨[],.ite .tru (.read .nul) .fls,[1]⟩ (.ifKnown true) [knownCond,knownArm])
#guard !checkTree RG (.node ⟨[[0,1]],.ite (.var 0) .fls (.read .nul),[1]⟩ (.ifKnown true)
  [.node ⟨[[0,1]],.var 0,[0,1]⟩ .var [],.node ⟨[[0,1]],.fls,[1]⟩ .flsLit []])

private def knownEffectProgram : Program :=
  [⟨.alloc .tru,.bind 1⟩,
   ⟨.ite (.letE (.write (.var 0) .fls) .tru) .fls (.read .nul),.ret⟩]
#guard ok (roundtrip ⟨refinedTypes ++ [[.refs [(valueField, [0,1])] [] []]],knownEffectProgram,
  [⟨[],[3]⟩,⟨[[3]],[1]⟩],[1],0,[]⟩)

/-- Selecting a known arm must not erase the condition's write. -/
theorem known_condition_effects_preserved : Execution knownEffectProgram 8 []
    (.at 0 (fun _ => .nul)) [.fls] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.iteC (.letC (.writeV rfl (by decide)))))
    | apply Execution.next (.expr (.iteC (.letV rfl)))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.ret rfl)

#print axioms known_condition_effects_preserved

-- A tag test can split an explicit null/Boolean union without a semantic join.
private def nullTypes : List (List (PositiveNormalization.Clause (List Nat))) :=
  [[.nul],[.boolLit true],[.boolLit false]]
private def NG : NormalGraph Nat := .ofRows fun i => (nullTypes[i]?).getD []
private def nullGuard : Tm := .ite (.test .isNul (.var 0)) .tru (.var 0)
private def nullProof : Evidence Nat :=
  (CertificateProducer.expression NG [[0],[1],[2],[1,2],[0,1,2]] 10 [[0,1,2],[2]] nullGuard [1,2]).getD
    (.node ⟨[],.nul,[]⟩ .nul [])
#guard checkTree NG nullProof
#guard ok (roundtrip ⟨nullTypes,[⟨nullGuard,.ret⟩],
  [⟨[[0,1,2]],[1,2]⟩],[1,2],0,[[0,1,2]]⟩)
-- The evidence cannot omit a union member or alter an unrelated binding.
#guard !(match nullProof with
  | .node j _ ps => checkTree NG (.node j (.unionVar 0) ps.tail))
#guard !(match nullProof with
  | .node j r ps => checkTree NG (.node j r (ps.map fun p => match p with
      | .node k r children => .node {k with context := k.context.set 1 [1]} r children)))
#guard !(match nullProof with
  | .node j _ ps => checkTree NG (.node j (.unionVar 1) ps))
#guard !checkTree NG (.node ⟨[],.nul,[0]⟩ (.unionVar 0) [])
-- An empty union has no inhabitants; this is elimination from an impossible input.
#guard checkTree NG (.node ⟨[[]],.read .nul,[1]⟩ (.unionVar 0) [])
-- Packing different shapes into a single graph label is not split by this search.
#guard !ok (roundtrip ⟨[[.nul,.boolLit true],[.boolLit true]],
  [⟨.ite (.test .isNul (.var 0)) .tru (.var 0),.ret⟩],
  [⟨[[0]],[1]⟩],[1],0,[[0]]⟩)

-- A captured cell is read when the closure is called, after an alias write.
private def captureProgram (q : Bool) : Program :=
  [⟨.alloc .tru,.bind 1⟩,
   ⟨.funE (.ite (.read (.var 2)) .tru .fls),.bind 2⟩,
   ⟨.write (.var 1) (if q then .tru else .fls),.effect 3⟩,
   ⟨.app (.var 0) .nul,.ret⟩]
private def captureRequest (q : Bool) : Request :=
  ⟨types,captureProgram q,[⟨[],[2]⟩,⟨[[2]],[3]⟩,⟨[[3],[2]],[1]⟩,⟨[[3],[2]],[0]⟩],[0],0,[]⟩
#guard ok (roundtrip (captureRequest true))
#guard ok (roundtrip (captureRequest false))

theorem captured_branch_reads_latest (q : Bool) : Execution (captureProgram q) 14 []
    (.at 0 (fun _ => .nul)) [if q then .tru else .fls,.nul] (.done (if q then .tru else .fls)) := by
  cases q <;> repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
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
   ⟨.ite (.letE (.write (.var 0) .fls) (.read (.var 1))) .tru .fls,.ret⟩]
#guard ok (roundtrip ⟨types,effectfulProgram,[⟨[],[2]⟩,⟨[[2]],[0]⟩],[0],0,[]⟩)

theorem condition_effects_preserved : Execution effectfulProgram 9 []
    (.at 0 (fun _ => .nul)) [.fls] (.done .fls) := by
  repeat first
    | exact Execution.refl
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.iteC (.letC (.writeV rfl (by decide)))))
    | apply Execution.next (.expr (.iteC (.letV rfl)))
    | apply Execution.next (.expr (.iteC (.readV rfl)))
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.ret rfl)

#print axioms captured_branch_reads_latest
#print axioms condition_effects_preserved
end Verification.Model.BooleanConditionalTests
