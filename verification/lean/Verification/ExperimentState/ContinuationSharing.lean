import Verification.ExperimentState.SourceTypes
import Verification.ExperimentState.DirectProof

/-! Shared local continuations use allocated function objects, lets and calls. This module
checks the construction before extending source lowering to multiple surviving
paths. It introduces no new term, typing rule or certificate constructor. -/
namespace Verification.ExperimentState.ContinuationSharing
open ProgramTyping PositiveRules ProgramCertificates ControlFlow RequestJson Lean

/-- `k` is under an argument slot; `body` is under a continuation slot.
The continuation term occurs once, independently of how many paths call it. -/
def share (k body : Tm) : Tm := .letE (.funE k) body

theorem share_typed {ι : Type} [DecidableEq ι] {G : PositiveGraphs.NormalGraph ι}
    {Γ N R C k body} (hc : Represents G C (.arrs [([N],R)]))
    (hk : HasTy G (N::Γ) k R) (hb : HasTy G (C::Γ) body R) :
    HasTy G Γ (share k body) R := by
  apply HasTy.letE (HasTy.funE hc (by simp) ?_) hb
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact hk

/-- The primitives, a Boolean cell, a null-to-Boolean arrow and a null-to-true arrow. -/
private def T : SourceTypes.Table :=
  SourceTypes.initial ++ [[.refs [(valueField,[1,2])] [] []],[.arrs [([[0]],[1,2])]],[.arrs [([[0]],[1])]]]
private def G := SourceTypes.graph T
private def Γ : List (Ty Nat) := [[4],[1,2],[1,2]]
private def H : List (Ty Nat) := [5]::Γ
private def call (Δ : List (Ty Nat)) (i : Nat) : DirectProof.Plan :=
  DirectProof.node Δ (.app (.var i) .nul) [1,2] .app
    [DirectProof.var Δ i [5],DirectProof.node Δ .nul [0] .nul]
private def choose (Δ : List (Ty Nat)) (i : Nat) (t e : DirectProof.Plan) :=
  DirectProof.node Δ (.ite (.var i) t.term e.term) [1,2] .ifBool
    [DirectProof.var Δ i [1,2],t,e]
private def recipe : DirectProof.Plan :=
  let K := [0]::Γ
  let k := DirectProof.node Γ (.funE (.read (.var 1))) [5] .funE
    [DirectProof.node K (.read (.var 1)) [1,2] .read [DirectProof.var K 1 [4]]]
  let write := DirectProof.node H (.write (.var 1) .fls) [0] .write
    [DirectProof.var H 1 [4],
     DirectProof.cast H [1,2] (DirectProof.node H .fls [2] .flsLit)]
  let updated := DirectProof.letE H write (call ([0]::H) 1)
  let body := choose H 2 (choose H 3
    (DirectProof.cast H [1,2] (DirectProof.node H .tru [1] .truLit)) updated) (call H 0)
  DirectProof.letE Γ k body

private def term : Tm := share (.read (.var 1))
  (.ite (.var 2)
    (.ite (.var 3) .tru (.letE (.write (.var 1) .fls) (.app (.var 1) .nul)))
    (.app (.var 0) .nul))
#guard recipe.term == term
private def proof : Option (Evidence Nat) :=
  DirectProof.render G (CertificateProducer.vocabulary G [0,1,2,4,5] [] [[1,2]]) Γ recipe
#guard (proof.map (checkTree G)) == some true

private def program : Program := [⟨.alloc .tru,.bind 1⟩,⟨term,.ret⟩]
private def request : Request :=
  ⟨T,program,[⟨[[1,2],[1,2]],[4]⟩,⟨Γ,[1,2]⟩],[1,2],0,[[1,2],[1,2]]⟩
private def accepted : Except String Unit := do
  let some p := proof | throw "missing direct proof"
  let wire ← Json.parse (toJson request).compress
  let e ← produceJson wire 10 [] [p] [] (some [0,1,2,4,5,T.length])
  verifyJson wire (← Json.parse e.compress)
#guard match accepted with | .ok _ => true | .error _ => false

-- Capturing a reference does not capture its current contents. All three paths
-- are observable: return early; write then resume; resume without writing.
theorem shared_paths (a b : Bool) : Execution program
    (if a then (if b then 9 else 13) else 10) []
    (.at 0 (fun i => if i == 0 then (if a then .tru else .fls) else (if b then .tru else .fls)))
    [if a && !b then .fls else .tru,.nul] (.done (if a && !b then .fls else .tru)) := by
  cases a <;> cases b <;> repeat first
    | exact Execution.refl
    | apply Execution.next (.expr (.letC (.makeV rfl)))
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.makeV rfl))
    | apply Execution.next (.expr (.letV rfl))
    | apply Execution.next (.expr (.beta rfl))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.expr (.letC (.writeV rfl (by decide))))
    | apply Execution.next (.expr (.readV rfl))
    | apply Execution.next (.bind rfl)
    | apply Execution.next (.ret rfl)

-- A shared continuation cannot promise a singleton result from a Boolean cell.
#guard !(DirectProof.render G
  (CertificateProducer.vocabulary G [0,1,2,4,5] [] [[1,2]]) Γ
  (DirectProof.cast Γ [1] recipe)).isSome

-- The promise is checked where the continuation is defined, not invented from
-- the paths on which it may later be called.
#guard !checkTree G (.node ⟨Γ,.funE (.read (.var 1)),[6]⟩ .funE
  [.node ⟨[0]::Γ,.read (.var 1),[1,2]⟩ .read
    [.node ⟨[0]::Γ,.var 1,[4]⟩ .var []]])

-- A later refinement is passed as a checked argument, not retroactively added
-- to the captured environment. Both surviving paths reach the same definition.
private def refinedTypes := T ++ [[PositiveNormalization.Clause.arrs [([[2]],[1,2])]]]
private def refinedGraph : PositiveGraphs.NormalGraph Nat := fun i => refinedTypes[i]?.getD []
private def outer : List (Ty Nat) := [[1,2],[1,2]]
private def extraLabel := T.length
private def inside : List (Ty Nat) := [extraLabel]::outer
private def refinedCall (Δ : List (Ty Nat)) (i : Nat) :=
  DirectProof.node Δ (.app (.var 0) (.var i)) [1,2] .app
    [DirectProof.var Δ 0 [extraLabel],DirectProof.var Δ i [2]]
private def refinedRecipe : DirectProof.Plan :=
  let k := DirectProof.node outer (.funE (.var 0)) [extraLabel] .funE
    [DirectProof.var ([2]::outer) 0 [1,2]]
  let yes := inside.set 2 [1]
  let no := inside.set 2 [2]
  let arm := DirectProof.node inside (.ite (.var 2) .tru (.app (.var 0) (.var 2)))
    [1,2] (.ifBoolVar [1] [2])
    [DirectProof.cast yes [1,2] (DirectProof.node yes .tru [1] .truLit),refinedCall no 2]
  DirectProof.letE outer k (choose inside 1 arm arm)
private def refinedPool := CertificateProducer.vocabulary refinedGraph [0,1,2,extraLabel] [] [[1,2]]
private def refinedProof := DirectProof.render refinedGraph refinedPool outer refinedRecipe
#guard (refinedProof.map (checkTree refinedGraph)) == some true
-- Neither the unrefined slot nor a different Boolean slot meets the contract.
#guard !(DirectProof.render refinedGraph refinedPool inside (refinedCall inside 2)).isSome
#guard !(DirectProof.render refinedGraph refinedPool (inside.set 2 [2])
  (refinedCall (inside.set 2 [2]) 1)).isSome

private def refinedTerm := share (.var 0)
  (.ite (.var 1) (.ite (.var 2) .tru (.app (.var 0) (.var 2)))
    (.ite (.var 2) .tru (.app (.var 0) (.var 2))))
#guard refinedRecipe.term == refinedTerm
private def refinedProgram : Program := [⟨refinedTerm,.ret⟩]
#guard match (do
  let some p := refinedProof | throw "missing refinement proof"
  let r : Request := ⟨refinedTypes,refinedProgram,[⟨outer,[1,2]⟩],[1,2],0,outer⟩
  let wire := toJson r
  let e ← produceJson wire 10 [] [p] [] (some [0,1,2,4,5,T.length])
  verifyJson wire (← Json.parse e.compress)) with
  | .ok _ => true | .error _ => false

theorem passed_refinement_paths (a b : Bool) : Execution refinedProgram
    (if b then 6 else 7) []
    (.at 0 (fun i => if i == 0 then (if a then .tru else .fls) else (if b then .tru else .fls)))
    [.nul] (.done (if b then .tru else .fls)) := by
  cases a <;> cases b <;> repeat first
    | exact Execution.refl
    | apply Execution.next (.expr (.letC (.makeV rfl)))
    | apply Execution.next (.enter rfl)
    | apply Execution.next (.expr (.letV rfl))
    | apply Execution.next (.expr (.beta rfl))
    | apply Execution.next (.expr .iteT)
    | apply Execution.next (.expr .iteF)
    | apply Execution.next (.ret rfl)

#print axioms passed_refinement_paths

#print axioms share_typed
#print axioms shared_paths
end Verification.ExperimentState.ContinuationSharing
