import Verification.ExperimentState.SourceTypes

namespace Verification.ExperimentState.BranchRefinementTests
open Lean ProgramTyping ControlFlow RequestJson BranchRefinement

private def ok (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false
private def T : SourceTypes.Table := SourceTypes.initial ++ [[.refs [1,2] []]]
private def G := SourceTypes.graph T

-- Tag observations split explicit unions without inventing a new type label.
#guard tagSlice G [0,1,2] .isNul true == [0]
#guard tagSlice G [0,1,2] .isNul false == [1,2]
#guard tagSlice G [0,1,2] .isBool true == [1,2]
#guard tagSlice G [0] .isNul false == []
-- Mixed labels are retained intact, rather than narrowed unsoundly by head shape.
private def mixed : PositiveGraphs.NormalGraph Nat := fun _ => [.nul,.bool]
#guard tagSlice mixed [0] .isNul true == [0]
#guard tagSlice mixed [0] .isNul false == [0]

-- An older immutable slot can be refined and reordered; unrelated slots cannot.
#guard checkObserved G [[1,2],[0,1,2]] [[0],[1,2]] 1 (.tag .isNul true)
  (some [1,0]) [.subset,.subset]
#guard checkObserved G [[1,2],[0,1,2]] [[1,2],[1,2]] 1 (.tag .isNul false)
  (some [1,0]) [.subset,.subset]
#guard !checkObserved G [[1,2],[0,1,2]] [[0],[1,2]] 1 (.tag .isNul false)
  (some [1,0]) [.subset,.subset]
#guard !checkObserved G [[1,2],[0,1,2]] [[0],[1]] 1 (.tag .isNul true)
  (some [1,0]) [.subset,.subset]
#guard !checkObserved G [[1,2],[0,1,2]] [[0],[1,2]] 1 (.tag .isNul true)
  (some [0,1]) [.subset,.subset]
#guard !checkObserved G [[0,1,2]] [[0]] 9 (.tag .isNul true)
  none [.subset]
#guard !checkObserved G [[0,1,2]] [[0]] 0 (.tag .isNul true)
  (some [4]) [.subset]
#guard !checkObserved G [[0,1,2]] [[0]] 0 (.tag .isNul true)
  none []

-- Boolean identity and a Boolean shape observation are different facts.
#guard checkObserved G [[1,2]] [[1]] 0 (.boolean true) none [.subset]
#guard !checkObserved G [[1,2]] [[1]] 0 (.tag .isBool true) none [.subset]
-- Observation metadata must identify an existing slot, including forgotten slots.
#guard !checkObserved G [] [] 0 (.boolean true) none []
#guard !checkObserved G [] [] 0 (.tag .isNul true) none []
#guard checkObserved G [[0,1,2]] [] 0 (.tag .isNul true) none []
-- Filtering's precision limit does not restrict the semantic obligation.
private def mixedWithNull : PositiveGraphs.NormalGraph Nat
  | 0 => [.nul,.bool]
  | _ => [.nul]
#guard !checkObservedSub mixedWithNull [0] [1] (.tag .isNul true) .subset
example : ObservedSub mixedWithNull [0] [1] (.tag .isNul true) := by
  intro n W v _ ho
  have hn : v = .nul := by cases v <;> simp_all [Observation.holds, tagHolds]
  subst v
  apply (PositiveRules.expand_sem _ _ _ _ _).mpr
  exact ⟨.nul, by simp [PositiveRules.expand, mixedWithNull], rfl⟩

-- Slot zero is justified by the branch observation. Slot one is not refined.
#guard checkObserved G [[1,2],[1,2]] [[1],[1,2]] 0 (.boolean true)
  (some [0,1]) [.subset,.subset]
#guard !checkObserved G [[1,2],[1,2]] [[2],[1,2]] 0 (.boolean true)
  (some [0,1]) [.subset,.subset]
#guard !checkObserved G [[1,2],[1,2]] [[1],[1]] 0 (.boolean true)
  (some [0,1]) [.subset,.subset]
#guard !checkObserved G [[1,2],[1,2]] [[1],[1,2]] 0 (.boolean true)
  (some [1,0]) [.subset,.subset]
#guard !checkObserved G [[1,2]] [[1]] 0 (.boolean true) (some [4]) [.subset]
#guard !checkObserved G [[1,2]] [[1]] 0 (.boolean true) (some [0]) []
#guard !checkObserved G [[1,2]] [[1]] 0 (.boolean true) (some [0,0]) [.subset]

private def request (v : Tm) : Request :=
  ⟨2, T,
    [⟨v,.bind 1⟩, ⟨.var 0,.branchBind ⟨2,some [0,1]⟩ ⟨3,some [0,1]⟩⟩,
     ⟨.var 0,.ret⟩, ⟨.var 0,.ret⟩],
    [⟨[],[1,2]⟩,⟨[[1,2]],[1,2]⟩,⟨[[1],[1,2]],[1,2]⟩,⟨[[2],[1,2]],[1,2]⟩],
    [1,2],0,[]⟩

private def roundtrip (r : Request) : Except String Unit := do
  let input ← Json.parse (toJson r).compress
  -- Search only the types the request mentions.
  let labels := ([0,1,2,3] ++ r.result ++ r.inputs.flatten ++
    r.claims.flatMap (fun (c : CertificateProducer.PointClaim Nat) => c.type ++ c.context.flatten)).eraseDups
  let evidence ← RequestJson.produceJson input 8 [] [] [] (some labels)
  verifyJson input (← Json.parse evidence.compress)

#guard ok (roundtrip (request .tru))
#guard ok (roundtrip (request .fls))
#guard !ok (roundtrip { request .tru with program := ((request .tru).program.set 1
  ⟨.var 0,.branchBind ⟨3,some [0,1]⟩ ⟨2,some [0,1]⟩⟩) })
#guard !ok (roundtrip { request .tru with claims := (request .tru).claims.set 3 ⟨[[1],[1,2]],[1,2]⟩ })
#guard !ok (roundtrip { request .tru with claims := (request .tru).claims.set 2 ⟨[[1],[1]],[1,2]⟩ })
#guard !ok (roundtrip { request .tru with program := ((request .tru).program.set 1
  ⟨.var 0,.branchBind ⟨2,some [1,0]⟩ ⟨3,some [0,1]⟩⟩) })
#guard !ok (roundtrip { request .tru with program := ((request .tru).program.set 1
  ⟨.var 0,.branchBind ⟨2,some [0,1]⟩ 99⟩) })
-- A possibly-null result is not accepted as a Boolean dispatch, even when this
-- particular source expression happens to evaluate to true.
#guard !ok (roundtrip { request .tru with claims := (request .tru).claims.set 1 ⟨[[1,2]],[0,1,2]⟩ })
-- Refining transfers also participate in cycles; checking requires no iteration.
#guard ok (roundtrip ⟨2,T,
  [⟨.tru,.bind 1⟩,⟨.var 0,.branchBind ⟨1,some [0]⟩ ⟨2,some [0]⟩⟩,⟨.var 0,.ret⟩],
  [⟨[],[1,2]⟩,⟨[[1,2]],[1,2]⟩,⟨[[2]],[1,2]⟩],[1,2],0,[]⟩)
-- Tag dispatch uses the same observed edge checker and retains the value itself.
private def tagRequest : Request :=
  ⟨2,T,
    [⟨.var 0,.tagBind .isNul ⟨1,some [0]⟩ ⟨2,some [0]⟩⟩,
     ⟨.fls,.ret⟩,⟨.var 0,.ret⟩],
    [⟨[[0,1,2]],[0,1,2]⟩,⟨[[0]],[1,2]⟩,⟨[[1,2]],[1,2]⟩],
    [1,2],0,[[0,1,2]]⟩
#guard ok (roundtrip tagRequest)
#guard !ok (roundtrip { tagRequest with program := (tagRequest.program.set 0
  ⟨.var 0,.tagBind .isBool ⟨1,some [0]⟩ ⟨2,some [0]⟩⟩) })
#guard !ok (roundtrip { tagRequest with program := (tagRequest.program.set 0
  ⟨.var 0,.tagBind .isNul ⟨1,some [1]⟩ ⟨2,some [0]⟩⟩) })
#guard !ok (roundtrip { tagRequest with program := (tagRequest.program.set 0
  ⟨.var 0,.tagBind .isNul 99 ⟨2,some [0]⟩⟩) })
-- Dispatch operates on the value, even at an empty heap or without an alias map.
example : Transition [] [] (.eval .nul (fun _ => .nul) (.tagBind .isNul 1 2)) []
    (.at 1 (PointClaims.mapEnv none (push .nul (fun _ => .nul)))) := .tagBind rfl
example : Transition [] [] (.eval .fls (fun _ => .nul) (.tagBind .isNul 1 2)) []
    (.at 2 (PointClaims.mapEnv none (push .fls (fun _ => .nul)))) := .tagBind rfl

end Verification.ExperimentState.BranchRefinementTests
