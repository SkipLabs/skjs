import Verification.Model.Source.SourceTypes

namespace Verification.Model.BranchRefinementTests
open Lean ProgramTyping ControlFlow RequestJson BranchRefinement

private def ok (r : Except String α) : Bool := match r with
  | .ok _ => true
  | .error _ => false
private def T : SourceTypes.Table := SourceTypes.initial ++ RequestJson.rows [[.refs [(valueField, [1,2])] [] []]]
private def G := SourceTypes.graph T

-- Tag observations split explicit unions without inventing a new type label.
#guard tagSlice G [0,1,2] .isNul true == [0]
#guard tagSlice G [0,1,2] .isNul false == [1,2]
#guard tagSlice G [0,1,2] .isBool true == [1,2]
#guard tagSlice G [0] .isNul false == []
-- Mixed labels are retained intact, rather than narrowed unsoundly by head shape.
private def mixed : PositiveGraphs.NormalGraph Nat := .ofRows fun _ => [.nul,.bool]
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
-- Filtering's precision limit does not restrict the semantic obligation, and
-- a passed test naming one family is covered by that family's clause
-- (`tagMember`), whatever the tested type was.
private def mixedWithNull : PositiveGraphs.NormalGraph Nat := .ofRows fun
  | 0 => [.nul,.bool]
  | _ => [.nul]
#guard checkObservedSub mixedWithNull [0] [1] (.tag .isNul true) .subset
#guard !checkObservedSub mixedWithNull [0] [1] (.tag .isNul false) .subset
example : ObservedSub mixedWithNull [0] [1] (.tag .isNul true) := by
  intro n W v _ ho
  have hn : v = .nul := by cases v <;> simp_all [Observation.holds, tagHolds, protoFree]
  subst v
  apply PositiveRules.expand_sem_mpr
  exact ⟨.nul, by simp [PositiveRules.clausesOf, mixedWithNull], rfl,
    PositiveGraphs.realmInvariant_of_not_record rfl _ _ _⟩

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
  ⟨T,
    [⟨v,.bind 1,none⟩, ⟨.var 0,.branchBind ⟨2,some [0,1]⟩ ⟨3,some [0,1]⟩,none⟩,
     ⟨.var 0,.ret,none⟩, ⟨.var 0,.ret,none⟩],
    [⟨[],[1,2]⟩,⟨[[1,2]],[1,2]⟩,⟨[[1],[1,2]],[1,2]⟩,⟨[[2],[1,2]],[1,2]⟩],
    [1,2],0,[], []⟩

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
  ⟨.var 0,.branchBind ⟨3,some [0,1]⟩ ⟨2,some [0,1]⟩,none⟩) })
#guard !ok (roundtrip { request .tru with claims := (request .tru).claims.set 3 ⟨[[1],[1,2]],[1,2]⟩ })
#guard !ok (roundtrip { request .tru with claims := (request .tru).claims.set 2 ⟨[[1],[1]],[1,2]⟩ })
#guard !ok (roundtrip { request .tru with program := ((request .tru).program.set 1
  ⟨.var 0,.branchBind ⟨2,some [1,0]⟩ ⟨3,some [0,1]⟩,none⟩) })
#guard !ok (roundtrip { request .tru with program := ((request .tru).program.set 1
  ⟨.var 0,.branchBind ⟨2,some [0,1]⟩ 99,none⟩) })
-- A possibly-null result is not accepted as a Boolean dispatch, even when this
-- particular source expression happens to evaluate to true.
#guard !ok (roundtrip { request .tru with claims := (request .tru).claims.set 1 ⟨[[1,2]],[0,1,2]⟩ })
-- Refining transfers also participate in cycles; checking requires no iteration.
#guard ok (roundtrip ⟨T,
  [⟨.tru,.bind 1,none⟩,⟨.var 0,.branchBind ⟨1,some [0]⟩ ⟨2,some [0]⟩,none⟩,⟨.var 0,.ret,none⟩],
  [⟨[],[1,2]⟩,⟨[[1,2]],[1,2]⟩,⟨[[2]],[1,2]⟩],[1,2],0,[], []⟩)
-- Tag dispatch uses the same observed edge checker and retains the value itself.
private def tagRequest : Request :=
  ⟨T,
    [⟨.var 0,.tagBind .isNul ⟨1,some [0]⟩ ⟨2,some [0]⟩,none⟩,
     ⟨.fls,.ret,none⟩,⟨.var 0,.ret,none⟩],
    [⟨[[0,1,2]],[0,1,2]⟩,⟨[[0]],[1,2]⟩,⟨[[1,2]],[1,2]⟩],
    [1,2],0,[[0,1,2]], []⟩
#guard ok (roundtrip tagRequest)
#guard !ok (roundtrip { tagRequest with program := (tagRequest.program.set 0
  ⟨.var 0,.tagBind .isBool ⟨1,some [0]⟩ ⟨2,some [0]⟩,none⟩) })
#guard !ok (roundtrip { tagRequest with program := (tagRequest.program.set 0
  ⟨.var 0,.tagBind .isNul ⟨1,some [1]⟩ ⟨2,some [0]⟩,none⟩) })
#guard !ok (roundtrip { tagRequest with program := (tagRequest.program.set 0
  ⟨.var 0,.tagBind .isNul 99 ⟨2,some [0]⟩,none⟩) })
-- Dispatch operates on the value, even at an empty heap or without an alias map.
example : Transition [] [] (.eval .nul (fun _ => .nul) (.tagBind .isNul 1 2) none) []
    (.at 1 (PointClaims.mapEnv none (push .nul (fun _ => .nul)))) := .tagBind rfl
example : Transition [] [] (.eval .fls (fun _ => .nul) (.tagBind .isNul 1 2) none) []
    (.at 2 (PointClaims.mapEnv none (push .fls (fun _ => .nul)))) := .tagBind rfl

-- `key in o` reads the prototype chain: a class instance holds its
-- prototype, whose method it lacks as an own key, and `in` finds it there.
private def protoHeap : List Tm := [.objAt [("m", 1)] .absent, .num 0, .num 1]
private def instanceWithProto : Tm := .objAt [("x", 2), ("[[proto]]", 0)] .absent
#guard tagHoldsIn protoHeap (.hasKey "m") instanceWithProto
#guard !tagHolds (.hasKey "m") instanceWithProto
#guard !tagHoldsIn protoHeap (.hasKey "n") instanceWithProto

-- The realm's array invariant, at boundaries no source reaches: a graph whose
-- realm's prototype is row 3, `sparse ReadonlyArray<unknown>` row 2 over the store of
-- values row 1, and an open record row 4.
private def realmG : PositiveGraphs.NormalGraph Nat :=
  { rows := fun
      | 0 => [.top]
      | 1 => [.list ⟨[], [], some [0], true, .sparse⟩ []]
      | 2 => [.refs [] [] [(CallArguments.arrayStoreField, [1]), (CallArguments.protoField, [3])] [] []
          [⟨false, []⟩]]
      | 3 => [.refs [] [] []]
      | 4 => [.refs [("a", [5])] [] []]
      | 5 => [.num]
      | _ => []
    realm := some ⟨[3], []⟩ }
#guard realmArrayLabel realmG 2
#guard !realmArrayLabel realmG 4
-- A record arm, where `Array.isArray` holds, is the realm's array; `unknown`
-- and a destination without that array are not.
#guard arraySlice realmG [4] [2]
#guard !arraySlice realmG [4] [4]
#guard !arraySlice realmG [0] [2]
-- An allocation owning the store key is an array of the realm, or refused.
#guard allocRealm realmG [(CallArguments.arrayStoreField, [1]), (CallArguments.protoField, [3])]
#guard !allocRealm realmG [(CallArguments.arrayStoreField, [5]), (CallArguments.protoField, [3])]
#guard !allocRealm realmG [(CallArguments.arrayStoreField, [1])]
#guard allocRealm realmG [("a", [5])]

end Verification.Model.BranchRefinementTests
