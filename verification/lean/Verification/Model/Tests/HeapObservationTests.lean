import Verification.Model.Semantics.HeapObservations
import Verification.Model.Types.CellUnion

/-! Semantic witnesses and counterexamples for current heap observations.
All terms run in the existing language. No source claims are reinterpreted here. -/
namespace Verification.Model.HeapObservationTests
open HeapObservations

/-- The generic observation rule works for a false write as well as a true write. -/
theorem write_then_read {n W h l} (hw : WorldAdm W) (hh : HeapOk n W h)
    (hr : refT boolT n W (.obj l .absent)) :
    SafePost (exact .fls) (fun h' u => Observes h' l .fls ∧ u = .fls) n W h
      (.letE (.write (.obj l .absent) .fls) (.read (.obj l .absent))) :=
  HeapObservations.write_then_read boolT_adm hw hh hr rfl (Or.inr rfl)

/-- The same read is precise before mutation, without strengthening Ref bool. -/
theorem before_write {n W h l} (hw : WorldAdm W) (hh : HeapOk n W h)
    (ho : Observes h l .tru) : Safe (exact .tru) n W h (.read (.obj l .absent)) :=
  erase (read_observed hw hh (lookup_value _) rfl ho)

/-- A callback overwriting a cell it names: graph code of one node, taking one
parameter. -/
def writer (l : Nat) : Tm := .obj 1 (.graph 1 [.write (.obj l .absent) .fls] [(.ret, none)] 0 [])

/-- The persistent Boolean world admits both heaps at every budget. -/
def boolWorld (n : Nat) : WorldT n := ofList [res boolT]

theorem boolWorld_adm (n : Nat) : WorldAdm (boolWorld n) := by
  intro l c hl j hj U U' hx v hv
  cases l with
  | zero => simp [boolWorld,lookup] at hl; subst c; exact hv
  | succ l => simp [boolWorld,lookup] at hl

theorem boolWorld_heap (n : Nat) (v : Val) (hv : v = .tru ∨ v = .fls) :
    HeapOk n (boolWorld n) [v] := by
  constructor
  · simp [boolWorld]
  · intro l c hl
    cases l with
    | zero =>
      simp [boolWorld,lookup] at hl; subst c
      exact ⟨v,rfl,fun _ _ => hv⟩
    | succ l => simp [boolWorld,lookup] at hl

theorem boolWorld_ref (n : Nat) : refT boolT n (boolWorld n) (.obj 0 .absent) :=
  refT_cell (c := res boolT) (by simp [boolWorld,lookup]) (fun _ _ _ _ => Iff.rfl)

/-- Observations are not resource assertions: they can be duplicated, but a
write through any alias invalidates the old one. -/
theorem alias_write_changes_observation :
    Observes [.tru] 0 .tru ∧
    Observes (([.tru] : Heap).set 0 .fls) 0 .fls ∧
    ¬ Observes (([.tru] : Heap).set 0 .fls) 0 .tru := by
  simp [Observes]

/-- A callback cannot be given a generic observation frame: one of type
`(x: null) => null` may overwrite the observed cell. Five levels see the call
enter the code, its node, the write, the run returning, and the returned
value/postcondition. -/
theorem callback_does_not_frame (W : WorldT 5) :
    ¬ SafePost nulT (fun h _ => Observes h 0 .tru) 5 W [.tru]
      (.app (writer 0) .nul) := by
  intro hs
  have s1 : Step [.tru] (.app (writer 0) .nul) [.tru] _ := .callGraph rfl (by decide)
  rcases hs with (⟨hv,_,_⟩ | hr) | ⟨_,_,_,_,_,step,_,hs⟩
  · cases hv
  · exact hr.no_step s1
  obtain ⟨rfl,rfl⟩ := Step_det s1 step
  have s2 : Step [.tru] (CallArguments.graphEntry 1 [.write (.obj 0 .absent) .fls] [(.ret, none)]
      0 [] false .undef [.nul]) [.tru] _ := .gotoEnter rfl rfl
  rcases hs with (⟨hv,_,_⟩ | hr) | ⟨_,_,_,_,_,step,_,hs⟩
  · cases hv
  · exact hr.no_step s2
  obtain ⟨rfl,rfl⟩ := Step_det s2 step
  have s3 : Step [.tru] (.frame [.write (.obj 0 .absent) .fls] [(.ret, none)]
      (.write (.obj 0 .absent) .fls) [.undef, .nul] .nul .ret none) [.fls] _ :=
    .frameC (.writeV rfl (by decide))
  rcases hs with (⟨hv,_,_⟩ | hr) | ⟨_,_,_,_,_,step,_,hs⟩
  · cases hv
  · exact hr.no_step s3
  obtain ⟨rfl,rfl⟩ := Step_det s3 step
  have s4 : Step [.fls] (.frame [.write (.obj 0 .absent) .fls] [(.ret, none)]
      .nul [.undef, .nul] .nul .ret none) [.fls] .nul := .frameRet rfl
  rcases hs with (⟨hv,_,_⟩ | hr) | ⟨_,_,_,_,_,step,_,hs⟩
  · cases hv
  · exact hr.no_step s4
  obtain ⟨rfl,rfl⟩ := Step_det s4 step
  rcases hs with (⟨_,_,ho⟩ | hr) | ⟨_,_,_,_,_,step,_,_⟩
  · simp [Observes] at ho
  · exact val_not_thrown rfl hr
  · exact value_no_step rfl step

/-- The very same world admits true and false contents. Consequently no
heap-independent value family can characterize the current true observation. -/
theorem observation_not_a_value_type (T : Fam) :
    ¬ (∀ h, HeapOk 2 (boolWorld 2) h →
      (T 2 (boolWorld 2) (.obj 0 .absent) ↔ Observes h 0 .tru)) := by
  intro he
  have ht := (he [.tru] (boolWorld_heap 2 .tru (Or.inl rfl))).mpr rfl
  have hf := (he [.fls] (boolWorld_heap 2 .fls (Or.inr rfl))).mp ht
  simp [Observes] at hf

/-- IMPORTANT: a point observation does not permit changing the invariant.
The read/write capability preorder used for schema absorption is NOT automatically
an exact normalization for a future `Ref write AND current read` interpretation. -/
theorem observation_does_not_narrow_invariant :
    HeapOk 1 (boolWorld 1) [.tru] ∧ refT boolT 1 (boolWorld 1) (.obj 0 .absent) ∧
    Observes [.tru] 0 .tru ∧ ¬ refT (exact .tru) 1 (boolWorld 1) (.obj 0 .absent) := by
  refine ⟨boolWorld_heap 1 .tru (Or.inl rfl),boolWorld_ref 1,rfl,?_⟩
  intro hr
  obtain ⟨flds,l,c,he,hf,hl,hc⟩ := refT_iff.mp hr
  cases he
  simp at hf
  subst l
  simp [boolWorld,lookup] at hl
  subst c
  have hf := (hc 0 (by decide) (ofList []) .fls).mp (Or.inr rfl)
  cases hf

-- Different storage invariants are deliberately not absorbed. The theorem
-- above is the semantic regression guarding that restriction.
#guard CellUnion.normalize [[⟨valueField,[1],[1,2]⟩],[⟨valueField,[1],[1]⟩]] = [[⟨valueField,[1],[1,2]⟩],[⟨valueField,[1],[1]⟩]]

#print axioms observation_not_a_value_type
#print axioms observation_does_not_narrow_invariant
#print axioms write_then_read
#print axioms callback_does_not_frame
end Verification.Model.HeapObservationTests
