import Verification.ExperimentState.HeapObservations
import Verification.ExperimentState.CellUnion

/-! Semantic witnesses and counterexamples for current heap observations.
All terms run in the existing language. No source claims are reinterpreted here. -/
namespace Verification.ExperimentState.HeapObservationTests
open HeapObservations

/-- The generic observation rule works for a false write as well as a true write. -/
theorem write_then_read {n W h l} (hw : WorldAdm W) (hh : HeapOk n W h)
    (hr : refT boolT n W (.obj l .nul)) :
    SafePost (exact .fls) (fun h' u => Observes h' l .fls ∧ u = .fls) n W h
      (.app (.lam (.read (.obj l .nul))) (.write (.obj l .nul) .fls)) :=
  HeapObservations.write_then_read boolT_adm hw hh hr rfl (Or.inr rfl)

/-- The same read is precise before mutation, without strengthening Ref bool. -/
theorem before_write {n W h l} (hw : WorldAdm W) (hh : HeapOk n W h)
    (ho : Observes h l .tru) : Safe (exact .tru) n W h (.read (.obj l .nul)) :=
  erase (read_observed hw hh rfl ho)

/-- This closure is a valid ordinary null-to-null arrow in every future
admissible world/heap, despite overwriting the captured cell. -/
def writer (l : Nat) : Tm := .lam (.write (.obj l .nul) .fls)

theorem writer_arrow {n W l} (hr : refT boolT n W (.obj l .nul)) :
    arrowT nulT nulT n W (writer l) := by
  apply lam_intro _ _ _ (by simp [Scoped])
  intro j hj U hx hu h hh a ha
  change Safe nulT j U h (.write (.obj l .nul) .fls)
  exact erase (write_observed boolT_adm hu hh (refT_transfer hr j (by omega) U hx)
    rfl (Or.inr rfl))

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

theorem boolWorld_ref (n : Nat) : refT boolT n (boolWorld n) (.obj 0 .nul) :=
  ⟨0,res boolT,rfl,by simp [boolWorld,lookup],fun _ _ _ _ => Iff.rfl⟩

/-- Observations are not resource assertions: they can be duplicated, but a
write through any alias invalidates the old one. -/
theorem alias_write_changes_observation :
    Observes [.tru] 0 .tru ∧
    Observes (([.tru] : Heap).set 0 .fls) 0 .fls ∧
    ¬ Observes (([.tru] : Heap).set 0 .fls) 0 .tru := by
  simp [Observes]

/-- Even a well-typed callback cannot be given a generic observation frame.
Three levels see beta, the write, and the returned value/postcondition. -/
theorem callback_does_not_frame (W : WorldT 3) :
    ¬ SafePost nulT (fun h _ => Observes h 0 .tru) 3 W [.tru]
      (.app (writer 0) .nul) := by
  intro hs
  rcases hs with ⟨hv,_,_⟩ | ⟨U,h',t',hx,hu,step,hh,hs⟩
  · cases hv
  · have st : Step [.tru] (.app (writer 0) .nul) [.tru] (.write (.obj 0 .nul) .fls) := .beta rfl
    obtain ⟨rfl,rfl⟩ := Step_det st step
    rcases hs with ⟨hv,_,_⟩ | ⟨V,h'',t'',hx,hu,step,hh,hs⟩
    · cases hv
    · have st : Step [.tru] (.write (.obj 0 .nul) .fls) [.fls] .nul := .writeV rfl (by decide)
      obtain ⟨rfl,rfl⟩ := Step_det st step
      rcases hs with ⟨_,_,ho⟩ | ⟨_,_,_,_,_,step,_,_⟩
      · simp [Observes] at ho
      · exact value_no_step rfl step

/-- The observation counterexample has a genuinely inhabited, admissible input
world and a valid arrow. It is not a consequence of inconsistent assumptions. -/
theorem callback_counterexample :
    WorldAdm (boolWorld 3) ∧ HeapOk 3 (boolWorld 3) [.tru] ∧
    arrowT nulT nulT 3 (boolWorld 3) (writer 0) ∧
    Observes [.tru] 0 .tru ∧
    ¬ SafePost nulT (fun h _ => Observes h 0 .tru) 3 (boolWorld 3) [.tru]
      (.app (writer 0) .nul) :=
  ⟨boolWorld_adm 3,boolWorld_heap 3 .tru (Or.inl rfl),writer_arrow (boolWorld_ref 3),
    rfl,callback_does_not_frame _⟩

/-- The very same world admits true and false contents. Consequently no
heap-independent value family can characterize the current true observation. -/
theorem observation_not_a_value_type (T : Fam) :
    ¬ (∀ h, HeapOk 2 (boolWorld 2) h →
      (T 2 (boolWorld 2) (.obj 0 .nul) ↔ Observes h 0 .tru)) := by
  intro he
  have ht := (he [.tru] (boolWorld_heap 2 .tru (Or.inl rfl))).mpr rfl
  have hf := (he [.fls] (boolWorld_heap 2 .fls (Or.inr rfl))).mp ht
  simp [Observes] at hf

/-- IMPORTANT: a point observation does not permit changing the invariant.
The read/write capability preorder used for schema absorption is NOT automatically
an exact normalization for a future `Ref write AND current read` interpretation. -/
theorem observation_does_not_narrow_invariant :
    HeapOk 1 (boolWorld 1) [.tru] ∧ refT boolT 1 (boolWorld 1) (.obj 0 .nul) ∧
    Observes [.tru] 0 .tru ∧ ¬ refT (exact .tru) 1 (boolWorld 1) (.obj 0 .nul) := by
  refine ⟨boolWorld_heap 1 .tru (Or.inl rfl),boolWorld_ref 1,rfl,?_⟩
  rintro ⟨l,c,he,hl,hc⟩
  cases he
  simp [boolWorld,lookup] at hl
  subst c
  have hf := (hc 0 (by decide) (ofList []) .fls).mp (Or.inr rfl)
  cases hf

-- Different storage invariants are deliberately not absorbed. The theorem
-- above is the semantic regression guarding that restriction.
#guard CellUnion.normalize [⟨[1],[1,2]⟩,⟨[1],[1]⟩] = [⟨[1],[1,2]⟩,⟨[1],[1]⟩]

#print axioms observation_not_a_value_type
#print axioms observation_does_not_narrow_invariant
#print axioms write_then_read
#print axioms callback_counterexample
end Verification.ExperimentState.HeapObservationTests
