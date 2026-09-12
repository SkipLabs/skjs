import Verification.ExperimentState.Types
/-!
# Heaps and their invariant

The world says what a location is for; the heap says what it holds. `HeapOk`
relates them: every declared location holds a value meeting its contract, at
every level below the current one, with the world truncated to that level.

Membership never inspects the heap, only the world. That is the point of the
whole construction: a write cannot disturb any claim, so preservation reduces to
a local check at the location written -- and allocation preserves the invariant
provided the world's contracts are admissible, which is a property of the
contracts and not of any one type constructor.
-/
namespace Verification
namespace ExperimentState

def HeapOk (n : Nat) (W : WorldT n) (h : Heap) : Prop :=
  h.length = (toList W).length ∧
    ∀ l c, lookup W l = some c →
      ∃ v, h[l]? = some v ∧ ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v

/-- Heap satisfaction survives dropping a level, with the world truncated. -/
theorem HeapOk_trunc (n : Nat) (W : WorldT (n + 1)) (h : Heap)
    (hok : HeapOk (n + 1) W h) : HeapOk n (trunc n (Nat.le_succ n) W) h := by
  obtain ⟨hlen, hall⟩ := hok
  refine ⟨by simpa [trunc, lookup] using hlen, ?_⟩
  intro l c hl
  simp only [lookup, trunc, toList_ofList, List.getElem?_map] at hl
  rcases hd : (toList W)[l]? with _ | d
  · rw [hd] at hl; simp at hl
  · rw [hd] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    subst hl
    obtain ⟨v, hv, hmem⟩ := hall l d (by simpa [lookup] using hd)
    refine ⟨v, hv, ?_⟩
    intro j hj
    rw [trunc_trunc]
    exact hmem j (by omega)

/-- A read yields a value meeting the location's contract, at every level below
the current one. -/
theorem read_sound (n : Nat) (W : WorldT n) (h : Heap) (l : Nat) (c : Ctr n)
    (hok : HeapOk n W h) (hl : lookup W l = some c) :
    ∃ v, h[l]? = some v ∧ ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v :=
  hok.2 l c hl

/-- A write meeting the contract preserves satisfaction, including when the
location is aliased: no other location's obligation mentions the heap. -/
theorem write_sound (n : Nat) (W : WorldT n) (h : Heap) (l : Nat) (c : Ctr n) (v : Val)
    (hok : HeapOk n W h) (hl : lookup W l = some c)
    (hv : ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) W) v) :
    HeapOk n W (h.set l v) := by
  obtain ⟨hlen, hall⟩ := hok
  refine ⟨by simpa using hlen, ?_⟩
  intro k d hk
  by_cases hkl : k = l
  · subst hkl
    rw [hl] at hk; cases hk
    refine ⟨v, ?_, hv⟩
    have hlt : k < h.length := by
      have := (List.getElem?_eq_some_iff.mp hl).1
      simp only [lookup] at hl
      omega
    simp [hlt]
  · obtain ⟨w, hw, hmem⟩ := hall k d hk
    exact ⟨w, by rwa [List.getElem?_set_ne (fun hc => hkl hc.symm)], hmem⟩

/-- **Allocation preserves satisfaction — and this is where admissibility is
needed.** Every existing location's obligation is stated against a contract that
must survive the world growing, which is a property of the contracts, not of any
one type constructor. -/
theorem heap_alloc (n : Nat) (W : WorldT n) (h : Heap) (c : Ctr n) (v : Val)
    (hok : HeapOk n W h) (hadm : WorldAdm W)
    (hv : ∀ (j : Nat) (hj : j < n), c j hj (trunc j (Nat.le_of_lt hj) (appendW W c)) v) :
    HeapOk n (appendW W c) (h ++ [v]) := by
  obtain ⟨hlen, hall⟩ := hok
  refine ⟨by simp [appendW, hlen], ?_⟩
  intro l d hl
  have hl' : (toList W ++ [c])[l]? = some d := by simpa [lookup, appendW] using hl
  by_cases hlt : l < (toList W).length
  · rw [List.getElem?_append_left hlt] at hl'
    have hlW : lookup W l = some d := by simpa [lookup] using hl'
    obtain ⟨w, hw, hmem⟩ := hall l d hlW
    refine ⟨w, by rw [List.getElem?_append_left (by omega)]; exact hw, ?_⟩
    intro j hj
    exact hadm l d hlW j hj _ _
      (WExt_trunc (Nat.le_of_lt hj) (WExt_appendW W c)) w (hmem j hj)
  · have hb : l < (toList W).length + 1 := by
      have := (List.getElem?_eq_some_iff.mp hl').1; simpa using this
    have hll : l = (toList W).length := by omega
    subst hll
    rw [List.getElem?_append_right (Nat.le_refl _)] at hl'
    simp at hl'
    subst hl'
    refine ⟨v, ?_, hv⟩
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]

/-! ## An inhabited cyclic heap -/


/-- **The cyclic heap.** One location, whose contract is `R`, holding a
reference to itself -- and the heap really satisfies the world. -/
theorem cyclic_heap_ok (n : Nat) : HeapOk n (ofList [res R]) [Tm.obj 0 .absent] := by
  refine ⟨by simp, ?_⟩
  intro l c hl
  simp only [lookup, toList_ofList] at hl
  cases l with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    refine ⟨.obj 0 .absent, rfl, ?_⟩
    intro j hj
    show R j _ _
    rw [trunc_res]
    exact R_cyclic j
  | succ k => simp at hl

/-- The cyclic world only holds admissible contracts, so it can carry a heap. -/
theorem cyclic_world_adm (n : Nat) : WorldAdm (ofList [res R] : WorldT n) := by
  intro l c hl
  simp only [lookup, toList_ofList] at hl
  cases l with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
    subst hl
    intro j _ W W' hx v hv
    exact R_adm.mono j W W' hx v hv
  | succ k => simp at hl

theorem emptyHeapOk (j : Nat) : HeapOk j (ofList ([] : List (Ctr j))) [] := by
  refine ⟨by simp, ?_⟩
  intro l c hl
  simp [lookup] at hl

/-- Heap satisfaction survives truncation to any lower level, not just one. -/
theorem heap_down {n : Nat} {U : WorldT n} {h : Heap} (hh : HeapOk n U h)
    (j : Nat) (hj : j ≤ n) : HeapOk j (trunc j hj U) h := by
  induction n generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst j
    simpa [trunc_id] using hh
  | succ n ih =>
    by_cases he : j = n + 1
    · subst j; simpa [trunc_id] using hh
    · have hh' := HeapOk_trunc n U h hh
      have := ih hh' j (by omega)
      simpa [trunc_trunc] using this

end ExperimentState
end Verification
