import Verification.ExperimentState.Rules
/-!
# Callable objects and their bags

A bag invariant forgets the call slot without changing the value. A callable
object combines that invariant with the existing overloaded call contracts.
The old reference family still denotes plain objects, so its disjointness and
certificate rules keep their existing meaning. The positive graph now exposes combined callable/property contracts through
`CallableConjunctions` and its `callable` clause.

This is the one-cell, closed-closure fragment: construction, receiver binding,
and property descriptors remain outside this fragment. `ObjectCoherence`
proves the separate identity/descriptor invariant for execution.
-/
namespace Verification.ExperimentState

/-- A writable bag invariant independent of the object's call slot. The plain
object in `refT` is only a semantic projection, never an allocation or coercion. -/
def bagT (P : Fam) : Fam := fun n W v =>
  ∃ l code, v = .obj l code ∧ isVal v = true ∧ refT P n W (.obj l .absent)

/-- Call and property contracts hold of the same object value. -/
def callableT (L : List (Fam × Fam)) (P : Fam) : Fam :=
  interT (bagT P) (arrowsT L)

theorem bagT_adm (P : Fam) : Adm (bagT P) := by
  constructor
  · rintro n W v ⟨l, code, hv, hval, hr⟩
    exact ⟨l, code, hv, hval, (refT_adm P).down n W _ hr⟩
  · rintro n W W' hx v ⟨l, code, hv, hval, hr⟩
    exact ⟨l, code, hv, hval, (refT_adm P).mono n W W' hx _ hr⟩

theorem bagT_valOnly (P : Fam) : ValOnly (bagT P) := by
  rintro n W v ⟨l, code, hv, hval, hr⟩
  exact hval

theorem bagT_contractive : Contractive bagT := by
  intro n P Q hag W v
  constructor <;> rintro ⟨l, code, hv, hval, hr⟩ <;> refine ⟨l, code, hv, hval, ?_⟩
  · exact (refT_contractive n P Q hag W _).mp hr
  · exact (refT_contractive n P Q hag W _).mpr hr

theorem refT_bag {P : Fam} {n W v} (h : refT P n W v) : bagT P n W v := by
  obtain ⟨l, c, rfl, hl, hc⟩ := h
  exact ⟨l, .absent, rfl, rfl, l, c, rfl, hl, hc⟩

theorem callableT_adm (L : List (Fam × Fam)) (P : Fam) : Adm (callableT L P) :=
  interT_adm _ _ (bagT_adm P) (arrowsT_adm L)

/-- Forgetting properties leaves the same callable and all its call contracts. -/
theorem callableT_calls {L P n W v} (h : callableT L P n W v) : arrowsT L n W v := h.2

theorem callableT_bag {L P n W v} (h : callableT L P n W v) : bagT P n W v := h.1

/-- An overload intersection is a conjunction of code obligations, with one bag
invariant; it does not impose incompatible writable types on the code. -/
theorem callableT_append (L M : List (Fam × Fam)) (P : Fam) (n W v) :
    callableT (L ++ M) P n W v ↔ interT (callableT L P) (callableT M P) n W v := by
  simp only [callableT, interT, arrowsT, List.mem_append]
  constructor
  · rintro ⟨hp, hc, hs⟩
    exact ⟨⟨hp, hc, fun p hm => hs p (Or.inl hm)⟩,
      ⟨hp, hc, fun p hm => hs p (Or.inr hm)⟩⟩
  · rintro ⟨⟨hp, hc, hs⟩, ⟨_, _, ht⟩⟩
    exact ⟨hp, hc, fun p hm => hm.elim (hs p) (ht p)⟩

theorem bag_read {P : Fam} (hP : ValOnly P) {n W h v}
    (hv : bagT P n W v) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe P n W h (.read v) := by
  obtain ⟨l, code, rfl, _, k, c, he, hl, hc⟩ := hv
  cases he
  exact read_rule (code := code) hP n W h l hw hh hl hc

theorem bag_write {P : Fam} (hP : Adm P) {n W h v a}
    (hv : bagT P n W v) (ha : P n W a) (hval : isVal a = true)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe nulT n W h (.write v a) := by
  obtain ⟨l, code, rfl, _, k, c, he, hl, hc⟩ := hv
  cases he
  exact write_rule (code := code) hP n W h l a hval hw hh hl hc ha

/-- Creation checks the code and the stored value separately, then allocates a
single fresh identity. The call contracts survive the extended world. -/
theorem attach_rule {P : Fam} {L : List (Fam × Fam)} (hA : Adm P)
    (n : Nat) (W : WorldT n) (h : Heap) (b v : Tm)
    (hf : CodeSpec L n W b) (hval : isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hv : P n W v) :
    Safe (callableT L P) n W h (.attach b v) := by
  apply make_rule hA n W h (.closure b) v hval hadm hok hv
  intro j hj U hx hr
  have hf' : arrowsT L j U (.obj h.length (.closure b)) :=
    (arrowsT_adm L).mono j _ U hx _ ((arrowsT_adm L).down_le n j
      (Nat.le_of_lt hj) W _ ((arrowsT_code_iff L h.length b n W).mpr hf))
  exact ⟨⟨h.length, .closure b, rfl, rfl, hr⟩, hf'⟩

#print axioms Callable.step
#print axioms bagT_contractive
#print axioms callableT_adm
#print axioms callableT_append
#print axioms bag_read
#print axioms bag_write
#print axioms attach_rule

end Verification.ExperimentState
