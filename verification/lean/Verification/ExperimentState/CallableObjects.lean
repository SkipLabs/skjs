import Verification.ExperimentState.Rules
import Verification.ExperimentState.ReferenceConjunctions
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
def bagT (P : Fields) : Fam := fun n W v =>
  ∃ flds code, v = .objAt flds code ∧ isVal v = true ∧ recT P n W (.objAt flds .absent)

/-- Call and property contracts hold of the same object value. -/
def callableT (L : List (Fam × Fam)) (P : Fields) : Fam :=
  interT (bagT P) (arrowsT L)

theorem bagT_adm (P : Fields) : Adm (bagT P) := by
  constructor
  · rintro n W v ⟨l, code, hv, hval, hr⟩
    exact ⟨l, code, hv, hval, (recT_adm P).down n W _ hr⟩
  · rintro n W W' hx v ⟨l, code, hv, hval, hr⟩
    exact ⟨l, code, hv, hval, (recT_adm P).mono n W W' hx _ hr⟩

theorem bagT_valOnly (P : Fields) : ValOnly (bagT P) := by
  rintro n W v ⟨l, code, hv, hval, hr⟩
  exact hval

theorem bagT_contractive {ι : Type} (X Y : ι → Fam) (fs : List (String × ι)) (n : Nat)
    (hag : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    bagT (ReferenceConjunctions.famsOf X fs) n W v ↔
      bagT (ReferenceConjunctions.famsOf Y fs) n W v := by
  constructor <;> rintro ⟨l, code, hv, hval, hr⟩ <;> refine ⟨l, code, hv, hval, ?_⟩
  · exact (ReferenceConjunctions.recT_congr_below X Y fs n hag W _).mp hr
  · exact (ReferenceConjunctions.recT_congr_below X Y fs n hag W _).mpr hr

theorem recT_bag {P : Fields} {n W v} (h : recT P n W v) : bagT P n W v := by
  obtain ⟨flds, rfl, hr⟩ := h
  exact ⟨flds, .absent, rfl, rfl, flds, rfl, hr⟩

theorem callableT_adm (L : List (Fam × Fam)) (P : Fields) : Adm (callableT L P) :=
  interT_adm _ _ (bagT_adm P) (arrowsT_adm L)

/-- Forgetting properties leaves the same callable and all its call contracts. -/
theorem callableT_calls {L P n W v} (h : callableT L P n W v) : arrowsT L n W v := h.2

theorem callableT_bag {L P n W v} (h : callableT L P n W v) : bagT P n W v := h.1

/-- An overload intersection is a conjunction of code obligations, with one bag
invariant; it does not impose incompatible writable types on the code. -/
theorem callableT_append (L M : List (Fam × Fam)) (P : Fields) (n W v) :
    callableT (L ++ M) P n W v ↔ interT (callableT L P) (callableT M P) n W v := by
  simp only [callableT, interT, arrowsT, List.mem_append]
  constructor
  · rintro ⟨hp, hc, hs⟩
    exact ⟨⟨hp, hc, fun p hm => hs p (Or.inl hm)⟩,
      ⟨hp, hc, fun p hm => hs p (Or.inr hm)⟩⟩
  · rintro ⟨⟨hp, hc, hs⟩, ⟨_, _, ht⟩⟩
    exact ⟨hp, hc, fun p hm => hm.elim (hs p) (ht p)⟩

theorem bag_read {fs : Fields} {f : String} {P : Fam} (hP : ValOnly P)
    (hm : (f, P) ∈ fs) {n W h v}
    (hv : bagT fs n W v) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe P n W h (.readAt f v) := by
  obtain ⟨flds, code, rfl, _, hr⟩ := hv
  obtain ⟨flds', l, c, he, hf, hl, hc⟩ := recT_at hm hr
  cases he
  exact read_rule (code := code) hP n W h l hw hh hf hl hc

theorem bag_write {fs : Fields} {f : String} {P : Fam} (hP : Adm P)
    (hm : (f, P) ∈ fs) {n W h v a}
    (hv : bagT fs n W v) (ha : P n W a) (hval : isVal a = true)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe nulT n W h (.writeAt f v a) := by
  obtain ⟨flds, code, rfl, _, hr⟩ := hv
  obtain ⟨flds', l, c, he, hf, hl, hc⟩ := recT_at hm hr
  cases he
  exact write_rule (code := code) hP n W h l a hval hw hh hf hl hc ha

/-- Native creation preserves every list signature across allocation. -/
theorem make_callable_rule {P : Fam} {L : List (List Fam × Fam)} (hA : Adm P)
    (arity n : Nat) (W : WorldT n) (h : Heap) (b v : Tm)
    (hf : InvocationSpec arity L n W b) (hval : isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hv : P n W v) :
    Safe (interT (bagT [(valueField, P)]) (callsT L)) n W h (.make (.closure arity b) v) := by
  apply make_rule hA n W h (.closure arity b) v hval hadm hok hv
  intro j hj U hx hr
  have hf' := (callsT_adm L).mono j _ U hx _ ((callsT_adm L).down_le n j
    (Nat.le_of_lt hj) W _ ((callsT_code_iff L arity [(valueField, h.length)] b n W).mpr hf))
  exact ⟨⟨_, .closure arity b, rfl, rfl, hr⟩, hf'⟩

/-- The same, for a bag with any named fields. The call contracts survive the
extended world exactly as they do for one field; nothing here depends on the
arity of the bag or on what its fields are called. -/
theorem make_callable_fields_rule {P : List Fam} {L : List (List Fam × Fam)}
    (hA : ∀ A ∈ P, Adm A) (arity n : Nat) (W : WorldT n) (h : Heap)
    (ns : List String) (vs : List Val) (b : Tm)
    (hnd : ns.Nodup) (hns : ns.length = vs.length) (hPs : P.length = vs.length)
    (hf : InvocationSpec arity L n W b) (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hv : ∀ p ∈ P.zip vs, p.1 n W p.2) :
    Safe (interT (bagT (ns.zip P)) (callsT L)) n W h
      (.makeAt (.closure arity b) ns vs) := by
  apply make_fields_rule hA n W h (.closure arity b) ns vs hnd hns hPs hvals hadm hok hv
  intro j hj U hx hrec
  have hf' := (callsT_adm L).mono j _ U hx _ ((callsT_adm L).down_le n j
    (Nat.le_of_lt hj) W _ ((callsT_code_iff L arity (slots h.length ns) b n W).mpr hf))
  exact ⟨⟨_, .closure arity b, rfl, rfl, hrec⟩, hf'⟩

/-- Creation checks the code and the stored value separately, then allocates a
single fresh identity. The call contracts survive the extended world. -/
theorem attach_rule {P : Fam} {L : List (Fam × Fam)} (hA : Adm P)
    (n : Nat) (W : WorldT n) (h : Heap) (b v : Tm)
    (hf : CodeSpec L n W b) (hval : isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hv : P n W v) :
    Safe (callableT L [(valueField, P)]) n W h (.attach b v) := by
  apply make_rule hA n W h (.closure 1 b) v hval hadm hok hv
  intro j hj U hx hr
  have hf' : arrowsT L j U (.obj h.length (.closure 1 b)) :=
    (arrowsT_adm L).mono j _ U hx _ ((arrowsT_adm L).down_le n j
      (Nat.le_of_lt hj) W _ ((arrowsT_code_iff L [(valueField, h.length)] b n W).mpr hf))
  exact ⟨⟨_, .closure 1 b, rfl, rfl, hr⟩, hf'⟩

#print axioms Callable.step
#print axioms bagT_contractive
#print axioms callableT_adm
#print axioms callableT_append
#print axioms bag_read
#print axioms bag_write
#print axioms make_callable_rule
#print axioms attach_rule

end Verification.ExperimentState
