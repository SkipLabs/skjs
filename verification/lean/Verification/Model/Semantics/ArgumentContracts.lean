import Verification.Model.Semantics.Safety

/-! Same-level contracts on argument lists. Grouping evaluated arguments adds
no operational step; the call or constructor supplies the recursive guard. -/
namespace Verification.Model.ArgumentContracts

/-- A contract on an actual list; grouping values spends no execution step. -/
abbrev Family := ArgFam
abbrev Agree := @Model.Agree (List Val)
abbrev Admissible := @Adm (List Val)

/-- Homogeneous arguments retain the current approximation level. -/
def All (E : Fam) : ArgFam := fun n W vs => ∀ v ∈ vs, E n W v

theorem all_adm {E : Fam} (hE : Adm E) : Adm (All E) :=
  Adm.of_transfer (fun h j hj U hx v hv => hE.transfer (h v hv) j hj U hx)

/-- The same tuple shape as a store, interpreted on values at this level. -/
def Fits (T : TupleF) : Family := fun n W vs =>
  TupleFits (fun A v => A n W v) T vs

theorem fits_adm {T : TupleF}
    (hT : ∀ i A, positionFam T i = some A → Adm A) : Adm (Fits T) :=
  Adm.of_transfer (fun h j hj U hx =>
    h.map (fun i A hA v hv => (hT i A hA).transfer hv j hj U hx))

/-- Exact tuples and fixed parameters have identical membership, for arbitrary
families: objects, callbacks and recursive types need no stability premise. -/
theorem fits_exact (As : List Fam) (n W vs) :
    Fits ⟨As, [], none, false⟩ n W vs ↔ ArgsT As n W vs := by
  constructor
  · rintro ⟨hl, hb, hp⟩
    dsimp at hl hb
    have hlen : As.length = vs.length := by have := hb rfl; omega
    apply ArgsT_of_getElem? hlen
    intro i A v hA hv
    exact hp i v A hv (by simp [positionFam, hA])
  · intro ha
    have hl := ArgsT_length ha
    refine ⟨by simp [hl], by simp [hl], ?_⟩
    intro i v A hv hA
    have hi : i < As.length := by
      obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hv
      omega
    have he : As[i]? = some A := by
      simpa [positionFam, List.getElem?_eq_getElem hi] using hA
    exact ArgsT_getElem? ha he hv

/-- Same-level arguments still suffice for the existing allocation proof.
The loss of a level belongs to allocation, not to argument-list membership. -/
theorem fits_below {T : TupleF} (hT : ∀ i A, positionFam T i = some A → Adm A)
    {n W vs} (h : Fits T n W vs) : PackFits T n W vs :=
  ⟨h.1, h.2.1, fun i v A hv hA j hj U hx =>
    (hT i A hA).mono j _ U hx v
      ((hT i A hA).down_le n j (Nat.le_of_lt hj) W v (h.2.2 i v A hv hA))⟩

/-- Within a contract's bounds every index has a position. -/
theorem positionFam_isSome {T : TupleF} {i : Nat}
    (h : i < T.required.length + T.optional.length ∨ T.rest.isSome = true) :
    (positionFam T i).isSome = true := by
  unfold positionFam
  cases hr : T.required[i]? with
  | some A => rfl
  | none =>
    cases ho : T.optional[i - T.required.length]? with
    | some A => rfl
    | none =>
      rw [List.getElem?_eq_none_iff] at hr ho
      simp only
      rcases h with h | h
      · omega
      · rw [if_pos (by omega)]; exact h

/-- A tuple's element bound constrains the same-level argument values. -/
theorem fits_bound {T : TupleF} {E : Fam}
    (hb : ∀ i A, positionFam T i = some A → FamLe A E) {n W vs}
    (h : Fits T n W vs) : ∀ v ∈ vs, E n W v := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hs : (positionFam T i).isSome = true := by
    apply positionFam_isSome
    cases hr : T.rest with
    | none => have := h.2.1 hr; left; omega
    | some _ => right; rfl
  obtain ⟨A, hA⟩ := Option.isSome_iff_exists.mp hs
  exact hb i A hA n W _ (h.2.2 i _ A (List.getElem?_eq_getElem hi) hA)

/-- The identical element bound establishes the tuple's readonly array view.
Existing locations retain their write contracts; only reads are widened. -/
theorem array_bound {T : TupleF} {E : Fam}
    (hb : ∀ i A, positionFam T i = some A → FamLe A E) :
    FamLe (listT T) (listT ⟨[], [], some E, true⟩) := by
  intro n W v h
  obtain ⟨ls, rfl, hlen, hbound, hreq, hopt, hrest⟩ := h
  refine ⟨ls, rfl, by simp, by simp, by simp, by simp, ?_⟩
  intro i l _ hl
  have finish : ∀ A c, lookup W l = some c →
      positionFam T i = some A →
      (∀ j (hj : j < n) U u, SlotContract T.readonly (c j hj U u) (A j U u)) →
      ∃ F c, some E = some F ∧ lookup W l = some c ∧
        ∀ j (hj : j < n) U u, SlotContract true (c j hj U u) (F j U u) := by
    intro A c hc hA hs
    exact ⟨E, c, rfl, hc, fun j hj U u =>
      ⟨fun hu => hb i A hA j U u ((hs j hj U u).1 hu), by simp⟩⟩
  cases hr : T.required[i]? with
  | some A =>
    obtain ⟨l', c, hl', hc, hs⟩ := hreq i A hr
    have he : l = l' := by simpa [hl] using hl'
    subst he
    exact finish A c hc (by simp [positionFam, hr]) hs
  | none =>
    have hir : T.required.length ≤ i := List.getElem?_eq_none_iff.mp hr
    cases ho : T.optional[i - T.required.length]? with
    | some A =>
      obtain ⟨c, hc, hs⟩ := hopt (i - T.required.length) A l ho (by simpa [Nat.add_sub_of_le hir] using hl)
      exact finish A c hc (by simp [positionFam, hr, ho]) hs
    | none =>
      have hi : T.required.length + T.optional.length ≤ i := by
        have := List.getElem?_eq_none_iff.mp ho; omega
      obtain ⟨A, c, hA, hc, hs⟩ := hrest i l hi hl
      exact finish A c hc (by simp [positionFam, hr, ho, hi, hA]) hs

/-- One operational call promise for every argument-list presentation. -/
def callable (P : Family) (Rc R : Fam) : Fam := fun n W v =>
  Invocable v ∧ Promise P Rc R n W v

theorem callable_adm (P : Family) (Rc R : Fam) : Adm (callable P Rc R) :=
  ⟨fun _ _ _ h => ⟨h.1, h.2.down⟩, fun _ _ _ hx _ h => ⟨h.1, h.2.mono hx⟩⟩

theorem callable_congr {P Q : Family} {Rc Rc' R R' : Fam} {n : Nat}
    (hp : Agree P Q n) (hrc : Model.Agree Rc Rc' n) (hr : Model.Agree R R' n) (W v) :
    callable P Rc R n W v ↔ callable Q Rc' R' n W v :=
  and_congr Iff.rfl (Promise.congr hrc hp hr)

/-- Elimination uses the existing operational step and establishes `Safe`. -/
theorem call_safe {P : Family} {Rc R : Fam} (hP : Admissible P) (hRc : Adm Rc)
    {n W heap f r vs} (hf : callable P Rc R n W f) (hr : Rc n W r)
    (hrv : isVal r = true) (hv : CallArguments.Values vs) (ha : P n W vs)
    (hw : WorldAdm W) (hh : HeapOk n W heap) : Safe R n W heap (.invoke f r vs) := by
  cases n with
  | zero => trivial
  | succ n =>
    let U := trunc n (Nat.le_succ n) W
    obtain ⟨body, hi, hs⟩ := hf.2 n (Nat.lt_succ_self n) U (WExt_refl _)
      (WorldAdm_trunc _ hw) heap (HeapOk_trunc n W heap hh) r hrv (hRc.down n W r hr)
      vs hv (hP.transfer ha n (Nat.le_succ n) U (WExt_refl _))
    exact .inr ⟨U, heap, body, WExt_refl _, WorldAdm_trunc _ hw, hi.step heap,
      HeapOk_trunc n W heap hh, hs⟩

/-- Calls with exact tuple arguments are covered by the corresponding fixed
signature, even when a fixed signature additionally allows omitted undefined
arguments. No claim of equality is made for that optional-argument case. -/
theorem fixed_call_covers_tuple (As : List Fam) (Rc R : Fam) :
    FamLe (callsT [(Rc, As, R)]) (callable (Fits ⟨As, [], none, false⟩) Rc R) := by
  intro n W v h
  refine ⟨h.1, ?_⟩
  intro j hj U hx hu heap hh r hrv hr args hvals ha
  exact h.2 _ (List.mem_singleton_self _) j hj U hx hu heap hh r hrv hr args hvals
    (ArgsShort_of_exact ((fits_exact As j U args).mp ha))

/-- Constructor promises use the same argument-list contracts and the actual
constructor reduction; no synthetic runtime step is inserted. -/
def constructor (P : Family) (R : Fam) : Fam := fun n W v =>
  Constructible v ∧ ConstructPromise P R n W v

theorem constructor_adm (P : Family) (R : Fam) : Adm (constructor P R) :=
  ⟨fun _ _ _ h => ⟨h.1, fun j hj U hx hu heap hh args hv ha =>
      h.2 j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh args hv ha⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun j hj U hy hu heap hh args hv ha =>
      h.2 j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh args hv ha⟩⟩

/-- The desired general equation, without a stability side condition. -/
theorem fixed_constructor_eq_tuple (As : List Fam) (R : Fam) :
    ctorsT [(As, R)] = constructor (Fits ⟨As, [], none, false⟩) R := by
  funext n W v
  apply propext
  simp only [ctorsT, constructor, ConstructPromise, List.mem_singleton, forall_eq, fits_exact]

/-- The general equality uses the production variadic constructor contract,
with no primitive/stability premise and no encoded value standing for a list. -/
theorem fixed_constructor_eq_rest (As : List Fam) (R : Fam) :
    ctorsT [(As, R)] = ctorRestsT [([], Fits ⟨As, [], none, false⟩, R)] := by
  funext n W v
  apply propext
  simp [ctorsT, ctorRestsT, ConstructPromise, CtorRest, ArgsT, fits_exact]

/-- Constructor coverage is contravariant in the whole argument list. -/
theorem constructor_weaken {P Q : Family} {R S : Fam}
    (hP : ∀ n W vs, Q n W vs → P n W vs) (hR : FamLe R S) :
    FamLe (constructor P R) (constructor Q S) := by
  intro n W v h
  refine ⟨h.1, ?_⟩
  intro j hj U hx hu heap hh args hv ha
  obtain ⟨result, hi, hs⟩ := h.2 j hj U hx hu heap hh args hv (hP j U args ha)
  exact ⟨result, hi, Safe_mono j (fun m _ V u hm => hR m V u hm) U heap result hs⟩

theorem constructor_congr {P Q : Family} {R S : Fam} {n : Nat}
    (hP : Agree P Q n) (hR : Model.Agree R S n) (W v) :
    constructor P R n W v ↔ constructor Q S n W v := by
  constructor <;> rintro ⟨hc, h⟩ <;> refine ⟨hc, ?_⟩ <;>
    intro j hj U hx hu heap hh args hv ha
  · obtain ⟨r, hi, hs⟩ := h j hj U hx hu heap hh args hv ((hP j hj U args).mpr ha)
    exact ⟨r, hi, (Safe_congr n hR j hj U heap r).mp hs⟩
  · obtain ⟨r, hi, hs⟩ := h j hj U hx hu heap hh args hv ((hP j hj U args).mp ha)
    exact ⟨r, hi, (Safe_congr n hR j hj U heap r).mpr hs⟩

#print axioms array_bound
#print axioms fits_adm
#print axioms fits_exact
#print axioms call_safe
#print axioms fixed_call_covers_tuple
#print axioms fixed_constructor_eq_rest
#print axioms fixed_constructor_eq_tuple
#print axioms constructor_weaken
end Verification.Model.ArgumentContracts
