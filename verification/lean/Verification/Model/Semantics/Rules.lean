import Verification.Model.Semantics.Safety
/-!
# Compatibility rules

The rules a program's safety proof should be assembled from, rather than traced
by hand. Application spends the beta step and uses the function guarantee one level
below the current budget. Abstraction proves the substituted body safe.

`Safe_bind_appR` is the bind: run a subterm, then continue with whatever value it
produces, in whatever world and heap it produced them. It is what lets composite
programs be built compositionally.
-/
namespace Verification
namespace Model

/-- The invocation code of an existing object establishes safety at every smaller
budget. Application, rather than this obligation, spends the beta step. The
body is under the frame `[this, x]`: a plain application binds `undefined` in
slot 0 and the argument in slot 1. -/
theorem fn_intro {l : Nat} {A B : Fam} (b : Tm) (k : Nat) (W : WorldT k) (hc : Scoped 2 b)
    (h : ∀ (j : Nat) (hj : j < k) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U → WorldAdm U →
      ∀ (heap : Heap), HeapOk j U heap → ∀ a, A j U a →
        Safe B j U heap (subst 0 .undef (subst 1 a b))) : arrowT A B k W (.fn l b) := by
  refine ⟨⟨1, b, _, rfl, hc⟩, ?_⟩
  intro j hj U hx hu heap hh a ha
  simpa [callBody, CallArguments.bindParameters, CallArguments.parameters, bindArgs]
    using h j hj U hx hu heap hh a ha

/-- Ready native list calls consume one step, then satisfy the chosen result
contract. The receiver's contract and the domains transfer the saved receiver
and actuals to that smaller budget. -/
theorem call_elim {L : List (Fam × List Fam × Fam)} {p : Fam × List Fam × Fam}
    (hR : Adm p.1) (hA : ∀ A ∈ p.2.1, Adm A) (hAv : ∀ A ∈ p.2.1, ValOnly A)
    {n : Nat} {W : WorldT n} {f r : Tm} {args : List Tm} {heap : Heap}
    (hrv : isVal r = true) (hf : callsT L n W f) (hp : p ∈ L) (hr : p.1 n W r)
    (ha : ArgsT p.2.1 n W args)
    (hw : WorldAdm W) (hh : HeapOk n W heap) : Safe p.2.2 n W heap (.invoke f r args) := by
  cases n with
  | zero => trivial
  | succ n =>
    let U := trunc n (Nat.le_succ n) W
    have hu : WorldAdm U := WorldAdm_trunc _ hw
    have hh' : HeapOk n U heap := HeapOk_trunc n W heap hh
    have ha' := ArgsT_transfer hA ha n (Nat.le_succ n) U (WExt_refl _)
    have hr' : p.1 n U r := hR.down n W r hr
    obtain ⟨body, hi, hs⟩ := callsT_invoke hf hp (Nat.lt_succ_self n)
      (WExt_refl _) hu hh' hrv hr' hAv ha'
    exact Or.inr ⟨U, heap, body, WExt_refl _, hu, hi.step heap, hh', hs⟩

/-- A ready call that omits trailing actuals. Every omitted position's contract
admits `undefined`, which is the value the machine binds there, so the selected
signature covers the padded list and the same body runs. -/
theorem call_elim_short {L : List (Fam × List Fam × Fam)} {p : Fam × List Fam × Fam}
    (hR : Adm p.1) (hA : ∀ A ∈ p.2.1, Adm A) (hAv : ∀ A ∈ p.2.1, ValOnly A)
    {n : Nat} {W : WorldT n} {f r : Tm} {args pad : List Tm} {heap : Heap}
    (hpad : ∀ a ∈ pad, a = .undef) (hrv : isVal r = true)
    (hf : callsT L n W f) (hp : p ∈ L) (hr : p.1 n W r) (ha : ArgsT p.2.1 n W (args ++ pad))
    (hw : WorldAdm W) (hh : HeapOk n W heap) : Safe p.2.2 n W heap (.invoke f r args) := by
  cases n with
  | zero => trivial
  | succ n =>
    let U := trunc n (Nat.le_succ n) W
    have hu : WorldAdm U := WorldAdm_trunc _ hw
    have hh' : HeapOk n U heap := HeapOk_trunc n W heap hh
    have ha' := ArgsT_transfer hA ha n (Nat.le_succ n) U (WExt_refl _)
    have hr' : p.1 n U r := hR.down n W r hr
    obtain ⟨body, hi, hs⟩ := callsT_invoke_short hf hp (Nat.lt_succ_self n)
      (WExt_refl _) hu hh' hrv hr' hpad hAv ha'
    exact Or.inr ⟨U, heap, body, WExt_refl _, hu, hi.step heap, hh', hs⟩

/-- Same-budget application compatibility, the rule needed for the fundamental
 theorem under semantic environments. Both values are available at the current
budget; beta consumes one step and uses the function guarantee below it. -/
theorem app_elim {A B : Fam} (hA : Adm A) (hAv : ValOnly A)
    {n : Nat} {W : WorldT n} {f a : Tm} {heap : Heap}
    (hf : arrowT A B n W f) (ha : A n W a)
    (hw : WorldAdm W) (hh : HeapOk n W heap) : Safe B n W heap (.app f a) := by
  apply call_elim (L := [(undefT, [A], B)]) (p := (undefT, [A], B)) undefT_adm
    (by simpa using hA) (by simpa using hAv) rfl
  · exact callsT_of_arrowsT (L := [(A, B)]) ((arrowsT_singleton A B n W f).mpr hf)
  · simp
  · rfl
  · exact ⟨ha, trivial⟩
  · exact hw
  · exact hh

/-- **Beta.** -/
theorem beta_rule {l : Nat} {B : Fam} (b a : Tm) (hval : isVal a = true) (p : Nat) (W : WorldT (p + 1))
    (h : Heap) (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h)
    (hb : Safe B p (trunc p (Nat.le_succ p) W) h (subst 0 .undef (subst 1 a b))) :
    Safe B (p + 1) W h (.app (.fn l b) a) :=
  Or.inr ⟨_, h, _, WExt_refl _, WorldAdm_trunc _ hadm, .beta hval,
    HeapOk_trunc p W h hok, by
      simpa [CallArguments.bindParameters, CallArguments.parameters, bindArgs] using hb⟩

/-- A binding consumes one step after its initializer has become a value. -/
theorem let_rule {B : Fam} (b a : Tm) (hval : isVal a = true) (p : Nat) (W : WorldT (p + 1))
    (h : Heap) (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h)
    (hb : Safe B p (trunc p (Nat.le_succ p) W) h (subst 0 a b)) :
    Safe B (p + 1) W h (.letE a b) :=
  Or.inr ⟨_, h, _, WExt_refl _, WorldAdm_trunc _ hadm, .letV hval,
    HeapOk_trunc p W h hok, hb⟩

/-- **Evaluation inside the argument of an application.** The bind rule the
composite programs need: run the argument, then continue with whatever value it
produces, in whatever world and heap it produced them. -/
theorem Safe_bind_appR {A B : Fam} (f : Tm) (hfv : isVal f = true) :
    ∀ (n : Nat) (W : WorldT n) (h : Heap) (a : Tm),
      WorldAdm W → HeapOk n W h → Safe A n W h a →
      (∀ (j : Nat) (hj : j ≤ n) (W' : WorldT j), WExt (trunc j hj W) W' → WorldAdm W' →
        ∀ (h' : Heap) (v : Tm), HeapOk j W' h' → A j W' v → Safe B j W' h' (.app f v)) →
      Safe B n W h (.app f a) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _; trivial
  | succ p ih =>
    intro W h a hadm hok hsafe hcont
    rcases hsafe with ⟨hv, hA⟩ | ⟨W', h', a', hx, hadm', hstep, hok', hsafe'⟩
    · exact hcont (p + 1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hadm h a hok hA
    · refine Or.inr ⟨W', h', .app f a', hx, hadm', .appR hfv hstep, hok', ?_⟩
      refine ih W' h' a' hadm' hok' hsafe' ?_
      intro j hj W'' hW hadm'' h'' v hok'' hAv
      refine hcont j (by omega) W'' ?_ hadm'' h'' v hok'' hAv
      refine WExt_trans ?_ hW
      have : trunc j hj W' = trunc j hj W' := rfl
      have hx' : WExt (trunc j hj (trunc p (Nat.le_succ p) W)) (trunc j hj W') :=
        WExt_trunc hj hx
      rwa [trunc_trunc] at hx'

/-! ## Storage -/


/-- **Read.** -/
theorem read_rule {code : CallCode} {flds : List (String × Nat)} {f : String} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hf : flds.lookup f = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u) :
    Safe A n W h (.readAt f (.objAt flds code)) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.2 l c hl
    have hAv : A p (trunc p (Nat.le_succ p) W) v := (hag p (by omega) _ v).mp (hmem p (by omega))
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, v, WExt_refl _,
      WorldAdm_trunc _ hadm, .readField hf hv, HeapOk_trunc p W h hok, ?_⟩
    cases p with
    | zero => trivial
    | succ q => exact Or.inl ⟨hA _ _ _ hAv, hAv⟩

/-- **Read through a view.** The location's contract implies the stated family,
which is all a read observes. -/
theorem read_view_rule {code : CallCode} {flds : List (String × Nat)} {f : String} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hf : flds.lookup f = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → A j U u) :
    Safe A n W h (.readAt f (.objAt flds code)) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.2 l c hl
    have hAv : A p (trunc p (Nat.le_succ p) W) v := hag p (by omega) _ v (hmem p (by omega))
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, v, WExt_refl _,
      WorldAdm_trunc _ hadm, .readField hf hv, HeapOk_trunc p W h hok, ?_⟩
    cases p with
    | zero => trivial
    | succ q => exact Or.inl ⟨hA _ _ _ hAv, hAv⟩

/-- A string dictionary covers every present field, while a missing name
reads `undefined`. A lookup cannot discard that alternative. -/
theorem read_dict_rule {flds : List (String × Nat)} {f : String} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hd : dictViewT A n W (.objAt flds .absent)) :
    Safe (unionT A undefT) n W h (.readAt f (.objAt flds .absent)) := by
  cases hlook : flds.lookup f with
  | some l =>
    obtain ⟨c, hc, hag⟩ := dictViewT_present hd hlook
    apply Safe_mono n (fun _ _ _ _ ha => Or.inl ha) W h _
      (read_view_rule hA n W h l hadm hok hlook hc hag)
  | none =>
    cases n with
    | zero => trivial
    | succ p =>
      refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, .undef, WExt_refl _,
        WorldAdm_trunc _ hadm, .readMissing hlook, HeapOk_trunc p W h hok, ?_⟩
      cases p with
      | zero => trivial
      | succ q => exact Or.inl ⟨rfl, Or.inr rfl⟩

/-- The same dictionary guarantee when the property name was evaluated at
runtime. The caller must separately prove that the key is a string. -/
theorem index_dict_rule {flds : List (String × Nat)} {f : String} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hd : dictViewT A n W (.objAt flds .absent)) :
    Safe (unionT A undefT) n W h (.indexAt (.objAt flds .absent) (.str f)) := by
  cases hlook : flds.lookup f with
  | some l =>
    obtain ⟨c, hc, hag⟩ := dictViewT_present hd hlook
    cases n with
    | zero => trivial
    | succ p =>
      obtain ⟨v, hv, hmem⟩ := hok.2 l c hc
      have hAv : A p (trunc p (Nat.le_succ p) W) v := hag p (by omega) _ v (hmem p (by omega))
      refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, v, WExt_refl _,
        WorldAdm_trunc _ hadm, .indexField hlook hv, HeapOk_trunc p W h hok, ?_⟩
      cases p with
      | zero => trivial
      | succ q => exact Or.inl ⟨hA _ _ _ hAv, Or.inl hAv⟩
  | none =>
    cases n with
    | zero => trivial
    | succ p =>
      refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, .undef, WExt_refl _,
        WorldAdm_trunc _ hadm, .indexMissing hlook, HeapOk_trunc p W h hok, ?_⟩
      cases p with
      | zero => trivial
      | succ q => exact Or.inl ⟨rfl, Or.inr rfl⟩

#print axioms index_dict_rule

/-- **Write.** -/
theorem write_rule {code : CallCode} {flds : List (String × Nat)} {f : String} {A : Fam}
    (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (v : Tm) (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hf : flds.lookup f = some l)
    {c : Ctr n} (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u)
    (hv : A n W v) :
    Safe nulT n W h (.writeAt f (.objAt flds code) v) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨w, hw, -⟩ := hok.2 l c hl
    have hlt : l < h.length := by
      have := (List.getElem?_eq_some_iff.mp hw).1; omega
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h.set l v, .nul, WExt_refl _,
      WorldAdm_trunc _ hadm, .writeField hval hf hlt, ?_, Safe_nul p _ _⟩
    refine write_sound p _ h l _ v (HeapOk_trunc p W h hok)
      (lookup_trunc (Nat.le_succ p) W l c hl) ?_
    intro i hi
    show c i _ _ v
    refine (hag i (by omega) _ v).mpr ?_
    have := hA.down_le (p + 1) i (by omega) W v hv
    rw [trunc_trunc]
    exact this

/-- **Object allocation.** Both descriptor shapes allocate through this rule.
The world grows by the stored contract; the result obligation supplies the
descriptor-specific view of the fresh object in that future world. -/
theorem make_rule {A Q : Fam} (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap) (code : CallCode) (v : Tm)
    (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h) (hv : A n W v)
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      refT A j U (.obj h.length .absent) → Q j U (.obj h.length code)) :
    Safe Q n W h (.make code v) := by
  cases n with
  | zero => trivial
  | succ p =>
    have hcadm : CtrAdm (res A : Ctr p) := fun i _ U U' hx w hw => hA.mono i U U' hx w hw
    have hlen : h.length = (toList (trunc p (Nat.le_succ p) W)).length := by
      have := hok.1; simp [trunc] at this ⊢; omega
    have hcont : ∀ (i : Nat) (hi : i < p),
        (res A : Ctr p) i hi
          (trunc i (Nat.le_of_lt hi) (appendW (trunc p (Nat.le_succ p) W) (res A))) v := by
      intro i hi
      show A i _ v
      rw [trunc_appendW, trunc_trunc]
      exact hA.mono i _ _ (WExt_appendW _ _) v (hA.down_le (p + 1) i (by omega) W v hv)
    refine Or.inr ⟨appendW (trunc p (Nat.le_succ p) W) (res A), h ++ [v], .obj h.length code,
      WExt_appendW _ _, WorldAdm_append (WorldAdm_trunc _ hadm) hcadm, .makeV hval,
      heap_alloc p _ h (res A) v (HeapOk_trunc p W h hok) (WorldAdm_trunc _ hadm) hcont,
      ?_⟩
    cases p with
    | zero => trivial
    | succ q =>
      refine Or.inl ⟨rfl, result (q + 1) (by omega) _ (WExt_appendW _ _) ?_⟩
      refine refT_cell (c := res A) ?_ (fun _ _ _ _ => Iff.rfl)
      simp only [lookup, appendW, toList_ofList]
      rw [List.getElem?_append_right (by omega)]
      simp [hlen]

/-- **Allocating an object with named fields.** One step takes one fresh
location per field, so the world grows by one contract per field and the result
sees the whole record. The single-cell rule above is the one-field case. -/
theorem make_fields_rule {Q : Fam} {As : List Fam} (hA : ∀ A ∈ As, Adm A)
    (n : Nat) (W : WorldT n) (h : Heap) (code : CallCode)
    (ns : List String) (vs : List Val)
    (hnd : ns.Nodup) (hns : ns.length = vs.length) (hAs : As.length = vs.length)
    (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ p ∈ As.zip vs, p.1 n W p.2)
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      recT (ns.zip As) j U (.objAt (slots h.length ns) .absent) →
      Q j U (.objAt (slots h.length ns) code)) :
    Safe Q n W h (.makeAt code ns vs) := by
  cases n with
  | zero => trivial
  | succ p =>
    have hcadm : ∀ c ∈ As.map (fun A => (res A : Ctr p)), CtrAdm c := by
      intro c hc
      obtain ⟨A, hA', rfl⟩ := List.mem_map.mp hc
      exact fun i _ U U' hx w hw => (hA A hA').mono i U U' hx w hw
    have hlen : h.length = (toList (trunc p (Nat.le_succ p) W)).length := by
      have := hok.1; simp [trunc] at this ⊢; omega
    have hcont : ∀ q ∈ (As.map (fun A => (res A : Ctr p))).zip vs, ∀ (j : Nat) (hj : j < p),
        q.1 j hj (trunc j (Nat.le_of_lt hj) (trunc p (Nat.le_succ p) W)) q.2 := by
      rw [List.zip_map_left]
      rintro q hq j hj
      obtain ⟨⟨A, v⟩, hm, rfl⟩ := List.mem_map.mp hq
      show A j _ v
      rw [trunc_trunc]
      exact (hA A (List.of_mem_zip hm).1).down_le (p + 1) j (by omega) W v (hv (A, v) hm)
    refine Or.inr ⟨appendWs (trunc p (Nat.le_succ p) W) (As.map (fun A => (res A : Ctr p))),
      h ++ vs, .objAt (slots h.length ns) code,
      WExt_appendWs _ _, WorldAdm_appendWs (WorldAdm_trunc _ hadm) hcadm,
      .makeFields hvals hns,
      heap_allocs p _ (trunc p (Nat.le_succ p) W) h vs (HeapOk_trunc p W h hok)
        (WorldAdm_trunc _ hadm) hcadm (by simp [hAs]) hcont, ?_⟩
    cases p with
    | zero => trivial
    | succ q =>
      refine Or.inl ⟨rfl, result (q + 1) (by omega) _ (WExt_appendWs _ _) ?_⟩
      refine recT_alloc hnd (by omega) ?_
      intro i hi
      have hib : i < (As.map (fun A => (res A : Ctr (q + 1)))).length := by
        simp; omega
      have := lookup_appendWs (trunc (q + 1) (Nat.le_succ (q + 1)) W)
        (As.map (fun A => (res A : Ctr (q + 1)))) hib
      rw [← hlen] at this
      rw [this]
      simp [List.getElem?_map, List.getElem?_eq_getElem (show i < As.length by omega)]

/-- Fresh dictionary construction chooses the index element contract for
every location it creates. The rule does not coerce an open record: its
premises type *all* initializers at the index contract. -/
theorem make_dict_rule {Q A : Fam} (hA : Adm A)
    (n : Nat) (W : WorldT n) (h : Heap) (ns : List String) (vs : List Val)
    (hnd : ns.Nodup) (hlen : ns.length = vs.length)
    (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ p ∈ (List.replicate vs.length A).zip vs, p.1 n W p.2)
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      dictViewT A j U (.objAt (slots h.length ns) .absent) →
      Q j U (.objAt (slots h.length ns) .absent)) :
    Safe Q n W h (.makeAt .absent ns vs) := by
  apply make_fields_rule (As := List.replicate vs.length A)
    (by intro B hB; simp at hB; simpa [hB] using hA)
    n W h .absent ns vs hnd hlen (by simp) hvals hadm hok
  · exact hv
  · intro j hj U he hrec
    apply result j hj U he
    have hrec' : recT (ns.zip (List.replicate ns.length A)) j U
        (.objAt (slots h.length ns) .absent) := by simpa [hlen] using hrec
    exact recT_fresh_dict hrec'

#print axioms make_dict_rule

/-- **A literal allocates a store.** One fresh location per element, each
under its family, and the store meets the claimed tuple contract by
`listT_alloc`; the continuation sees it at the extended world. -/
theorem arr_alloc_rule {Q : Fam} {As : List Fam} (hA : ∀ A ∈ As, Adm A)
    (n : Nat) (W : WorldT n) (h : Heap) (vs : List Val)
    (hAs : As.length = vs.length) (hvals : ∀ v ∈ vs, isVal v = true)
    (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hv : ∀ p ∈ As.zip vs, p.1 n W p.2)
    (result : ∀ j (hj : j < n) (U : WorldT j),
      WExt (trunc j (Nat.le_of_lt hj) W) U →
      (∀ (i : Nat) (hi : i < As.length), lookup U (h.length + i) = some (res (As[i]'hi))) →
      Q j U (.arr (elemSlots h.length vs.length))) :
    Safe Q n W h (.arrLit vs) := by
  cases n with
  | zero => trivial
  | succ p =>
    have hcadm : ∀ c ∈ As.map (fun A => (res A : Ctr p)), CtrAdm c := by
      intro c hc
      obtain ⟨A, hA', rfl⟩ := List.mem_map.mp hc
      exact fun i _ U U' hx w hw => (hA A hA').mono i U U' hx w hw
    have hlen : h.length = (toList (trunc p (Nat.le_succ p) W)).length := by
      have := hok.1; simp [trunc] at this ⊢; omega
    have hcont : ∀ q ∈ (As.map (fun A => (res A : Ctr p))).zip vs, ∀ (j : Nat) (hj : j < p),
        q.1 j hj (trunc j (Nat.le_of_lt hj) (trunc p (Nat.le_succ p) W)) q.2 := by
      rw [List.zip_map_left]
      rintro q hq j hj
      obtain ⟨⟨A, v⟩, hm, rfl⟩ := List.mem_map.mp hq
      show A j _ v
      rw [trunc_trunc]
      exact (hA A (List.of_mem_zip hm).1).down_le (p + 1) j (by omega) W v (hv (A, v) hm)
    refine Or.inr ⟨appendWs (trunc p (Nat.le_succ p) W) (As.map (fun A => (res A : Ctr p))),
      h ++ vs, .arr (elemSlots h.length vs.length),
      WExt_appendWs _ _, WorldAdm_appendWs (WorldAdm_trunc _ hadm) hcadm,
      .arrAlloc hvals,
      heap_allocs p _ (trunc p (Nat.le_succ p) W) h vs (HeapOk_trunc p W h hok)
        (WorldAdm_trunc _ hadm) hcadm (by simp [hAs]) hcont, ?_⟩
    cases p with
    | zero => trivial
    | succ q =>
      refine Or.inl ⟨rfl, result (q + 1) (by omega) _ (WExt_appendWs _ _) ?_⟩
      intro i hi
      have hib : i < (As.map (fun A => (res A : Ctr (q + 1)))).length := by
        simp; omega
      have := lookup_appendWs (trunc (q + 1) (Nat.le_succ (q + 1)) W)
        (As.map (fun A => (res A : Ctr (q + 1)))) hib
      rw [← hlen] at this
      rw [this]
      simp [List.getElem?_map, List.getElem?_eq_getElem hi]

/-- **An element read.** The index names a location; its contract implies
the family, which is all the read observes. -/
theorem elem_read_rule {ls : List (Option Nat)} {b : UInt64} {A : Fam}
    (hA : ValOnly A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (hadm : WorldAdm W) (hok : HeapOk n W h) (hl : elemLoc ls b = some l)
    {c : Ctr n} (hc : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → A j U u) :
    Safe A n W h (.elemAt (.arr ls) (.num b)) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨v, hv, hmem⟩ := hok.2 l c hc
    have hAv : A p (trunc p (Nat.le_succ p) W) v := hag p (by omega) _ v (hmem p (by omega))
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, v, WExt_refl _,
      WorldAdm_trunc _ hadm, .elemRead hl hv, HeapOk_trunc p W h hok, ?_⟩
    cases p with
    | zero => trivial
    | succ q => exact Or.inl ⟨hA _ _ _ hAv, hAv⟩

/-- **An absent element reads `undefined`.** -/
theorem elem_absent_rule {ls : List (Option Nat)} {b : UInt64} {Q : Fam}
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hn : elemLoc ls b = none) (hq : ∀ m (U : WorldT m), Q m U .undef) :
    Safe Q n W h (.elemAt (.arr ls) (.num b)) := by
  cases n with
  | zero => trivial
  | succ p =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, .undef, WExt_refl _, WorldAdm_trunc _ hadm,
      .elemAbsent hn, HeapOk_trunc p W h hok, ?_⟩
    exact value_safe _ _ _ _ _ rfl (hq _ _)

/-- **A write to a present element.** As a field write: the location's contract
admits the value, and the store, unchanged, is what the write yields. -/
theorem set_present_rule {ls : List (Option Nat)} {b : UInt64} {A Q : Fam}
    (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap) (l : Nat)
    (v : Tm) (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hl : elemLoc ls b = some l) {c : Ctr n} (hc : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u ↔ A j U u)
    (hv : A n W v) (hq : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U → Q j U (.arr ls)) :
    Safe Q n W h (.setElem (.arr ls) (.num b) v) := by
  cases n with
  | zero => trivial
  | succ p =>
    obtain ⟨w, hw, -⟩ := hok.2 l c hc
    have hlt : l < h.length := by
      have := (List.getElem?_eq_some_iff.mp hw).1; omega
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h.set l v, .arr ls, WExt_refl _,
      WorldAdm_trunc _ hadm, .setPresent hval hl hlt, ?_, ?_⟩
    · refine write_sound p _ h l _ v (HeapOk_trunc p W h hok)
        (lookup_trunc (Nat.le_succ p) W l c hc) ?_
      intro i hi
      show c i _ _ v
      refine (hag i (by omega) _ v).mpr ?_
      have := hA.down_le (p + 1) i (by omega) W v hv
      rw [trunc_trunc]
      exact this
    · exact value_safe _ _ _ _ _ rfl (hq p (by omega) _ (WExt_refl _))

/-- **A write that grows the store.** A fresh location under the position's
family takes the value; the store the write yields records it. -/
theorem set_grow_rule {ls : List (Option Nat)} {b : UInt64} {k : Nat} {A Q : Fam}
    (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap)
    (v : Tm) (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hk : indexOfBits b = some k) (hn : elemLoc ls b = none) (hv : A n W v)
    (hq : ∀ j (hj : j < n) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      lookup U h.length = some (res A) → Q j U (.arr (placeAt ls k h.length))) :
    Safe Q n W h (.setElem (.arr ls) (.num b) v) := by
  cases n with
  | zero => trivial
  | succ p =>
    have hcadm : ∀ c ∈ [(res A : Ctr p)], CtrAdm c := by
      intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      exact fun i _ U U' hx w hw => hA.mono i U U' hx w hw
    have hlen : h.length = (toList (trunc p (Nat.le_succ p) W)).length := by
      have := hok.1; simp [trunc] at this ⊢; omega
    have hcont : ∀ q ∈ [(res A : Ctr p)].zip [v], ∀ (j : Nat) (hj : j < p),
        q.1 j hj (trunc j (Nat.le_of_lt hj) (trunc p (Nat.le_succ p) W)) q.2 := by
      intro q hq j hj
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq
      subst hq
      show A j _ v
      rw [trunc_trunc]
      exact hA.down_le (p + 1) j (by omega) W v hv
    refine Or.inr ⟨appendWs (trunc p (Nat.le_succ p) W) [res A], h ++ [v], .arr (placeAt ls k h.length),
      WExt_appendWs _ _, WorldAdm_appendWs (WorldAdm_trunc _ hadm) hcadm,
      .setGrow hval hk hn,
      heap_allocs p _ (trunc p (Nat.le_succ p) W) h [v] (HeapOk_trunc p W h hok)
        (WorldAdm_trunc _ hadm) hcadm rfl hcont, ?_⟩
    cases p with
    | zero => trivial
    | succ q =>
      refine Or.inl ⟨rfl, hq (q + 1) (by omega) _ (WExt_appendWs _ _) ?_⟩
      rw [hlen]
      have := lookup_appendWs (trunc (q + 1) (Nat.le_succ (q + 1)) W) [(res A : Ctr (q + 1))]
        (i := 0) (by simp)
      simpa using this

/-- **A length read** is a number. -/
theorem len_rule {ls : List (Option Nat)} {Q : Fam}
    (n : Nat) (W : WorldT n) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hq : ∀ m (U : WorldT m), Q m U (.num (bitsOfNat ls.length))) :
    Safe Q n W h (.lenOf (.arr ls)) := by
  cases n with
  | zero => trivial
  | succ p =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, _, WExt_refl _, WorldAdm_trunc _ hadm,
      .lenV, HeapOk_trunc p W h hok, ?_⟩
    exact value_safe _ _ _ _ _ rfl (hq _ _)

/-- Plain references specialize the common allocation rule to an absent descriptor. -/
theorem alloc_rule {A : Fam} (hA : Adm A) (n : Nat) (W : WorldT n) (h : Heap) (v : Tm)
    (hval : isVal v = true) (hadm : WorldAdm W) (hok : HeapOk n W h) (hv : A n W v) :
    Safe (refT A) n W h (.alloc v) :=
  make_rule hA n W h .absent v hval hadm hok hv (fun _ _ _ _ hr => hr)

#print axioms make_rule
#print axioms alloc_rule

theorem refT_transfer {A : Fam} {k : Nat} {W : WorldT k} {flds : List (String × Nat)}
    (hr : refT A k W (.objAt flds .absent)) (j : Nat) (hj : j ≤ k) (W' : WorldT j)
    (hW : WExt (trunc j hj W) W') : refT A j W' (.objAt flds .absent) :=
  (refT_adm A).mono j _ _ hW _ ((refT_adm A).down_le k j hj W _ hr)

/-- A function that ignores its argument and diverges inhabits *every* arrow
type: applied to anything, it never returns, and that is safe at any result. -/
theorem ignore_safe (B : Fam) (n : Nat) (W : WorldT n) (h : Heap)
    (ha : WorldAdm W) (hh : HeapOk n W h) (v : Val) (hv : isVal v = true) :
    Safe B n W h (.app (.fn 0 omegaTm) v) := by
  cases n with
  | zero => trivial
  | succ n =>
    apply beta_rule _ _ hv n W h ha hh
    simpa [omegaTm, delta, subst] using
      omega_safe B n _ h (WorldAdm_trunc _ ha) (HeapOk_trunc n W h hh)

theorem diverging_arrow {A B : Fam} (n : Nat) (W : WorldT n) :
    arrowT A B n W (.fn 0 omegaTm) := by
  apply fn_intro _ _ _ (by simp [omegaTm, delta, Scoped])
  intro p hp U hx hu h hh a hA
  simpa [omegaTm, delta, subst] using
    omega_safe B p U h hu hh

/-- Being stuck is exactly what `Safe` forbids. -/
theorem stuck_not_safe (B : Fam) (k : Nat) (W : WorldT (k + 1)) (h : Heap) :
    ¬ Safe B (k + 1) W h (.app .nul .nul) := by
  rintro (⟨hv, -⟩ | ⟨_, _, _, _, _, hs, _, _⟩)
  · simp [isVal] at hv
  · exact stuck_no_step hs

/-- An arrow with an uninhabited domain constrains nothing: every function has
that type, including one that would get stuck if it were ever applied. -/
theorem vacuous_arrow {l : Nat} {A B : Fam} (hA : ∀ (j : Nat) (W : WorldT j) (v : Val), ¬ A j W v)
    (b : Tm) (k : Nat) (W : WorldT k) (hc : Scoped 2 b) : arrowT A B k W (.fn l b) :=
  ⟨⟨1, b, _, rfl, hc⟩, fun _ _ _ _ _ _ _ a ha => absurd ha (hA _ _ a)⟩

/-! ## Testing a value's shape, and branching on the answer

The two constructs a narrowing source language needs. A test of a value answers
in one step; a branch on that answer takes one more. Both are ordinary reduction
steps, so each spends a budget, which is why the rule below starts two above the
budget its branches are checked at. -/

/-- **A shape test answers.** -/
theorem test_value_safe (k : Tag) (v : Val) (hv : isVal v = true) (p : Nat)
    (W : WorldT (p + 1)) (h : Heap) (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h) :
    Safe boolT (p + 1) W h (.test k v) := by
  refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, _, WExt_refl _, WorldAdm_trunc _ hadm,
    .testV hv, HeapOk_trunc p W h hok, ?_⟩
  cases p with
  | zero => trivial
  | succ q =>
    refine Or.inl ⟨?_, ?_⟩ <;> cases tagHolds k v <;> simp [boolT, isVal]

/-- **Arithmetic on two numbers answers.** The result is a number of the
family `S` names, whatever its bits. -/
theorem arith_value_safe {S : Fam} (op : Arith) (x y : UInt64) (n : Nat) (W : WorldT n)
    (h : Heap) (hadm : WorldAdm W) (hok : HeapOk n W h)
    (hr : ∀ m (U : WorldT m), S m U (.num (arithBits op x y))) :
    Safe S n W h (.arith op (.num x) (.num y)) := by
  cases n with
  | zero => trivial
  | succ p =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) W, h, _, WExt_refl _, WorldAdm_trunc _ hadm,
      .arithV, HeapOk_trunc p W h hok, ?_⟩
    exact value_safe _ _ _ _ _ rfl (hr _ _)

/-- **Branching on a shape test.** The two branches are checked under the answer
they run in, which is what makes this narrowing rather than a plain conditional:
the `then` branch may assume the test succeeded. -/
theorem ite_test_rule {B : Fam} (k : Tag) (a : Val) (hv : isVal a = true) (u e : Tm)
    (p : Nat) (W : WorldT (p + 2)) (h : Heap) (hadm : WorldAdm W)
    (hok : HeapOk (p + 2) W h)
    (hthen : tagHolds k a = true → Safe B p (trunc p (by omega) W) h u)
    (helse : tagHolds k a = false → Safe B p (trunc p (by omega) W) h e) :
    Safe B (p + 2) W h (.ite (.test k a) u e) := by
  refine Or.inr ⟨trunc (p + 1) (Nat.le_succ _) W, h, _, WExt_refl _,
    WorldAdm_trunc _ hadm, .iteC (.testV hv), HeapOk_trunc (p + 1) W h hok, ?_⟩
  have hadm' : WorldAdm (trunc (p + 1) (Nat.le_succ _) W) := WorldAdm_trunc _ hadm
  have hok' : HeapOk (p + 1) (trunc (p + 1) (Nat.le_succ _) W) h := HeapOk_trunc (p + 1) W h hok
  cases hb : tagHolds k a with
  | true =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) _, h, u, WExt_refl _, WorldAdm_trunc _ hadm',
      by simp; exact Step.iteT, HeapOk_trunc p _ h hok', ?_⟩
    rw [trunc_trunc]
    exact hthen hb
  | false =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) _, h, e, WExt_refl _, WorldAdm_trunc _ hadm',
      by simp; exact Step.iteF, HeapOk_trunc p _ h hok', ?_⟩
    rw [trunc_trunc]
    exact helse hb


/-- An arrow below every conjunct is below the intersection: one function serves
a whole overloaded type when its domain covers every domain and its codomain
sits inside every codomain. -/
theorem arrowsT_of_arrow {L : List (Fam × Fam)} {A B : Fam}
    (hdom : ∀ p ∈ L, FamLe p.1 A) (hcod : ∀ p ∈ L, FamLe B p.2) :
    FamLe (arrowT A B) (arrowsT L) := by
  rintro n W v ⟨hl, h⟩
  refine ⟨hl, ?_⟩
  intro p hp j hj W' hx hu hh hok a ha
  exact Safe_mono j (fun m _ U u hb => hcod p hp m U u hb) W' hh _
    (h j hj W' hx hu hh hok a (hdom p hp j W' a ha))

/-- The diverging function inhabits every intersection of arrows, as a direct check that these types admit safe nontermination. -/
theorem diverging_in_arrowsT (L : List (Fam × Fam))
    (k : Nat) (W : WorldT k) : arrowsT L k W (.fn 0 omegaTm) := by
  refine ⟨⟨1, omegaTm, _, rfl, by simp [omegaTm, delta, Scoped]⟩, ?_⟩
  intro p hp j hj W' hx hu hh hok a ha
  exact (diverging_arrow (A := p.1) (B := p.2) k W).2 j hj W' hx hu hh hok a ha


#print axioms call_elim
#print axioms app_elim
#print axioms let_rule

end Model
end Verification
