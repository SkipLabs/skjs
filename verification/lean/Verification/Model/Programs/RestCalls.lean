import Verification.Model.Semantics.Rules

/-!
# Variadic calls

Variadic code takes a fixed number of parameters and collects every further
actual into one fresh array. What it promises is `RestSpec`, a code contract;
its signatures are `restsT`, which says only which actual lists a caller may
write, so the same value may also meet fixed signatures (`Safety`, call
contracts).

The array is not built by invocation. `CallArguments.bindRest` yields a term
that allocates it with the ordinary store and allocation steps, so the heap
changes only as those steps run.
-/
namespace Verification.Model.RestCalls

/-- What variadic code promises: for a receiver in `Rc` and fixed actuals in
`Ps`, followed by further actuals that as one pack are in `E`, the term
invocation yields is safe at `R`. -/
def RestSpec (n : Nat) (Rc : Fam) (Ps : List Fam) (E R : Fam) (k : Nat) (W : WorldT k)
    (b : Tm) : Prop :=
  Scoped (n + 2) b ∧ Ps.length = n ∧
  ∀ (j : Nat) (hj : j < k) (W' : WorldT j),
    WExt (trunc j (Nat.le_of_lt hj) W) W' → WorldAdm W' → ∀ (h : Heap), HeapOk j W' h →
      ∀ r, Rc j W' r → ∀ args extra, ArgsT Ps j W' args → E j W' (.args extra) →
        CallArguments.Values extra →
        Safe R j W' h (CallArguments.bindRest n (args ++ extra) r b)

/-- Fixed actuals exactly as many as the parameters bind as themselves; the
rest are left to the array. -/
theorem parameters_prefix (args extra : List Tm) :
    CallArguments.parameters args.length (args ++ extra) = args := by
  induction args with
  | nil => rfl
  | cons a args ih => simp [CallArguments.parameters, ih]

theorem RestSpec.down {n Rc Ps E R k W b} (h : RestSpec n Rc Ps E R (k + 1) W b) :
    RestSpec n Rc Ps E R k (trunc k (Nat.le_succ k) W) b := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro j hj U hx hu heap hh r hr args extra ha he hv
  exact h.2.2 j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh r hr args extra ha he hv

theorem RestSpec.mono {n Rc Ps E R k W W' b} (hx : WExt W W')
    (h : RestSpec n Rc Ps E R k W b) : RestSpec n Rc Ps E R k W' b := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro j hj U hy hu heap hh r hr args extra ha he hv
  exact h.2.2 j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh r hr args
    extra ha he hv

/-- Binding fewer actuals than parameters pads the rest with `undefined`. -/
theorem parameters_short : ∀ (n : Nat) (args : List Tm), args.length ≤ n →
    CallArguments.parameters n args = args ++ List.replicate (n - args.length) .undef
  | 0, [], _ => rfl
  | n + 1, [], _ => by
    simp [CallArguments.parameters, parameters_short n [] (by simp), List.replicate_succ]
  | n + 1, a :: args, h => by
    simp [CallArguments.parameters, parameters_short n args (by simp at h; omega)]
  | 0, _ :: _, h => by simp at h

/-- Variadic code meeting its code contract meets the signature: a list its
fixed parameters admit binds as the padded one, collecting nothing, and a
longer one binds its fixed prefix and collects the rest. -/
theorem restsT_of_restSpec {n : Nat} {Rc : Fam} {Ps : List Fam} {E R : Fam} {k : Nat}
    {W : WorldT k} {b : Tm} (fs : List (PropKey × Nat)) (hs : RestSpec n Rc Ps E R k W b) :
    restsT [(Rc, Ps, E, R)] k W (.objAt fs (.variadic n b)) := by
  refine ⟨⟨fs, _, rfl, rfl, by simpa [Scoped, Nat.add_comm, Nat.add_left_comm] using hs.1⟩, ?_⟩
  intro s hsm j hj U hx hu heap hh r hrv hr args hvals ha
  cases List.mem_singleton.mp hsm
  refine ⟨_, .variadic hrv hvals, ?_⟩
  obtain ⟨hshort, hpack⟩ := ha
  have hn : Ps.length = n := hs.2.1
  by_cases hl : args.length ≤ Ps.length
  · rw [List.take_of_length_le hl] at hshort
    rw [List.drop_eq_nil_of_le hl] at hpack
    have hsafe := hs.2.2 j hj U hx hu heap hh r hr _ [] (ArgsShort_pad hshort) hpack (fun a ha => by cases ha)
    simp only [List.append_nil] at hsafe
    unfold CallArguments.bindRest at hsafe ⊢
    have hlen : (args ++ List.replicate (Ps.length - args.length) Tm.undef).length = n := by
      simp; omega
    rw [List.drop_eq_nil_of_le (by omega), ← hlen, CallArguments.parameters_exact] at hsafe
    rw [List.drop_eq_nil_of_le (by omega), parameters_short n args (by omega), ← hn]
    exact hsafe
  · have htl : (args.take Ps.length).length = Ps.length := by simp; omega
    have ht : ArgsT Ps j U (args.take Ps.length) := by
      have := hshort.2.1
      rwa [htl, List.take_length] at this
    have hsafe := hs.2.2 j hj U hx hu heap hh r hr _ _ ht hpack
      (fun a ha => hvals a (List.mem_of_mem_drop ha))
    rwa [List.take_append_drop] at hsafe

/-- A ready variadic call consumes one step, then meets the result contract. -/
theorem call_elim_rest {S : List (Fam × List Fam × Fam × Fam)} {s : Fam × List Fam × Fam × Fam}
    (hs : s ∈ S) (hR : Adm s.1) (hA : ∀ A ∈ s.2.1, Adm A) (hAv : ∀ A ∈ s.2.1, ValOnly A)
    (hE : Adm s.2.2.1)
    {n : Nat} {W : WorldT n} {f r : Tm} {args extra : List Tm} {heap : Heap}
    (hrv : isVal r = true) (hr : s.1 n W r)
    (hf : restsT S n W f) (ha : ArgsT s.2.1 n W args) (he : s.2.2.1 n W (.args extra))
    (hev : CallArguments.Values extra)
    (hw : WorldAdm W) (hh : HeapOk n W heap) :
    Safe s.2.2.2 n W heap (.invoke f r (args ++ extra)) := by
  cases n with
  | zero => trivial
  | succ n =>
    let U := trunc n (Nat.le_succ n) W
    have hu : WorldAdm U := WorldAdm_trunc _ hw
    have hh' : HeapOk n U heap := HeapOk_trunc n W heap hh
    have ha' := ArgsT_transfer hA ha n (Nat.le_succ n) U (WExt_refl _)
    have he' : s.2.2.1 n U (.args extra) := hE.down n W _ he
    have hr' : s.1 n U r := hR.down n W r hr
    have hvals : CallArguments.Values (args ++ extra) := by
      intro a hm
      rcases List.mem_append.mp hm with hm | hm
      · exact ArgsT_values hAv ha' a hm
      · exact hev a hm
    obtain ⟨body, hi, hsafe⟩ := hf.2 s hs n (Nat.lt_succ_self n) U (WExt_refl _) hu heap hh'
      r hrv hr' _ hvals (ArgsRest_of_exact_extra ha' he')
    exact Or.inr ⟨U, heap, body, WExt_refl _, hu, hi.step heap, hh', hsafe⟩

/-- Run a subterm in an evaluation context, then continue with its value. -/
theorem ctx_bind {A B : Fam} (C : Tm → Tm)
    (lift : ∀ {h t h' t'}, Step h t h' t' → Step h (C t) h' (C t')) :
    ∀ n W h t, WorldAdm W → HeapOk n W h → Safe A n W h t →
    (∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
      ∀ h' v, HeapOk j U h' → isVal v = true → A j U v → Safe B j U h' (C v)) →
    Safe B n W h (C t) := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hw hh hs hk
    rcases hs with ⟨hv, ht⟩ | ⟨U, h', t', hx, hu, step, hh', ht'⟩
    · exact hk (n+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw h t hh hv ht
    · refine Or.inr ⟨U, h', C t', hx, hu, lift step, hh', ih U h' t' hu hh' ht' ?_⟩
      intro j hj V hx' hv h'' v hh'' hval ha
      apply hk j (by omega) V _ hv h'' v hh'' hval ha
      apply WExt_trans _ hx'
      simpa only [trunc_trunc] using WExt_trunc hj hx

/-- **Creating a variadic value.** Code whose body is safe with any receiver
in `Rc` (slot 1), any fixed actuals in `Ps` (from slot 2) and any array in `Arr` in slot 0 meets the
variadic signature, provided collecting further actuals whose pack is in `E`
allocates such an array. -/
theorem restSpec_of_body {n : Nat} {Rc : Fam} {Ps : List Fam} {E Arr R : Fam} {k : Nat}
    {W : WorldT k} {b : Tm}
    (hscope : Scoped (n + 2) b) (hlen : Ps.length = n) (hRc : Adm Rc)
    (hP : ∀ A ∈ Ps, Adm A) (hArr : Adm Arr)
    (halloc : ∀ j (U : WorldT j) h extra, WorldAdm U → HeapOk j U h →
      E j U (.args extra) → CallArguments.Values extra →
      Safe Arr j U h (CallArguments.restArray extra))
    (hbody : ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      WorldAdm U → ∀ h, HeapOk j U h → ∀ r, Rc j U r → ∀ args a, ArgsT Ps j U args →
        Arr j U a → isVal a = true → Safe R j U h (subst 0 a (bindArgs 1 (r :: args) b))) :
    RestSpec n Rc Ps E R k W b := by
  refine ⟨hscope, hlen, ?_⟩
  intro j hj U hx hu h hh r hr args extra ha he hev
  have hl : args.length = n := (ArgsT_length ha).trans hlen
  unfold CallArguments.bindRest
  rw [List.drop_left' hl, ← hl, parameters_prefix]
  apply ctx_bind (.letE · _) .letC j U h _ hu hh (halloc j U h extra hu hh he hev)
  intro i hi V hy hv h' a hh' hval harr
  cases i with
  | zero => trivial
  | succ p =>
    apply let_rule _ a hval p V h' hv hh'
    have hUV : WExt (trunc p (by omega) U) (trunc p (Nat.le_succ p) V) := by
      simpa only [trunc_trunc] using WExt_trunc (Nat.le_succ p) hy
    have hWV : WExt (trunc p (by omega) W) (trunc p (Nat.le_succ p) V) := by
      apply WExt_trans _ hUV
      simpa only [trunc_trunc] using WExt_trunc (show p ≤ j by omega) hx
    exact hbody p (by omega) _ hWV (WorldAdm_trunc _ hv) h' (HeapOk_trunc p V h' hh') r
      (hRc.mono p _ _ hUV r (hRc.down_le j p (by omega) U r hr)) args a
      (ArgsT_transfer hP ha p (by omega) _ hUV) (hArr.down p V a harr) hval

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

/-- **Allocating a pack.** Its values, as a fresh store, meet its tuple
contract as a writable store. Each value is at its position's family below the
budget, which is all the allocation step needs. -/
theorem pack_alloc_safe {T : TupleF} (hT : ∀ i A, positionFam T i = some A → Adm A)
    {n : Nat} {W : WorldT n} {h : Heap} {vs : List Tm}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hp : PackFits T n W vs)
    (hvals : ∀ v ∈ vs, isVal v = true) :
    Safe (listT { T with readonly := false }) n W h (.arrLit vs) := by
  obtain ⟨hreq, hbound, hel⟩ := hp
  have hsome : ∀ i, i < vs.length → ∃ A, positionFam T i = some A := by
    intro i hi
    apply Option.isSome_iff_exists.mp
    apply positionFam_isSome
    cases hr : T.rest with
    | none => have := hbound hr; left; omega
    | some _ => right; rfl
  let As := (List.range vs.length).map fun i => (positionFam T i).getD (fun _ _ _ => False)
  have hlen : As.length = vs.length := by simp [As]
  have hAi : ∀ i (hi : i < As.length), positionFam T i = some (As[i]'hi) := by
    intro i hi
    obtain ⟨A, hA⟩ := hsome i (by simpa [hlen] using hi)
    simp [As, hA]
  have hres := arr_alloc_rule_below (Q := listT { T with readonly := false }) (As := As)
    (by
      intro A hA
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hA
      exact hT i _ (hAi i hi))
    n W h vs hlen hvals hw hh
    (by
      intro p hp j hj
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
      rw [List.getElem_zip] at hpi
      subst hpi
      have hiv : i < vs.length := by simp at hi; omega
      exact hel i _ _ (List.getElem?_eq_getElem hiv) (hAi i _) j hj _ (WExt_refl _))
    (by
      intro j hj U hx hl
      have := listT_alloc (T := { T with readonly := false }) (As := As) (base := h.length)
        (by simp only [hlen]; exact hreq) (by simp only [hlen]; exact hbound)
        (fun i A hA => by
          obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hA
          exact hAi i hi)
        hl
      rwa [hlen] at this)
  exact hres

/-! ## Spread actuals

A spread actual evaluates to a store, and the call then reads the store's
elements in its place, before any later actual runs. A store family spreads
into `E` when every element it may hold reads at `E`: through its location's
contract one budget down, or as `undefined` at a hole. -/

/-- Reading the elements of a store the heap satisfies yields members of `E`. -/
def Spreads (S E : Fam) : Prop :=
  ∀ n W (h : Heap) v, HeapOk n W h → S n W v →
    ∃ ls vs, v = .arr ls ∧ readElems h ls = some vs ∧
      ∀ e ∈ vs, ∀ (j : Nat) (hj : j < n), E j (trunc j (Nat.le_of_lt hj) W) e

/-- Every location a store names has a contract implying `E`, and a hole is
allowed only where `E` admits `undefined`: then the elements read at `E`. -/
theorem readElems_ok {E : Fam} {n : Nat} {W : WorldT n} {h : Heap} (hh : HeapOk n W h) :
    ∀ ls : List (Option Nat),
      (∀ l, some l ∈ ls → ∃ c : Ctr n, lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → E j U u) →
      (none ∈ ls → ∀ j (U : WorldT j), E j U .undef) →
      ∃ vs, readElems h ls = some vs ∧
        ∀ e ∈ vs, ∀ (j : Nat) (hj : j < n), E j (trunc j (Nat.le_of_lt hj) W) e
  | [], _, _ => ⟨[], rfl, by simp⟩
  | none :: ls, hl, hn => by
    obtain ⟨vs, hr, he⟩ := readElems_ok hh ls (fun l hm => hl l (by simp [hm]))
      (fun hm => hn (by simp [hm]))
    refine ⟨.undef :: vs, by simp [readElems, hr], ?_⟩
    intro e hm j hj
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hn (by simp) j _
    · exact he e hm j hj
  | some l :: ls, hl, hn => by
    obtain ⟨vs, hr, he⟩ := readElems_ok hh ls (fun l hm => hl l (by simp [hm]))
      (fun hm => hn (by simp [hm]))
    obtain ⟨c, hc, hag⟩ := hl l (by simp)
    obtain ⟨v, hv, hmem⟩ := hh.2 l c hc
    refine ⟨v :: vs, by simp [readElems, hv, hr], ?_⟩
    intro e hm j hj
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hag j hj _ e (hmem j hj)
    · exact he e hm j hj

/-- A tuple contract spreads into `E` when every position's family implies
`E`, and `E` admits `undefined` if the store may have a hole: at an optional
position or among the rest. -/
theorem listT_spreads {T : TupleF} {E : Fam}
    (hpos : ∀ i A, positionFam T i = some A → FamLe A E)
    (hhole : (T.optional ≠ [] ∨ T.rest.isSome) → ∀ j (U : WorldT j), E j U .undef) :
    Spreads (listT T) E := by
  rintro n W h v hh ⟨ls, rfl, hlen, hbound, hreq, hopt, hrest⟩
  have hsome : ∀ l, some l ∈ ls → ∃ c : Ctr n, lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → E j U u := by
    intro l hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    by_cases h1 : i < T.required.length
    · obtain ⟨A, hA⟩ : ∃ A, T.required[i]? = some A := ⟨_, List.getElem?_eq_getElem h1⟩
      obtain ⟨l', c, hl', hc, hag⟩ := hreq i A hA
      rw [hi] at hl'; cases hl'
      refine ⟨c, hc, fun j hj U u hu => hpos i A (by simp [positionFam, hA]) j U u ((hag j hj U u).1 hu)⟩
    · by_cases h2 : i < T.required.length + T.optional.length
      · obtain ⟨A, hA⟩ : ∃ A, T.optional[i - T.required.length]? = some A :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨c, hc, hag⟩ := hopt (i - T.required.length) A l hA
          (by rw [show T.required.length + (i - T.required.length) = i by omega]; exact hi)
        refine ⟨c, hc, fun j hj U u hu => hpos i A ?_ j U u ((hag j hj U u).1 hu)⟩
        simp [positionFam, List.getElem?_eq_none (show T.required.length ≤ i by omega), hA]
      · obtain ⟨A, c, hA, hc, hag⟩ := hrest i l (by omega) hi
        refine ⟨c, hc, fun j hj U u hu => hpos i A ?_ j U u ((hag j hj U u).1 hu)⟩
        simp [positionFam, List.getElem?_eq_none (show T.required.length ≤ i by omega),
          List.getElem?_eq_none (show T.optional.length ≤ i - T.required.length by omega),
          show T.required.length + T.optional.length ≤ i by omega, hA]
  have hnone : none ∈ ls → ∀ j (U : WorldT j), E j U .undef := by
    intro hm
    apply hhole
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    by_cases h1 : i < T.required.length
    · obtain ⟨A, hA⟩ : ∃ A, T.required[i]? = some A := ⟨_, List.getElem?_eq_getElem h1⟩
      obtain ⟨l', c, hl', -⟩ := hreq i A hA
      rw [hi] at hl'; cases hl'
    · have hlt := (List.getElem?_eq_some_iff.mp hi).1
      by_cases ho : T.optional = []
      · cases hrs : T.rest with
        | none => have := hbound hrs; simp [ho] at this; omega
        | some _ => exact Or.inr rfl
      · exact Or.inl ho
  obtain ⟨vs, hr, he⟩ := readElems_ok hh ls hsome hnone
  exact ⟨ls, vs, rfl, hr, he⟩

/-- A step of the actual after a completed prefix is a step of the call. -/
theorem call_lift {h h' : Heap} {f r t t' : Tm} {pre rest : List Tm}
    (hf : isVal f = true) (hr : isVal r = true) (hp : CallArguments.Values pre)
    (s : Step h t h' t') :
    Step h (.invoke f r (pre ++ t :: rest)) h' (.invoke f r (pre ++ t' :: rest)) :=
  (CallArguments.Prepare.args (r := r) (args := pre ++ t :: rest) hf hr
    (CallArguments.keep_prefix hp (.head s))).step

/-- The term a part is written as: itself, or a spread of it. -/
def partTerm (p : Option Fam × Tm) : Tm :=
  match p.1 with
  | none => p.2
  | some _ => .spread p.2

/-- **Actuals after the fixed ones.** Each part is a plain actual at `E` or a
spread of a store in a family that spreads into `E`; they run left to right,
each spread read as soon as its store is ready, and the continuation receives
every element and actual at `E`. -/
theorem spread_parts_safe {E R : Fam} (hE : Adm E) (hEv : ValOnly E) {f r : Tm}
    (hf : isVal f = true) (hrv : isVal r = true) :
    ∀ (parts : List (Option Fam × Tm)) (n : Nat) (W : WorldT n) (heap : Heap) (pre : List Tm),
      (∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ Spreads S E) →
      WorldAdm W → HeapOk n W heap → CallArguments.Values pre →
      (∀ p ∈ parts, ∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
        ∀ heap, HeapOk j U heap → Safe (p.1.getD E) j U heap p.2) →
      (∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
        ∀ heap extra, HeapOk j U heap → (∀ e ∈ extra, E j U e) →
          Safe R j U heap (.invoke f r (pre ++ extra))) →
      Safe R n W heap (.invoke f r (pre ++ parts.map partTerm))
  | [], n, W, heap, pre, _, hw, hh, _, _, hk => by
    simpa using hk n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap [] hh (by simp)
  | (none, a) :: parts, n, W, heap, pre, hS, hw, hh, hp, ht, hk => by
    have ha := ht (none, a) (by simp) n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap hh
    apply ctx_bind (A := E) (fun t => .invoke f r (pre ++ t :: parts.map partTerm))
      (fun s => call_lift hf hrv hp s) n W heap a hw hh ha
    intro j hj U hx hu heap' v hh' hv hEv'
    have hrest := spread_parts_safe hE hEv hf hrv parts j U heap' (pre ++ [v])
      (fun p hm => hS p (by simp [hm])) hu hh'
      (by intro x hx'; rcases List.mem_append.mp hx' with hx' | hx'
          · exact hp x hx'
          · simp at hx'; subst hx'; exact hv)
      (by
        intro p hm i hi V hy hV heap'' hh''
        apply ht p (by simp [hm]) i (by omega) V _ hV heap'' hh''
        apply WExt_trans _ hy
        simpa only [trunc_trunc] using WExt_trunc hi hx)
      (by
        intro i hi V hy hV heap'' extra hh'' he
        have hw' : WExt (trunc i (by omega) W) V := by
          apply WExt_trans _ hy
          simpa only [trunc_trunc] using WExt_trunc hi hx
        have := hk i (by omega) V hw' hV heap'' (v :: extra) hh'' (by
          intro e hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact hE.mono i _ V hy e (hE.down_le j i hi U e hEv')
          · exact he e hm)
        simpa using this)
    simpa [partTerm] using hrest
  | (some S, s) :: parts, n, W, heap, pre, hS, hw, hh, hp, ht, hk => by
    obtain ⟨hSa, hSs⟩ := hS (some S, s) (by simp) S rfl
    have hs := ht (some S, s) (by simp) n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap hh
    show Safe R n W heap (.invoke f r (pre ++ .spread s :: parts.map partTerm))
    apply ctx_bind (A := S) (fun t => .invoke f r (pre ++ .spread t :: parts.map partTerm))
      (fun s => call_lift hf hrv hp (.spreadC s)) n W heap s hw hh hs
    intro j hj U hx hu heap' v hh' _ hv
    obtain ⟨ls, vs, rfl, hr, he⟩ := hSs j U heap' _ hh' hv
    cases j with
    | zero => trivial
    | succ p =>
      have hvs : CallArguments.Values vs := fun e hm => hEv p _ e (he e hm p (by omega))
      refine Or.inr ⟨trunc p (Nat.le_succ p) U, heap', .invoke f r (pre ++ vs ++ parts.map partTerm), WExt_refl _,
        WorldAdm_trunc _ hu, .callSpread hf hrv rfl hp hr, HeapOk_trunc p U heap' hh', ?_⟩
      have hUV : ∀ i (hi : i ≤ p) (X : WorldT i),
          WExt (trunc i hi (trunc p (Nat.le_succ p) U)) X → WExt (trunc i (by omega) W) X := by
        intro i hi X hy
        apply WExt_trans _ hy
        have := WExt_trunc (show i ≤ p + 1 by omega) hx
        simpa only [trunc_trunc] using this
      have hrest := spread_parts_safe hE hEv hf hrv parts p _ heap' (pre ++ vs)
        (fun q hm => hS q (by simp [hm])) (WorldAdm_trunc _ hu) (HeapOk_trunc p U heap' hh')
        (by intro x hx'; rcases List.mem_append.mp hx' with hx' | hx'
            · exact hp x hx'
            · exact hvs x hx')
        (by
          intro q hm i hi X hy hX heap'' hh''
          exact ht q (by simp [hm]) i (by omega) X (hUV i hi X hy) hX heap'' hh'')
        (by
          intro i hi X hy hX heap'' extra hh'' hex
          have := hk i (by omega) X (hUV i hi X hy) hX heap'' (vs ++ extra) hh'' (by
            intro e hm
            rcases List.mem_append.mp hm with hm | hm
            · have h0 := he e hm p (by omega)
              exact hE.mono i _ X hy e (hE.down_le p i hi _ e h0)
            · exact hex e hm)
          simpa using this)
      simpa using hrest

#print axioms restsT_of_restSpec
#print axioms call_elim_rest
#print axioms restSpec_of_body
#print axioms listT_spreads
#print axioms spread_parts_safe

end Verification.Model.RestCalls
