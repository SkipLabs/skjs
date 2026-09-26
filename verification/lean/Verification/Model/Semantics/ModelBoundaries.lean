import Verification.Model.Semantics.Rules

/-! Regression proofs constraining the current rules: allocation forbids
unrestricted distribution over a signature's result, and finite observation
depth forbids collapsing all ultimately incompatible reference results to
bottom. -/
namespace Verification.Model.ModelBoundaries

/-! ## Code of one node

The counterexamples below are callables of one node, `return e`: a call enters
the code's run (`graphEntry`), the run enters its node, evaluates `e` in its
frame and returns the value. -/

/-- One-node code returning `e`, of one parameter. -/
def oneNode (e : Tm) : CallCode := .graph 1 [e] [(.ret, none)] 0 []

/-- A run returning what its node evaluates to is as safe as that evaluation:
the return spends one step, which an admissible type can pay. -/
theorem frame_ret_safe {A : Fam} (hA : Adm A) {E K L d} :
    ∀ (n : Nat) (W : WorldT n) (h : Heap) (t : Tm), WorldAdm W → HeapOk n W h →
      Safe A n W h t → Safe A n W h (.frame E K t L d .ret none) := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hw hh hs
    rcases hs with (⟨hv, ht⟩ | ⟨v, hr, hsc⟩) | ⟨U, h', t', hx, hu, st, hh', hs⟩
    · exact Or.inr ⟨trunc n (Nat.le_succ n) W, h, t, WExt_refl _, WorldAdm_trunc _ hw,
        .frameRet hv, HeapOk_trunc n W h hh,
        value_safe A n _ h t hv (hA.down_le (n + 1) n (Nat.le_succ n) W t ht)⟩
    · exact Or.inr ⟨trunc n (Nat.le_succ n) W, h, .throw v, WExt_refl _, WorldAdm_trunc _ hw,
        .frameRaise hr, HeapOk_trunc n W h hh,
        thrown_safe A n _ h ⟨v, .throwV (raises_val hr), hsc⟩⟩
    · exact Or.inr ⟨U, h', _, hx, hu, .frameC st, hh', ih U h' t' hu hh' hs⟩

/-! ## Allocation and arrow results -/

/-- Allocate a fresh cell holding null, and return it. -/
def allocFn : Tm := .obj 0 (oneNode (.alloc .nul))

/-- The function meets `(x: null) => ref B` for *every* admissible `B` that
contains null: the contract of the new cell is chosen by the membership proof,
not by the program. -/
theorem allocFn_typed {Rc B : Fam} (hB : Adm B)
    (hnul : ∀ (j : Nat) (W : WorldT j), B j W .nul) (k : Nat) (W : WorldT k) :
    callsT [(Rc, [nulT], refT B)] k W allocFn := by
  refine ⟨⟨_, _, rfl, rfl, by simp [Scoped, allocFn, oneNode]⟩, ?_⟩
  intro p hp j hj U hx hu heap hh r hrv hr args hvals ha
  cases List.mem_singleton.mp hp
  refine ⟨_, .graph hrv hvals, ?_⟩
  cases j with
  | zero => trivial
  | succ j =>
    refine Or.inr ⟨trunc j (Nat.le_succ j) U, heap, _, WExt_refl _, WorldAdm_trunc _ hu,
      .gotoEnter rfl rfl, HeapOk_trunc j U heap hh, ?_⟩
    apply frame_ret_safe (refT_adm B) j _ heap _ (WorldAdm_trunc _ hu) (HeapOk_trunc j U heap hh)
    simpa [instantiate] using alloc_rule hB j _ heap .nul rfl (WorldAdm_trunc _ hu)
      (HeapOk_trunc j U heap hh) (hnul _ _)

/-- Two references whose operands differ have an empty intersection: a location
belongs to `ref X` only when the world's contract for it *equals* `⟦X⟧`, and one
cell has one contract. -/
theorem ref_inter_empty (j : Nat) (hj : 0 < j) (W : WorldT j) (u : Val) :
    ¬ interT (refT nulT) (refT (unionT nulT boolT)) j W u := by
  rintro ⟨h1, h2⟩
  obtain ⟨flds, l, c, he, hf, hl, hc⟩ := refT_iff.mp h1
  obtain ⟨flds', l', c', he', hf', hl', hc'⟩ := refT_iff.mp h2
  subst he
  cases he'
  cases Option.some.inj (hf.symm.trans hf')
  rw [hl] at hl'
  cases hl'
  have h1 := (hc' 0 hj (ofList []) .tru).mpr (Or.inr (Or.inl rfl))
  exact absurd ((hc 0 hj (ofList []) .tru).mp h1) (by simp [nulT])

theorem trunc_empty {k j : Nat} (h : j ≤ k) :
    trunc j h (ofList ([] : List (Ctr k))) = ofList [] := by
  simp [trunc, toList_ofList]

theorem emptyWorld_adm (k : Nat) : WorldAdm (ofList ([] : List (Ctr k))) := by
  intro l c hl
  simp [lookup] at hl

/-- **The classical arrow decomposition is unsound here.** No rule may conclude
the signature `(x: A) => B ∧ C` from `(x: A) => B` and `(x: A) => C`. -/
theorem arrow_inter_codomain_fails :
    ¬ ∀ (Rc A B C : Fam) (k : Nat) (W : WorldT k) (v : Val),
        callsT [(Rc, [A], B)] k W v → callsT [(Rc, [A], C)] k W v →
        callsT [(Rc, [A], interT B C)] k W v := by
  intro hrule
  have h1 : callsT [(undefT, [nulT], refT nulT)] 5 (ofList []) allocFn :=
    allocFn_typed nulT_adm (fun _ _ => rfl) 5 _
  have h2 : callsT [(undefT, [nulT], refT (unionT nulT boolT))] 5 (ofList []) allocFn :=
    allocFn_typed (unionT_adm nulT boolT nulT_adm boolT_adm) (fun _ _ => Or.inl rfl) 5 _
  have hb := hrule _ _ _ _ 5 (ofList []) allocFn h1 h2
  have hx : WExt (trunc 4 (by omega) (ofList ([] : List (Ctr 5)))) (ofList []) := by
    rw [trunc_empty]
    exact WExt_refl _
  obtain ⟨result, hi, hsafe⟩ := hb.2 _ (List.mem_singleton_self _) 4 (by omega) (ofList []) hx
    (emptyWorld_adm 4) [] (emptyHeapOk 4) .undef rfl rfl [.nul]
    (by simp [CallArguments.Values, isVal]) (ArgsShort_of_exact ⟨rfl, trivial⟩)
  cases hi
  -- the run enters its node
  have s1 : Step [] (CallArguments.graphEntry 1 [.alloc .nul] [(.ret, none)] 0 [] false .undef [.nul])
      [] _ := .gotoEnter rfl rfl
  rcases hsafe with (⟨hv, -⟩ | hr) | ⟨_, _, _, _, _, st, _, hs⟩
  · simp [CallArguments.graphEntry, isVal] at hv
  · exact hr.no_step s1
  obtain ⟨rfl, rfl⟩ := Step_det s1 st
  -- the allocation
  have s2 : Step [] (.frame [.alloc .nul] [(.ret, none)] (.alloc .nul) [.undef, .nul] .nul .ret none)
      [.nul] (.frame [.alloc .nul] [(.ret, none)] (.obj 0 .absent) [.undef, .nul] .nul .ret none) :=
    .frameC (.makeV rfl)
  rcases hs with (⟨hv, -⟩ | hr) | ⟨_, _, _, _, _, st, _, hs⟩
  · simp [isVal] at hv
  · exact hr.no_step s2
  obtain ⟨rfl, rfl⟩ := Step_det s2 st
  -- the return
  have s3 : Step [.nul] (.frame [.alloc .nul] [(.ret, none)] (.obj 0 .absent) [.undef, .nul] .nul .ret none)
      [.nul] (.obj 0 .absent) := .frameRet rfl
  rcases hs with (⟨hv, -⟩ | hr) | ⟨_, _, _, _, _, st, _, hs⟩
  · simp [isVal] at hv
  · exact hr.no_step s3
  obtain ⟨rfl, rfl⟩ := Step_det s3 st
  -- a location is a value, and it would have to inhabit an empty codomain
  rcases hs with (⟨-, hmem⟩ | hr) | ⟨_, _, _, _, _, st, _, _⟩
  · exact ref_inter_empty 1 (by omega) _ _ hmem
  · exact val_not_thrown rfl hr
  · exact value_no_step (show isVal (Tm.obj _ .absent) = true from rfl) st

/-! ## Finite observation of nested references -/

def nestedRef : Nat → Fam → Fam
  | 0, A => A
  | d + 1, A => refT (nestedRef d A)

theorem nested_agrees_cycle (d : Nat) (A : Fam) :
    ∀ n, n < d → ∀ W v, nestedRef d A n W v ↔ R n W v := by
  induction d with
  | zero => intro n hn; omega
  | succ d ih =>
    intro n hn W v
    rw [R_unfold]
    exact refT_contractive n _ _ (fun j hj U u => ih j (by omega) U u) W v

def bottomT : Fam := fun _ _ _ => False

/-- A function returning the location of a cyclic cell. -/
def constFn : Tm := .obj 1 (oneNode (.obj 0 .absent))

/-- A constant body returns a location before two reference levels can be
observed: the call enters the run, then its node, and the value is observed
two levels below the call. Distinct eventual contracts remain
indistinguishable at these budgets. -/
theorem constant_nested_calls (Rc A : Fam) :
    callsT [(Rc, [nulT], nestedRef 2 A)] 4 (ofList [res R]) constFn := by
  refine ⟨⟨_, _, rfl, rfl, by simp [Scoped, constFn, oneNode]⟩, ?_⟩
  intro p hp j hj U hx hu heap hh r hrv hr args hvals ha
  cases List.mem_singleton.mp hp
  refine ⟨_, .graph hrv hvals, ?_⟩
  match j, hj with
  | 0, _ => trivial
  | 1, _ =>
    exact Or.inr ⟨_, heap, _, WExt_refl _, WorldAdm_trunc _ hu, .gotoEnter rfl rfl,
      HeapOk_trunc 0 U heap hh, trivial⟩
  | m + 2, hm =>
    refine Or.inr ⟨trunc (m + 1) (Nat.le_succ _) U, heap, _, WExt_refl _, WorldAdm_trunc _ hu,
      .gotoEnter rfl rfl, HeapOk_trunc (m + 1) U heap hh, ?_⟩
    refine Or.inr ⟨trunc m (Nat.le_succ m) (trunc (m + 1) (Nat.le_succ _) U), heap, .obj 0 .absent,
      WExt_refl _, WorldAdm_trunc _ (WorldAdm_trunc _ hu), .frameRet rfl,
      HeapOk_trunc m _ heap (HeapOk_trunc (m + 1) U heap hh), ?_⟩
    have hr : R m (trunc m (Nat.le_succ m) (trunc (m + 1) (Nat.le_succ _) U)) (.obj 0 .absent) := by
      rw [trunc_trunc]
      exact R_adm.down_le (m + 2) m (by omega) U _ (R_adm.mono (m + 2) _ U hx _
        (R_adm.down_le 4 (m + 2) (Nat.le_of_lt hm) _ _ (R_cyclic 4)))
    exact value_safe _ m _ heap (.obj 0 .absent) rfl
      ((nested_agrees_cycle 2 A m (by omega) _ _).mpr hr)

theorem constant_not_bottom (Rc : Fam) (hRc : Rc 3 (ofList [res R]) .undef) :
    ¬ callsT [(Rc, [nulT], bottomT)] 4 (ofList [res R]) constFn := by
  intro ht
  have hx : WExt (trunc 3 (by omega) (ofList [res R] : WorldT 4))
      (ofList [res R] : WorldT 3) := by
    rw [trunc_res]
    exact WExt_refl _
  obtain ⟨result, hi, hs⟩ := ht.2 _ (List.mem_singleton_self _) 3 (by omega) _ hx
    (cyclic_world_adm 3) [.obj 0 .absent] (cyclic_heap_ok 3) .undef rfl hRc [.nul]
    (by simp [CallArguments.Values, isVal]) (ArgsShort_of_exact ⟨rfl, trivial⟩)
  cases hi
  have s1 : Step [.obj 0 .absent]
      (CallArguments.graphEntry 1 [.obj 0 .absent] [(.ret, none)] 0 [] false .undef [.nul])
      [.obj 0 .absent] _ := .gotoEnter rfl rfl
  rcases hs with (⟨hv, -⟩ | hr) | ⟨_, _, _, _, _, st, _, hs⟩
  · simp [CallArguments.graphEntry, isVal] at hv
  · exact hr.no_step s1
  obtain ⟨rfl, rfl⟩ := Step_det s1 st
  have s2 : Step [.obj 0 .absent]
      (.frame [.obj 0 .absent] [(.ret, none)] (.obj 0 .absent) [.undef, .nul] .nul .ret none)
      [.obj 0 .absent] (.obj 0 .absent) := .frameRet rfl
  rcases hs with (⟨hv, -⟩ | hr) | ⟨_, _, _, _, _, st, _, hs⟩
  · simp [isVal] at hv
  · exact hr.no_step s2
  obtain ⟨rfl, rfl⟩ := Step_det s2 st
  exact safe_value_mem (show isVal (Tm.obj 0 .absent) = true from rfl) hs

/-- It is UNSOUND to extrapolate the single-reference empty-result rule to
arbitrary reference nesting in the exact indexed interpretation. This is a
finite-budget counterexample in an admissible world with a satisfying heap. -/
theorem deeper_reference_rule_fails : ¬ (∀ n W v,
    callsT [(undefT, [nulT], nestedRef 2 nulT)] n W v →
    callsT [(undefT, [nulT], nestedRef 2 boolT)] n W v →
    callsT [(undefT, [nulT], bottomT)] n W v) := by
  intro hr
  exact constant_not_bottom undefT rfl
    (hr 4 _ _ (constant_nested_calls undefT nulT) (constant_nested_calls undefT boolT))

#print axioms frame_ret_safe
#print axioms arrow_inter_codomain_fails
#print axioms deeper_reference_rule_fails
end Verification.Model.ModelBoundaries
