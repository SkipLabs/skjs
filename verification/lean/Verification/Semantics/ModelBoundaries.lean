import Verification.Semantics.Rules
import Verification.Semantics.HeapObservations

/-! Regression proofs constraining the current rules: allocation forbids
unrestricted distribution over a signature's result, finite observation
depth forbids collapsing all ultimately incompatible reference results to
bottom, and a current heap observation is neither framed by an ordinary
callback, nor a value type, nor a narrower invariant. -/
namespace Verification.ModelBoundaries

/-! ## Code of one node

The counterexamples below are callables of one node, `return e`: a call enters
the code's run (`graphEntry`), the run enters its node, evaluates `e` in its
frame and returns the value. -/

/-- One-node code returning `e`, of one parameter. -/
def oneNode (e : Tm) : CallCode := .graph 1 [e] [(.ret, none)] 0 []

/-- A run returning what its node evaluates to is as safe as that evaluation:
the return spends one step, which an admissible type can pay. -/
theorem frame_ret_safe {Ξ A : Fam} (hΞ : Adm Ξ) (hA : Adm A) {E K L d} :
    ∀ (n : Nat) (W : WorldT n) (h : Heap) (t : Tm), WorldAdm W → HeapOk n W h →
      Safe Ξ A n W h t → Safe Ξ A n W h (.frame E K t L d .ret none) := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hw hh hs
    rcases hs with (⟨hv, ht⟩ | ⟨v, hr, hsc, hxi⟩) | ⟨U, h', t', hx, hu, st, hh', hs⟩
    · exact Or.inr ⟨trunc n (Nat.le_succ n) W, h, t, WExt_refl _, WorldAdm_trunc _ hw,
        .frameRet hv, HeapOk_trunc n W h hh,
        value_safe A n _ h t hv (hA.down_le (n + 1) n (Nat.le_succ n) W t ht)⟩
    · exact Or.inr ⟨trunc n (Nat.le_succ n) W, h, .throw v, WExt_refl _, WorldAdm_trunc _ hw,
        .frameRaise hr, HeapOk_trunc n W h hh,
        thrown_safe A n _ h ⟨v, .throwV (raises_val hr) (raises_sourceVal hr), hsc,
          hΞ.down_le (n + 1) n (Nat.le_succ n) W v hxi⟩⟩
    · exact Or.inr ⟨U, h', _, hx, hu, .frameC st, hh', ih U h' t' hu hh' hs⟩

/-! ## Allocation and arrow results -/

/-- Allocate a fresh cell holding null, and return it. -/
def allocFn : Tm := .obj 0 (oneNode (.alloc .nul))

/-- The function meets `(x: null) => ref B` for *every* admissible `B` that
contains null: the contract of the new cell is chosen by the membership proof,
not by the program. -/
theorem allocFn_typed {Ξ Rc B : Fam} (hΞ : Adm Ξ) (hB : Adm B)
    (hnul : ∀ (j : Nat) (W : WorldT j), B j W .nul) (k : Nat) (W : WorldT k) :
    callsT Ξ [(Rc, [nulT], refT B)] k W allocFn := by
  refine ⟨⟨_, _, _, rfl, rfl, by simp [Scoped, allocFn, oneNode]⟩, ?_⟩
  intro p hp j hj U hx hu heap hh r hrv hr args hvals ha
  cases List.mem_singleton.mp hp
  refine ⟨_, .graph hrv hvals, ?_⟩
  cases j with
  | zero => trivial
  | succ j =>
    refine Or.inr ⟨trunc j (Nat.le_succ j) U, heap, _, WExt_refl _, WorldAdm_trunc _ hu,
      .gotoEnter rfl rfl, HeapOk_trunc j U heap hh, ?_⟩
    apply frame_ret_safe hΞ (refT_adm B) j _ heap _ (WorldAdm_trunc _ hu) (HeapOk_trunc j U heap hh)
    simpa [instantiate] using alloc_rule hB j _ heap .nul rfl (WorldAdm_trunc _ hu)
      (HeapOk_trunc j U heap hh) (hnul _ _)

/-- Two references whose operands differ have an empty intersection: a location
belongs to `ref X` only when the world's contract for it *equals* `⟦X⟧`, and one
cell has one contract. -/
theorem ref_inter_empty (j : Nat) (hj : 0 < j) (W : WorldT j) (u : Val) :
    ¬ interT (refT nulT) (refT (unionT nulT boolT)) j W u := by
  rintro ⟨h1, h2⟩
  obtain ⟨flds, l, c, oid, he, hf, hl, hc⟩ := refT_iff.mp h1
  obtain ⟨flds', l', c', oid', he', hf', hl', hc'⟩ := refT_iff.mp h2
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
        callsT topF [(Rc, [A], B)] k W v → callsT topF [(Rc, [A], C)] k W v →
        callsT topF [(Rc, [A], interT B C)] k W v := by
  intro hrule
  have h1 : callsT topF [(undefT, [nulT], refT nulT)] 5 (ofList []) allocFn :=
    allocFn_typed topF_adm nulT_adm (fun _ _ => rfl) 5 _
  have h2 : callsT topF [(undefT, [nulT], refT (unionT nulT boolT))] 5 (ofList []) allocFn :=
    allocFn_typed topF_adm (unionT_adm nulT boolT nulT_adm boolT_adm) (fun _ _ => Or.inl rfl) 5 _
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
      [.nul, .nul] (.frame [.alloc .nul] [(.ret, none)] (.obj 0 .absent) [.undef, .nul] .nul .ret none) :=
    .frameC (.makeV rfl)
  rcases hs with (⟨hv, -⟩ | hr) | ⟨_, _, _, _, _, st, _, hs⟩
  · simp [isVal] at hv
  · exact hr.no_step s2
  obtain ⟨rfl, rfl⟩ := Step_det s2 st
  -- the return
  have s3 : Step [.nul, .nul] (.frame [.alloc .nul] [(.ret, none)] (.obj 0 .absent) [.undef, .nul] .nul .ret none)
      [.nul, .nul] (.obj 0 .absent) := .frameRet rfl
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
    callsT Ξ [(Rc, [nulT], nestedRef 2 A)] 4 (ofList [res R]) constFn := by
  refine ⟨⟨_, _, _, rfl, rfl, by simp [Scoped, constFn, oneNode]⟩, ?_⟩
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
    ¬ callsT Ξ [(Rc, [nulT], bottomT)] 4 (ofList [res R]) constFn := by
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
    callsT Ξ [(undefT, [nulT], nestedRef 2 nulT)] n W v →
    callsT Ξ [(undefT, [nulT], nestedRef 2 boolT)] n W v →
    callsT Ξ [(undefT, [nulT], bottomT)] n W v) := by
  intro hr
  exact constant_not_bottom undefT rfl
    (hr 4 _ _ (constant_nested_calls undefT nulT) (constant_nested_calls undefT boolT))

/-! ## Current heap observations

A cell of the persistent Boolean world, observed to hold `true`
(`HeapObservations.Observes`). -/
section Observations
open HeapObservations

/-- A callback overwriting a cell it names: graph code of one node, taking one
parameter. -/
def writer (l : Nat) : Tm := .obj 1 (.graph 1 [.write (.obj l .absent) .fls] [(.ret, none)] 0 [])

/-- The persistent Boolean world admits both heaps at every budget. -/
def boolWorld (n : Nat) : WorldT n := ofList [res boolT]

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

/-- A callback cannot be given a generic observation frame: one of type
`(x: null) => null` may overwrite the observed cell. Five levels see the call
enter the code, its node, the write, the run returning, and the returned
value/postcondition. -/
theorem callback_does_not_frame (W : WorldT 5) :
    ¬ SafePost Ξ nulT (fun h _ => Observes h 0 .tru) 5 W [.tru]
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

/-- A point observation does not narrow the invariant: a Boolean cell currently
true is not a `Ref true`. The read/write capability preorder that schema
absorption uses is therefore no exact normalization of a reference together
with its current contents. -/
theorem observation_does_not_narrow_invariant :
    HeapOk 1 (boolWorld 1) [.tru] ∧ refT boolT 1 (boolWorld 1) (.obj 0 .absent) ∧
    Observes [.tru] 0 .tru ∧ ¬ refT (exact .tru) 1 (boolWorld 1) (.obj 0 .absent) := by
  refine ⟨boolWorld_heap 1 .tru (Or.inl rfl),boolWorld_ref 1,rfl,?_⟩
  intro hr
  obtain ⟨flds,l,c,oid,he,hf,hl,hc⟩ := refT_iff.mp hr
  cases he
  simp at hf
  subst l
  simp [boolWorld,lookup] at hl
  subst c
  have hf := (hc 0 (by decide) (ofList []) .fls).mp (Or.inr rfl)
  cases hf

end Observations

#print axioms frame_ret_safe
#print axioms arrow_inter_codomain_fails
#print axioms deeper_reference_rule_fails
#print axioms callback_does_not_frame
#print axioms observation_not_a_value_type
#print axioms observation_does_not_narrow_invariant
end Verification.ModelBoundaries
