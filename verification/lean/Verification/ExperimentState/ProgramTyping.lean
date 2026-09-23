import Verification.ExperimentState.CallableObjects
import Verification.ExperimentState.PositiveCertificates

/-!
# Program typing over positive recursive types

Types are finite unions of graph labels. Constructor rules inspect a singleton
expanded clause; subsumption is justified by the existing checked certificates.
The typing judgement is syntactic. Semantic environments enter only its soundness
proof, not its rules.
-/
namespace Verification.ExperimentState.ProgramTyping
open PositiveNormalization PositiveGraphs PositiveRules Tower

variable {ι : Type}

abbrev Ty (ι : Type) := List ι

def Represents (G : NormalGraph ι) (A : Ty ι) (c : Clause (Ty ι)) : Prop :=
  expand G A = [c]

theorem represents_sem {G : NormalGraph ι} {A c} (hr : Represents G A c) (n W v) :
    meaning G A n W v ↔ sem (meaning G) c n W v := by
  rw [expand_sem, hr]
  simp [semList, setSem]

theorem meaning_adm (G : NormalGraph ι) (A : Ty ι) : Adm (meaning G A) :=
  setSem_adm (fun i => Tower.denote_adm (normal_congr G)
    (fun X _ i => setSem_adm (sem_adm (setSem X)) (G i)) i) A

/-- A union of label lists means either side. -/
theorem meaning_append (G : NormalGraph ι) (A B : Ty ι) (n W v) :
    meaning G (A ++ B) n W v ↔ meaning G A n W v ∨ meaning G B n W v := by
  simp [meaning, setSem, List.mem_append, or_and_right, exists_or]

/-- The type a tuple contract states for an index, syntactically: a required
position's, an optional position's, or the rest's where any further position
may be. -/
def positionTy (T : Tuple (Ty ι)) (i : Nat) : Option (Ty ι) :=
  match T.required[i]? with
  | some A => some A
  | none => match T.optional[i - T.required.length]? with
    | some A => some A
    | none => if T.required.length + T.optional.length ≤ i then T.rest else none

theorem positionFam_tupleFams {X : Ty ι → Fam} (T : Tuple (Ty ι)) (i : Nat) :
    positionFam (tupleFams X T) i = (positionTy T i).map X := by
  simp only [positionFam, positionTy, tupleFams, List.getElem?_map, List.length_map]
  cases T.required[i]? <;> cases T.optional[i - T.required.length]? <;> simp <;> split <;> simp

theorem meaning_value {G : NormalGraph ι} {A n W v} (h : meaning G A n W v) :
    isVal v = true ∧ Scoped 0 v := by
  obtain ⟨c, _, hc⟩ := (expand_sem G A n W v).mp h
  exact sem_value hc

theorem meaning_valOnly (G : NormalGraph ι) (A : Ty ι) : ValOnly (meaning G A) :=
  fun _ _ _ h => (meaning_value h).1

def EnvOk (G : NormalGraph ι) (Γ : List (Ty ι)) (ρ : Env) (n : Nat) (W : WorldT n) : Prop :=
  (∀ i, Scoped 0 (ρ i)) ∧ ∀ i A, Γ[i]? = some A → meaning G A n W (ρ i)

theorem EnvOk.transfer {G : NormalGraph ι} {Γ ρ n W} (h : EnvOk G Γ ρ n W)
    (j : Nat) (hj : j ≤ n) (U : WorldT j) (hx : WExt (trunc j hj W) U) : EnvOk G Γ ρ j U :=
  ⟨h.1, fun i A hi => (meaning_adm G A).mono j _ U hx _
    ((meaning_adm G A).down_le n j hj W _ (h.2 i A hi))⟩

theorem EnvOk.push {G : NormalGraph ι} {Γ ρ n W A a} (h : EnvOk G Γ ρ n W)
    (ha : meaning G A n W a) : EnvOk G (A :: Γ) (push a ρ) n W := by
  constructor
  · intro i; cases i with
    | zero => exact (meaning_value ha).2
    | succ i => exact h.1 i
  · intro i B hi; cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
              subst B; exact ha
    | succ i => exact h.2 i B hi

/-- Parameter zero stays at slot zero; captures follow all parameters. -/
theorem EnvOk.prepend {G : NormalGraph ι} {Γ ρ n W As args}
    (h : EnvOk G Γ ρ n W) (ha : ArgsT (As.map (meaning G)) n W args) :
    EnvOk G (As ++ Γ) (prependArgs args ρ) n W := by
  induction As generalizing args with
  | nil => cases args <;> simp_all [ArgsT, prependArgs]
  | cons A As ih =>
    cases args with
    | nil => exact False.elim ha
    | cons a args => exact (ih ha.2).push ha.1

/-- A body safe under every declared parameter environment establishes the
native invocation contract. All overloads here have the descriptor's arity. -/
theorem invocation_of_body {G : NormalGraph ι} {Γ ρ n W b arity}
    {L : List (List (Ty ι) × Ty ι)} (he : EnvOk G Γ ρ n W)
    (hlen : ∀ p ∈ L, p.1.length = arity)
    (hb : ∀ p ∈ L, ∀ j U heap env, EnvOk G (p.1 ++ Γ) env j U →
      WorldAdm U → HeapOk j U heap → Safe (meaning G p.2) j U heap (instantiate 0 env b)) :
    InvocationSpec arity (L.map fun p => (p.1.map (meaning G), meaning G p.2))
      n W (instantiate arity ρ b) := by
  refine ⟨instantiate_scoped ρ he.1 b arity, ?_⟩
  intro p hp j hj U hx hu heap hok args ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hlength : args.length = arity := by
    simpa only [List.length_map, hlen q hq] using ArgsT_length ha
  have henv := (he.transfer j (Nat.le_of_lt hj) U hx).prepend ha
  have hscoped : ∀ (As : List (Ty ι)) args, ArgsT (As.map (meaning G)) j U args →
      ∀ a ∈ args, Scoped 0 a := by
    intro As
    induction As with
    | nil => intro args ha; cases args <;> simp_all [ArgsT]
    | cons A As ih =>
      intro args ha
      cases args with
      | nil => exact False.elim ha
      | cons a args =>
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact (meaning_value ha.1).2
        · exact ih args ha.2 v hv
  have hargs := hscoped q.1 args ha
  unfold CallArguments.bindParameters
  rw [← hlength, CallArguments.parameters_exact]
  rw [show args.length = 0 + args.length from (Nat.zero_add _).symm, instantiate_args ρ he.1 hargs]
  exact hb q hq j U heap _ henv hu hok

/-- An equality established by a branch can refine one immutable slot. -/
theorem EnvOk.refine {G : NormalGraph ι} {Γ ρ n W i A B}
    (h : EnvOk G Γ ρ n W) (hi : Γ[i]? = some A)
    (hb : meaning G B n W (ρ i)) : EnvOk G (Γ.set i B) ρ n W := by
  refine ⟨h.1, ?_⟩
  intro j C hc
  by_cases hj : j = i
  · subst j
    have hi' := (List.getElem?_eq_some_iff.mp hi).1
    rw [List.getElem?_set_self hi'] at hc
    cases Option.some.inj hc
    exact hb
  · rw [List.getElem?_set_ne (Ne.symm hj)] at hc
    exact h.2 j C hc

/-- General evaluation-context composition. Contexts are supplied with their
ordinary small-step congruence rule. -/
theorem bind {A B : Fam} (C : Tm → Tm)
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

/-- An operand remains safe after earlier operands spend budget or change the heap. -/
def FutureSafe (A : Fam) (n : Nat) (W : WorldT n) (t : Tm) : Prop :=
  ∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
    ∀ heap, HeapOk j U heap → Safe A j U heap t

theorem FutureSafe.transfer {A n W t} (h : FutureSafe A n W t)
    {j : Nat} (hj : j ≤ n) {U : WorldT j} (hx : WExt (trunc j hj W) U) :
    FutureSafe A j U t := by
  intro k hk V hy hv heap hh
  apply h k (by omega) V _ hv heap hh
  apply WExt_trans _ hy
  simpa only [trunc_trunc] using WExt_trunc hk hx

/-- Compose left-to-right argument evaluation with a continuation over the
resulting values. Earlier values retain their types across later heap effects. -/
theorem bind_list {B : Fam} (xs : List (Fam × Tm))
    (hA : ∀ p ∈ xs, Adm p.1) (C : List Tm → Tm)
    (lift : ∀ {h args h' args'}, CallArguments.ArgStep h args h' args' → Step h (C args) h' (C args'))
    {n W heap} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (ht : ∀ p ∈ xs, FutureSafe p.1 n W p.2)
    (hk : ∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
      ∀ heap args, HeapOk j U heap → ArgsT (xs.map Prod.fst) j U args → Safe B j U heap (C args)) :
    Safe B n W heap (C (xs.map Prod.snd)) := by
  induction xs generalizing n C heap with
  | nil =>
    exact hk n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap [] hh trivial
  | cons p xs ih =>
    apply bind (fun a => C (a :: xs.map Prod.snd)) (fun hs => lift (.head hs)) n W heap p.2 hw hh
      (ht p (by simp) n (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw heap hh)
    intro j hj U hx hu heap' v hok hv ha
    apply ih (fun q hq => hA q (by simp [hq])) (fun args => C (v :: args))
      (fun hs => lift (.tail hv hs)) hu hok
      (fun q hq => (ht q (by simp [hq])).transfer hj hx)
    intro k hk' V hy hv' heap'' args hok' hargs
    have hworld : WExt (trunc k (Nat.le_trans hk' hj) W) V := by
      apply WExt_trans _ hy
      simpa only [trunc_trunc] using WExt_trunc hk' hx
    apply hk k (Nat.le_trans hk' hj) V hworld hv' heap'' (v :: args) hok'
    exact ⟨(hA p (by simp)).mono k _ V hy v ((hA p (by simp)).down_le j k hk' U v ha), hargs⟩

/-- Native call compatibility includes the callee and every effectful actual,
then uses the invocation contract only after all operands have become values. -/
theorem call_safe {B : Fam} (xs : List (Fam × Tm))
    (hA : ∀ p ∈ xs, Adm p.1) (hAv : ∀ p ∈ xs, ValOnly p.1)
    {n W heap f} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe (callsT [(xs.map Prod.fst, B)]) n W heap f)
    (ha : ∀ p ∈ xs, FutureSafe p.1 n W p.2) :
    Safe B n W heap (.call f (xs.map Prod.snd)) := by
  apply bind (fun f => .call f (xs.map Prod.snd)) Step.callL n W heap f hw hh hf
  intro j hj U hx hu heap' v hok hv hfun
  apply bind_list xs hA (Tm.call v)
    (fun hs => (CallArguments.Prepare.args hv hs).step) hu hok
    (fun p hp => (ha p hp).transfer hj hx)
  intro k hk V hy hv' heap'' args hok' hargs
  have hf' := (callsT_adm _).mono k _ V hy v ((callsT_adm _).down_le j k hk U v hfun)
  exact call_elim (by intro A h; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h; exact hA p hp)
    (by intro A h; obtain ⟨p,hp,rfl⟩ := List.mem_map.mp h; exact hAv p hp)
    hf' (List.mem_singleton_self _) hargs hv' hok'

/-- A call that writes fewer actuals than its selected signature declares. The
omitted positions are exactly the ones whose contract admits `undefined`, which
is the value the machine binds there; nothing is added to the source term. -/
theorem call_safe_short {B : Fam} (xs : List (Fam × Tm)) (Us : List Fam)
    (hA : ∀ p ∈ xs, Adm p.1) (hAv : ∀ p ∈ xs, ValOnly p.1)
    (hUA : ∀ A ∈ Us, Adm A) (hUAv : ∀ A ∈ Us, ValOnly A)
    {n W heap f} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe (callsT [(xs.map Prod.fst ++ Us, B)]) n W heap f)
    (ha : ∀ p ∈ xs, FutureSafe p.1 n W p.2)
    (hu : ∀ A ∈ Us, FutureSafe A n W .undef) :
    Safe B n W heap (.call f (xs.map Prod.snd)) := by
  apply bind (fun f => .call f (xs.map Prod.snd)) Step.callL n W heap f hw hh hf
  intro j hj U hx hw' heap' v hok hv hfun
  apply bind_list xs hA (Tm.call v)
    (fun hs => (CallArguments.Prepare.args hv hs).step) hw' hok
    (fun p hp => (ha p hp).transfer hj hx)
  intro k hk V hy hv' heap'' args hok' hargs
  cases k with
  | zero => trivial
  | succ k =>
    have hf' := (callsT_adm _).mono (k+1) _ V hy v ((callsT_adm _).down_le j (k+1) hk U v hfun)
    have hundef : ∀ A ∈ Us, A (k+1) V .undef := by
      intro A hA'
      exact safe_value_mem rfl
        (((hu A hA').transfer hj hx).transfer hk hy (k+1) (Nat.le_refl _) V
          (by rw [trunc_id]; exact WExt_refl _) hv' heap'' hok')
    refine call_elim_short (p := (xs.map Prod.fst ++ Us, B))
      (pad := List.replicate Us.length .undef)
      (by
        intro A h
        rcases List.mem_append.mp h with h | h
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hA p hp
        · exact hUA A h)
      (by
        intro A h
        rcases List.mem_append.mp h with h | h
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h; exact hAv p hp
        · exact hUAv A h)
      (by intro a h; exact List.eq_of_mem_replicate h)
      hf' (List.mem_singleton_self _)
      (ArgsT_append hargs (ArgsT_undef hundef)) hv' hok'

/-- A shape-only test has a fixed answer. Numeric equality needs the
singleton bits; the whole number family has no uniform answer. -/
def tagShape (tag : Tag) (s : Nat) : Option Bool :=
  match tag with
  | .isNul => some (s == 0) | .isBool => some (s == 1) | .isRef => some (s == 2)
  | .isFun => some (s == 3) | .isUndef => some (s == 4)
  | .isNullish => some (s == 0 || s == 4) | .isNum => some (s == 5)
  | .numEq _ => if s == 5 then none else some false
  | .isStr => some (s == 6)
  | .strEq _ => if s == 6 then none else some false

def tagClause (tag : Tag) (c : Clause α) : Option Bool :=
  match tag, c with
  | _, .top => none
  | .numEq bits, .numLit value => some (numberEqual value bits)
  | .strEq s, .strLit t => some (s == t)
  | _, _ => tagShape tag (shape c)

/-- A finite syntactic check; unknown numeric answers cannot establish either
branch. It neither executes a term nor queries semantic membership. -/
def Answers (G : NormalGraph ι) (A : Ty ι) (tag : Tag) (q : Bool) : Prop :=
  ∀ c ∈ expand G A, tagClause tag c = some q

theorem tagClause_sound {S : α → Fam} {c tag q n W v}
    (hq : tagClause tag c = some q) (hv : sem S c n W v) : tagHolds tag v = q := by
  cases ht : tag with
  | numEq bits =>
    cases c <;> simp [ht, tagClause, tagShape, shape] at hq
    all_goals subst q
    case numLit value =>
      change v = .num value at hv
      subst v
      rfl
    all_goals
      have hs := sem_shape (by simp) hv
      cases v <;> simp_all [ht,valueShape,tagHolds,shape]
  | strEq s =>
    cases c <;> simp [ht, tagClause, tagShape, shape] at hq
    all_goals subst q
    case strLit t =>
      change v = .str t at hv
      subst v
      rfl
    all_goals
      have hs := sem_shape (by simp) hv
      cases v <;> simp_all [ht,valueShape,tagHolds,shape]
  | isNul | isBool | isRef | isFun | isUndef | isNullish | isNum | isStr =>
    by_cases hc : c = .top
    · subst hc; simp [ht, tagClause] at hq
    have htag : some (tagHolds tag v) = tagShape tag (valueShape v) := by
      rw [ht]
      cases v <;> first | rfl | (rename_i fs code; cases code <;> rfl)
    rw [sem_shape hc hv, ht] at htag
    exact Option.some.inj (htag.trans (by simpa only [ht,tagClause] using hq))

theorem answers_sound {G : NormalGraph ι} {A tag q n W v}
    (hq : Answers G A tag q) (hv : meaning G A n W v) : tagHolds tag v = q := by
  obtain ⟨c, hc, hv⟩ := (expand_sem G A n W v).mp hv
  exact tagClause_sound (hq c hc) hv

/-! ## Variadic functions

A variadic body finds the actuals past its fixed parameters in a fresh array in
slot 0. The array's type is an object whose one field holds a store of any
length at the element type; a spread reads a store whose every position's type
is among the element type's labels, and `undefined` must be among them when the
store may have a hole. -/

/-- The variadic signatures a callable type carries, fixed or callable object
alike; none for any other type. -/
def restSigs (G : NormalGraph ι) (F : Ty ι) : List (List (Ty ι) × Ty ι × Ty ι) :=
  match expand G F with
  | [.arrs _ S] | [.callable _ _ _ S] => S
  | _ => []

theorem restsT_of_restSigs {G : NormalGraph ι} {F : Ty ι} {s} (hs : s ∈ restSigs G F) {n W v}
    (hv : meaning G F n W v) :
    restsT [(s.1.map (meaning G), meaning G s.2.1, meaning G s.2.2)] n W v := by
  unfold restSigs at hs
  split at hs
  · rename_i L S hF
    have hv' := ((represents_sem hF n W v).mp hv).2
    exact restsT_select hv' (List.mem_map_of_mem hs)
  · rename_i P Ps L S hF
    have hv' := ((represents_sem hF n W v).mp hv).2
    exact restsT_select hv' (List.mem_map_of_mem hs)
  · cases hs

/-- The type of the array a variadic body receives: a record whose store field
holds any number of elements at `E`. -/
def RestArray (G : NormalGraph ι) (A E : Ty ι) : Prop :=
  match expand G A with
  | [.refs [(f, S)] [] []] => f = CallArguments.arrayStoreField ∧
      Represents G S (.list ⟨[], [], some E, false⟩ [])
  | _ => False

/-- A store type whose elements a spread passes at `E`. -/
def SpreadsInto (G : NormalGraph ι) (S E : Ty ι) : Prop :=
  match expand G S with
  | [.list T []] => (∀ A ∈ T.required ++ T.optional ++ T.rest.toList, ∀ i ∈ A, i ∈ E) ∧
      ((T.optional ≠ [] ∨ T.rest.isSome = true) → ∃ i ∈ E, Represents G [i] .undef)
  | _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (A E : Ty ι) : Decidable (RestArray G A E) := by
  unfold RestArray; split <;> (try dsimp only [Represents]) <;> infer_instance

instance [DecidableEq ι] (G : NormalGraph ι) (S E : Ty ι) : Decidable (SpreadsInto G S E) := by
  unfold SpreadsInto; split <;> (try dsimp only [Represents]) <;> infer_instance

/-- An actual as a call writes it: itself, or a spread of it. -/
def spreadTerm (p : Bool × Tm) : Tm := if p.1 then .spread p.2 else p.2

theorem instantiate_spreadTerm (d : Nat) (ρ : Env) (p : Bool × Tm) :
    instantiate d ρ (spreadTerm p) = spreadTerm (p.1, instantiate d ρ p.2) := by
  rcases p with ⟨_ | _, t⟩ <;> simp [spreadTerm, instantiate]

theorem positionTy_mem {T : Tuple (Ty ι)} {i : Nat} {A : Ty ι} (h : positionTy T i = some A) :
    A ∈ T.required ++ T.optional ++ T.rest.toList := by
  unfold positionTy at h
  split at h
  · rename_i B hB; cases h; simp [List.mem_of_getElem? hB]
  · split at h
    · rename_i B hB; cases h; simp [List.mem_of_getElem? hB]
    · split at h
      · simp [h]
      · cases h

theorem ArgsT_scoped {G : NormalGraph ι} {As : List (Ty ι)} {j U args}
    (ha : ArgsT (As.map (meaning G)) j U args) : ∀ a ∈ args, Scoped 0 a := by
  induction As generalizing args with
  | nil => cases args <;> simp_all [ArgsT]
  | cons A As ih =>
    cases args with
    | nil => exact False.elim ha
    | cons a args =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact (meaning_value ha.1).2
      · exact ih ha.2 v hv

theorem undef_of_label {G : NormalGraph ι} {E : Ty ι} {i : ι} (hi : i ∈ E)
    (hr : Represents G [i] .undef) (j : Nat) (U : WorldT j) : meaning G E j U .undef := by
  obtain ⟨i', hi', hv⟩ := (represents_sem hr j U .undef).mpr rfl
  simp only [List.mem_singleton] at hi'
  rw [hi'] at hv
  exact ⟨i, hi, hv⟩

theorem spreadsInto_sound {G : NormalGraph ι} {S E : Ty ι} (h : SpreadsInto G S E) :
    RestCalls.Spreads (meaning G S) (meaning G E) := by
  unfold SpreadsInto at h
  split at h
  · rename_i T hS
    obtain ⟨hsub, hhole⟩ := h
    have hl := RestCalls.listT_spreads (T := tupleFams (meaning G) T) (E := meaning G E)
      (by
        intro i A hA
        rw [positionFam_tupleFams] at hA
        obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp hA
        rintro n W v ⟨k, hk, hv⟩
        exact ⟨k, hsub A' (positionTy_mem hA') k hk, hv⟩)
      (by
        intro ho j U
        have ho' : T.optional ≠ [] ∨ T.rest.isSome = true := by
          simpa [tupleFams] using ho
        obtain ⟨i, hi, hr⟩ := hhole ho'
        exact undef_of_label hi hr j U)
    intro n W heap v hh hv
    exact hl n W heap v hh ((represents_sem hS n W v).mp hv).1
  · exact h.elim

/-- **Allocating the rest array.** A store of the given actuals, then the
object holding it, meets any rest-array type whose element type they meet. -/
theorem restArray_safe {G : NormalGraph ι} {A E : Ty ι} (hr : RestArray G A E)
    {n : Nat} {W : WorldT n} {h : Heap} {extra : List Tm} (hw : WorldAdm W) (hh : HeapOk n W h)
    (he : ∀ e ∈ extra, meaning G E n W e) :
    Safe (meaning G A) n W h (CallArguments.restArray extra) := by
  unfold RestArray at hr
  split at hr
  · rename_i f S hA
    obtain ⟨rfl, hS⟩ := hr
    apply bind_list [(meaning G S, .arrLit extra)] (by simp [meaning_adm])
      (fun args => .makeAt .absent [CallArguments.arrayStoreField] args)
      (fun hs => CallArguments.Step.makeArgs hs) hw hh
    · intro p hp j hj U hx hu heap hok
      simp only [List.mem_singleton] at hp
      subst hp
      have he' : ∀ e ∈ extra, meaning G E j U e := fun e hm =>
        (meaning_adm G E).mono j _ U hx e ((meaning_adm G E).down_le n j hj W e (he e hm))
      apply arr_alloc_rule (As := List.replicate extra.length (meaning G E))
        (by intro A hA; rw [List.eq_of_mem_replicate hA]; exact meaning_adm G E)
        j U heap extra (by simp) (fun v hv => (meaning_value (he' v hv)).1) hu hok
        (by
          intro p hp
          have hp1 := List.eq_of_mem_replicate (List.of_mem_zip hp).1
          rw [hp1]
          exact he' p.2 (List.of_mem_zip hp).2)
      intro k hk V hy hl
      refine (represents_sem hS k V _).mpr ⟨?_, by simp⟩
      have := listT_alloc (n := k) (W := V) (T := tupleFams (meaning G) ⟨[], [], some E, false⟩)
        (As := List.replicate extra.length (meaning G E)) (base := heap.length)
        (by simp [tupleFams]) (by simp [tupleFams])
        (by
          intro i A hA
          have := (List.getElem?_eq_some_iff.mp hA)
          simp only [List.getElem_replicate] at this
          rw [← this.2, positionFam_tupleFams]
          simp [positionTy])
        hl
      simpa using this
    · intro j hj U hx hu heap args hok hargs
      have hlen := ArgsT_length hargs
      apply make_fields_rule (As := [meaning G S]) (by simp [meaning_adm]) j U heap .absent
        [CallArguments.arrayStoreField] args (by simp) (by simpa using hlen.symm)
        (by simpa using hlen.symm)
        (ArgsT_values (by simp [meaning_valOnly]) hargs) hu hok (ArgsT_zip hargs)
      intro k hk V hy hrec
      refine (represents_sem hA k V _).mpr ⟨⟨?_, by simp⟩,
        fun f T hm => by simp [ReferenceConjunctions.famsOf] at hm⟩
      simpa [ReferenceConjunctions.famsOf] using hrec
  · exact hr.elim

theorem ArgStep_append {h h' : Heap} {args args' : List Tm} (rest : List Tm)
    (s : CallArguments.ArgStep h args h' args') :
    CallArguments.ArgStep h (args ++ rest) h' (args' ++ rest) := by
  induction s with
  | head hs => exact .head hs
  | tail hv _ ih => exact .tail hv ih

/-- **A variadic call.** The callee, the fixed actuals, then the further parts
run left to right; the call meets the signature's result. `Us` are trailing
fixed positions the call omits, each admitting `undefined`; a call that omits
one writes no further part. -/
theorem rest_call_safe {Ps Us : List Fam} {E R : Fam}
    (hA : ∀ A ∈ Ps, Adm A) (hAv : ∀ A ∈ Ps, ValOnly A) (hE : Adm E) (hEv : ValOnly E)
    (hUA : ∀ A ∈ Us, Adm A)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps) (parts : List (Option Fam × Tm))
    (hshort : Us = [] ∨ parts = [])
    (hS : ∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ RestCalls.Spreads S E)
    {n W heap f} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe (restsT [(Ps ++ Us, E, R)]) n W heap f)
    (hx : ∀ p ∈ xs, FutureSafe p.1 n W p.2) (hp : ∀ p ∈ parts, FutureSafe (p.1.getD E) n W p.2)
    (hu : ∀ A ∈ Us, FutureSafe A n W .undef) :
    Safe R n W heap (.call f (xs.map Prod.snd ++ parts.map RestCalls.partTerm)) := by
  apply bind (fun f => .call f (xs.map Prod.snd ++ parts.map RestCalls.partTerm)) Step.callL
    n W heap f hw hh hf
  intro j hj U hxU hu' heap' v hok hv hfun
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (fun args => .call v (args ++ parts.map RestCalls.partTerm))
    (fun hs => (CallArguments.Prepare.args hv (ArgStep_append _ hs)).step) hu' hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  rcases hshort with rfl | rfl
  · apply RestCalls.spread_parts_safe hE hEv hv parts k V heap'' args hS hv' hok'
      (ArgsT_values hAv hargs) (fun p hm => ((hp p hm).transfer hj hxU).transfer hk hy)
    intro i hi X hz hX heap3 extra hh3 hext
    have hUX : WExt (trunc i (Nat.le_trans hi hk) U) X := by
      apply WExt_trans _ hz
      simpa only [trunc_trunc] using WExt_trunc hi hy
    have hfX := (restsT_adm _).mono i _ X hUX v
      ((restsT_adm _).down_le j i (Nat.le_trans hi hk) U v hfun)
    simp only [List.append_nil] at hfX
    exact RestCalls.call_elim_rest (s := (Ps, E, R)) (by simp) hA hAv hE hEv hfX
      (ArgsT_transfer hA hargs i hi X hz) hext hX hh3
  · -- Nothing past the omitted positions: the fixed ones admit this list.
    simp only [List.map_nil, List.append_nil]
    cases k with
    | zero => trivial
    | succ k =>
      let X := trunc k (Nat.le_succ k) V
      have hX : WorldAdm X := WorldAdm_trunc _ hv'
      have hhX : HeapOk k X heap'' := HeapOk_trunc k V heap'' hok'
      have hfV := (restsT_adm _).mono (k + 1) _ V hy v
        ((restsT_adm _).down_le j (k + 1) hk U v hfun)
      have hargsX := ArgsT_transfer hA hargs k (Nat.le_succ k) X (WExt_refl _)
      have hundef : ∀ A ∈ Us, A k X .undef := by
        intro A hA'
        have := safe_value_mem rfl
          (((hu A hA').transfer hj hxU).transfer hk hy (k + 1) (Nat.le_refl _) V
            (by rw [trunc_id]; exact WExt_refl _) hv' heap'' hok')
        exact (hUA A hA').down k V _ this
      have hshortX : ArgsShort (Ps ++ Us) k X args :=
        ArgsShort_of_pad (pad := List.replicate Us.length .undef)
          (fun a hm => List.eq_of_mem_replicate hm)
          (ArgsT_append hargsX (ArgsT_undef hundef))
      obtain ⟨body, hi, hsafe⟩ := hfV.2 (Ps ++ Us, E, R) (by simp) k (Nat.lt_succ_self k) X
        (WExt_refl _) hX heap'' hhX args (ArgsT_values hAv hargsX) (Or.inl hshortX)
      exact Or.inr ⟨X, heap'', body, WExt_refl _, hX, hi.step heap'', hhX, hsafe⟩

/-- **Copying a spread.** `[...s]` reads the store `s` evaluates to where it is
written and allocates a fresh store of its elements, each at `E`. -/
theorem copy_safe {S E : Fam} (hS : RestCalls.Spreads S E) (hE : Adm E) (hEv : ValOnly E)
    {n : Nat} {W : WorldT n} {h : Heap} {s : Tm} (hw : WorldAdm W) (hh : HeapOk n W h)
    (hs : Safe S n W h s) :
    Safe (listT ⟨[], [], some E, false⟩) n W h (.arrLit [.spread s]) := by
  apply RestCalls.ctx_bind (fun t => .arrLit [.spread t])
    (fun st => .arrArg (i := 0) rfl (by intro j hj; omega) (.spreadC st)) n W h s hw hh hs
  intro j hj U hx hu heap v hok _ hv
  obtain ⟨ls, vs, rfl, hr, he⟩ := hS j U heap _ hok hv
  cases j with
  | zero => trivial
  | succ p =>
    let V := trunc p (Nat.le_succ p) U
    have hvs : ∀ e ∈ vs, E p V e := fun e hm => he e hm p (by omega)
    have hstep : Step heap (.arrLit [.spread (.arr ls)]) heap (.arrLit vs) := by
      simpa using Step.arrSpread (inits := [Tm.spread (.arr ls)]) (pre := []) (post := [])
        rfl (by simp) hr
    refine Or.inr ⟨V, heap, .arrLit vs, WExt_refl _, WorldAdm_trunc _ hu,
      hstep, HeapOk_trunc p U heap hok, ?_⟩
    apply arr_alloc_rule (As := List.replicate vs.length E)
      (by intro A hA; rw [List.eq_of_mem_replicate hA]; exact hE)
      p V heap vs (by simp) (fun v hm => hEv p V v (hvs v hm)) (WorldAdm_trunc _ hu)
      (HeapOk_trunc p U heap hok)
      (by
        intro q hq
        rw [List.eq_of_mem_replicate (List.of_mem_zip hq).1]
        exact hvs q.2 (List.of_mem_zip hq).2)
    intro k hk X hy hl
    have := listT_alloc (n := k) (W := X) (T := ⟨[], [], some E, false⟩)
      (As := List.replicate vs.length E) (base := heap.length)
      (by simp) (by simp)
      (by
        intro i A hA
        have := (List.getElem?_eq_some_iff.mp hA)
        simp only [List.getElem_replicate] at this
        rw [← this.2]
        simp [positionFam])
      hl
    simpa using this

/-- Variadic code built from a body checked with the rest array in slot 0 meets
its code contract at any later world and budget. -/
theorem restSpec_of_premise {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat}
    {W : WorldT n} {k : Nat} {b : Tm} {s : List (Ty ι) × Ty ι × Ty ι} {A : Ty ι}
    (he : EnvOk G Γ ρ n W) (hk : s.1.length = k) (harr : RestArray G A s.2.1)
    (ih : ∀ j U heap env, EnvOk G (A :: s.1 ++ Γ) env j U → WorldAdm U → HeapOk j U heap →
      Safe (meaning G s.2.2) j U heap (instantiate 0 env b))
    {j : Nat} (hj : j ≤ n) {U : WorldT j} (hx : WExt (trunc j hj W) U) :
    RestCalls.RestSpec k (s.1.map (meaning G)) (meaning G s.2.1) (meaning G s.2.2) j U
      (instantiate (k + 1) ρ b) := by
  apply RestCalls.restSpec_of_body (instantiate_scoped ρ he.1 b (k + 1)) (by simpa using hk)
    (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
    (meaning_adm G A) (fun j' U' heap extra hu' hh' hext => restArray_safe harr hu' hh' hext)
  intro j' hj' U' hx' hu' heap hh' args a hargs harr' _
  have hsc := ArgsT_scoped hargs
  have hl : args.length = k := by rw [ArgsT_length hargs]; simpa using hk
  have hbeta := instantiate_beta _ (prependArgs_scoped hsc he.1) a b 0
  rw [Nat.zero_add] at hbeta
  rw [show k + 1 = 1 + args.length by omega, instantiate_args ρ he.1 hsc b 1, hbeta]
  have hWU : WExt (trunc j' (by omega) W) U' := WExt_trans
    (by simpa only [trunc_trunc] using WExt_trunc (Nat.le_of_lt hj') hx) hx'
  exact ih j' U' heap _ (((he.transfer j' (by omega) U' hWU).prepend hargs).push harr') hu' hh'

/-- The pair of a signature and its rest-array type, by index. -/
theorem zip_getElem_mem {α β : Type} {L : List α} {As : List β} {i : Nat} (hi : i < L.length)
    (hiA : i < As.length) : (L[i], As[i]) ∈ L.zip As :=
  List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr
    ⟨List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiA⟩)

variable [DecidableEq ι]

/-- Constructor views avoid any semantic normalization assumption. -/
inductive HasTy (G : NormalGraph ι) : List (Ty ι) → Tm → Ty ι → Prop where
  | var : Γ[i]? = some A → HasTy G Γ (.var i) A
  | nul : Represents G A .nul → HasTy G Γ .nul A
  | undef : Represents G A .undef → HasTy G Γ .undef A
  | tru : Represents G A .bool → HasTy G Γ .tru A
  | fls : Represents G A .bool → HasTy G Γ .fls A
  | truLit : Represents G A (.boolLit true) → HasTy G Γ .tru A
  | flsLit : Represents G A (.boolLit false) → HasTy G Γ .fls A
  | numLit : Represents G A (.numLit b) → HasTy G Γ (.num b) A
  /-- Every number is a number, as every Boolean is a Boolean. Without this a
  literal claimed at the family rather than at its own singleton has no rule. -/
  | num : Represents G A .num → HasTy G Γ (.num b) A
  | strLit : Represents G A (.strLit s) → HasTy G Γ (.str s) A
  | str : Represents G A .str → HasTy G Γ (.str s) A
  | funE : Represents G F (.arrs L []) → (∀ p ∈ L, p.1.length = arity) →
      (∀ p ∈ L, HasTy G (p.1 ++ Γ) b p.2) → HasTy G Γ (.make (.closure arity b) .nul) F
  /-- A callable object: the same allocation as a record, with invocation code
  attached. Its bag is a record like any other, so its fields are named by the
  program rather than fixed here. -/
  | makeCallable {parts : List (String × Ty ι × Tm)} :
      Represents G F (.callable (parts.map fun p => (p.1, p.2.1)) [] L []) →
      (parts.map Prod.fst).Nodup →
      (∀ p ∈ parts, HasTy G Γ p.2.2 p.2.1) →
      (∀ p ∈ L, p.1.length = arity) →
      (∀ p ∈ L, HasTy G (p.1 ++ Γ) b p.2) →
      HasTy G Γ (.makeAt (.closure arity b) (parts.map Prod.fst)
        (parts.map fun p => p.2.2)) F
  /-- A call writes the actuals it writes. `Us` are the trailing positions the
  selected signature declares and this call omits; each admits `undefined`,
  which is the value the machine binds there. `Us = []` is the exact-arity
  call. -/
  | callCallable {Us : List (Ty ι)} : HasTy G Γ f F → Represents G F (.callable P Ps L S) →
      ((xs : List (Ty ι × Tm)).map Prod.fst ++ Us, B) ∈ L →
      (∀ p ∈ xs, HasTy G Γ p.2 p.1) → (∀ A ∈ Us, HasTy G Γ .undef A) →
      HasTy G Γ (.call f (xs.map Prod.snd)) B
  | readCallable : HasTy G Γ a F → Represents G F (.callable P Ps L S) → (f, A) ∈ P →
      HasTy G Γ (.readAt f a) A
  | writeCallable : HasTy G Γ a F → Represents G F (.callable P Ps L S) → (f, A) ∈ P →
      HasTy G Γ b A → Represents G N .nul → HasTy G Γ (.writeAt f a b) N
  | app {Us : List (Ty ι)} : HasTy G Γ f F → Represents G F (.arrs L S) →
      ((xs : List (Ty ι × Tm)).map Prod.fst ++ Us, B) ∈ L →
      (∀ p ∈ xs, HasTy G Γ p.2 p.1) → (∀ A ∈ Us, HasTy G Γ .undef A) →
      HasTy G Γ (.call f (xs.map Prod.snd)) B
  | letE : HasTy G Γ a A → HasTy G (A :: Γ) b B → HasTy G Γ (.letE a b) B
  /-- **Allocation.** One object, one fresh location per named field. The field
  names are distinct, which is what makes the object a map from them. -/
  | alloc {parts : List (String × Ty ι × Tm)} : (parts.map Prod.fst).Nodup →
      (∀ p ∈ parts, HasTy G Γ p.2.2 p.2.1) →
      Represents G Ref (.refs (parts.map fun p => (p.1, p.2.1)) [] []) →
      HasTy G Γ (.makeAt .absent (parts.map Prod.fst) (parts.map fun p => p.2.2)) Ref
  | read : HasTy G Γ a Ref → Represents G Ref (.refs fs [] vs) → (f, A) ∈ fs →
      HasTy G Γ (.readAt f a) A
  /-- A view field reads at its bound: a capability, never a write permission. -/
  | readView : HasTy G Γ a Ref → Represents G Ref (.refs fs [] vs) → (f, A) ∈ vs →
      HasTy G Γ (.readAt f a) A
  | write : HasTy G Γ a Ref → Represents G Ref (.refs fs [] vs) → (f, A) ∈ fs →
      HasTy G Γ b A → Represents G N .nul → HasTy G Γ (.writeAt f a b) N
  /-- Arithmetic needs two operands the number test answers for, and yields
  the number family: no singleton, since the result's bits are not typed. -/
  | arith : HasTy G Γ a A → Answers G A .isNum true → HasTy G Γ b B → Answers G B .isNum true →
      Represents G N .num → HasTy G Γ (.arith op a b) N
  /-- A literal allocates a store: one fresh location per element, each
  under the position's contract of the tuple the store is claimed at, whose
  bounds the element count respects. -/
  | arrLit {Γ : List (Ty ι)} {L : Ty ι} {T : Tuple (Ty ι)} {xs : List (Ty ι × Tm)} :
      Represents G L (.list T []) → T.required.length ≤ xs.length →
      (T.rest = none → xs.length ≤ T.required.length + T.optional.length) →
      (∀ p ∈ xs.zipIdx, positionTy T p.2 = some p.1.1) →
      (∀ p ∈ xs, HasTy G Γ p.2 p.1) → HasTy G Γ (.arrLit (xs.map Prod.snd)) L
  /-- A required position, named by a literal index, reads at its contract. -/
  | elem {Γ : List (Ty ι)} {a i : Tm} {L I A : Ty ι} {T : Tuple (Ty ι)} {b : UInt64} {k : Nat} :
      HasTy G Γ a L → Represents G L (.list T []) → HasTy G Γ i I → Represents G I (.numLit b) →
      indexOfBits b = some k → T.required[k]? = some A → HasTy G Γ (.elemAt a i) A
  /-- An optional or rest position, named by a literal index, reads at its
  contract or `undefined`: it may be a hole or past the end. -/
  | elemOpt {Γ : List (Ty ι)} {a i : Tm} {L I A U : Ty ι} {T : Tuple (Ty ι)} {b : UInt64} {k : Nat} :
      HasTy G Γ a L → Represents G L (.list T []) → HasTy G Γ i I → Represents G I (.numLit b) →
      indexOfBits b = some k → T.required[k]? = none → positionTy T k = some A →
      Represents G U .undef → HasTy G Γ (.elemAt a i) (A ++ U)
  /-- Any numeric index into a homogeneous array reads an element or
  `undefined`; no index is in bounds by type alone. -/
  | elemAny {Γ : List (Ty ι)} {a i : Tm} {L I E U : Ty ι} :
      HasTy G Γ a L → Represents G L (.list ⟨[], [], some E, false⟩ []) → HasTy G Γ i I →
      Answers G I .isNum true → Represents G U .undef → HasTy G Γ (.elemAt a i) (E ++ U)
  /-- A write at a literal index into a position the contract names keeps the
  contract: into the element's location, or a fresh one the store records. -/
  | setElem {Γ : List (Ty ι)} {a i v : Tm} {L I A : Ty ι} {T : Tuple (Ty ι)} {b : UInt64} {k : Nat} :
      HasTy G Γ a L → Represents G L (.list T []) → HasTy G Γ i I → Represents G I (.numLit b) →
      indexOfBits b = some k → positionTy T k = some A → T.readonly = false → HasTy G Γ v A →
      HasTy G Γ (.setElem a i v) L
  | len {Γ : List (Ty ι)} {a : Tm} {L N : Ty ι} {T : Tuple (Ty ι)} :
      HasTy G Γ a L → Represents G L (.list T []) → Represents G N .num → HasTy G Γ (.lenOf a) N
  /-- A tag test whose answer the operand's type does not settle is still a
  Boolean: its type holds both literals. -/
  | test : HasTy G Γ a A → (.boolLit true) ∈ expand G B → (.boolLit false) ∈ expand G B →
      HasTy G Γ (.test k a) B
  | ifBool : HasTy G Γ c C → Answers G C .isBool true →
      HasTy G Γ t A → HasTy G Γ e A → HasTy G Γ (.ite c t e) A
  /-- The condition still evaluates; its singleton type selects the reachable arm. -/
  | ifKnown : HasTy G Γ c C → Represents G C (.boolLit q) →
      HasTy G Γ (if q then t else e) A → HasTy G Γ (.ite c t e) A
  | ifBoolVar : Γ[i]? = some C → Answers G C .isBool true →
      Represents G T (.boolLit true) → Represents G F (.boolLit false) →
      HasTy G (Γ.set i T) t A → HasTy G (Γ.set i F) e A →
      HasTy G Γ (.ite (.var i) t e) A
  | ifTag : Γ[i]? = some A → Answers G A tag q →
      (q = true → HasTy G Γ u B) → (q = false → HasTy G Γ e B) →
      HasTy G Γ (.ite (.test tag (.var i)) u e) B
  /-- Eliminate a finite union in one immutable environment slot. Every member
  must establish the same term and result, without changing other bindings. -/
  | unionVar : Γ[i]? = some C →
      (∀ a ∈ C, HasTy G (Γ.set i [a]) t A) → HasTy G Γ t A
  /-- **A variadic function.** Each signature's body is checked with the
fixed parameters and, in slot 0, an array whose type holds any number of
elements at the signature's element type. -/
  | funRest {Γ : List (Ty ι)} {F : Ty ι} {L : List (List (Ty ι) × Ty ι × Ty ι)}
      {As : List (Ty ι)} {n : Nat} {b : Tm} :
      Represents G F (.arrs [] L) → L.length = As.length →
      (∀ p ∈ L.zip As, p.1.1.length = n ∧ RestArray G p.2 p.1.2.1) →
      (∀ p ∈ L.zip As, HasTy G (p.2 :: p.1.1 ++ Γ) b p.1.2.2) →
      HasTy G Γ (.make (.variadic n b) .nul) F
  /-- **A variadic callable object.** The bag is allocated as a record's is,
  and the code is variadic: each signature's body is checked as `funRest`
  checks it. -/
  | makeCallableRest {Γ : List (Ty ι)} {F : Ty ι} {parts : List (String × Ty ι × Tm)}
      {L : List (List (Ty ι) × Ty ι × Ty ι)} {As : List (Ty ι)} {n : Nat} {b : Tm} :
      Represents G F (.callable (parts.map fun p => (p.1, p.2.1)) [] [] L) →
      (parts.map Prod.fst).Nodup → (∀ p ∈ parts, HasTy G Γ p.2.2 p.2.1) →
      L.length = As.length →
      (∀ p ∈ L.zip As, p.1.1.length = n ∧ RestArray G p.2 p.1.2.1) →
      (∀ p ∈ L.zip As, HasTy G (p.2 :: p.1.1 ++ Γ) b p.1.2.2) →
      HasTy G Γ (.makeAt (.variadic n b) (parts.map Prod.fst) (parts.map fun p => p.2.2)) F
  /-- **A copy of a spread.** `[...s]` allocates a fresh store holding the
  elements of the store `s` evaluates to, read where it is written. -/
  | arrCopy {Γ : List (Ty ι)} {s : Tm} {S T E : Ty ι} :
      HasTy G Γ s S → SpreadsInto G S E → Represents G T (.list ⟨[], [], some E, false⟩ []) →
      HasTy G Γ (.arrLit [.spread s]) T
  /-- **A variadic call.** The fixed actuals meet the selected signature's
  parameters, less trailing ones `Us` the call omits, each admitting
  `undefined`; each further part is an actual at its element type or a spread
  of a store whose elements are, and a call that omits a fixed position writes
  none. The signature may be a function's or a callable object's. -/
  | callRest {Γ : List (Ty ι)} {f : Tm} {F : Ty ι}
      {xs : List (Ty ι × Tm)} {Us : List (Ty ι)} {E B : Ty ι} {parts : List (Bool × Ty ι × Tm)} :
      HasTy G Γ f F → (xs.map Prod.fst ++ Us, E, B) ∈ restSigs G F →
      (∀ p ∈ xs, HasTy G Γ p.2 p.1) → (∀ A ∈ Us, HasTy G Γ .undef A) → (Us = [] ∨ parts = []) →
      (∀ p ∈ parts, HasTy G Γ p.2.2 p.2.1) →
      (∀ p ∈ parts, p.1 = false → p.2.1 = E) →
      (∀ p ∈ parts, p.1 = true → SpreadsInto G p.2.1 E) →
      HasTy G Γ (.call f (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2))) B
  | sub : HasTy G Γ t A → PositiveCertificates.check G A B cert = true → HasTy G Γ t B

/-- Every derivation is safe in every admissible world and satisfying heap. -/
theorem HasTy.sound {G : NormalGraph ι} {Γ t A} (ht : HasTy G Γ t A) :
    ∀ n W h ρ, EnvOk G Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaning G A) n W h (instantiate 0 ρ t) := by
  induction ht with
  | var hi =>
    intro n W h ρ he hw hh
    simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    exact value_safe _ _ _ _ _ (meaning_value (he.2 _ _ hi)).1 (he.2 _ _ hi)
  | nul hr | undef hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_sem hr n W _).mpr rfl)
  | tru hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_sem hr n W _).mpr (Or.inl rfl))
  | fls hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_sem hr n W _).mpr (Or.inr rfl))
  | truLit hr | flsLit hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_sem hr n W _).mpr rfl)
  | numLit hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_sem hr n W _).mpr rfl)
  | @num _ _ b hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_sem hr n W _).mpr ⟨b, rfl⟩)
  | strLit hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_sem hr n W _).mpr rfl)
  | @str _ _ s hr =>
    intro n W h ρ he hw hh
    exact value_safe _ _ _ _ _ rfl ((represents_sem hr n W _).mpr ⟨s, rfl⟩)
  | @funE F L arity Γ b hr hlen hb ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, Nat.zero_add]
    have hcode := invocation_of_body he hlen (fun p hp => ih p hp)
    have hs := make_callable_rule nulT_adm arity n W h _ .nul hcode rfl hw hh rfl
    exact Safe_mono n (fun k _ U v hv => (represents_sem hr k U v).mpr
      ⟨hv.2, hv.2.1, by simp⟩) W h _ hs
  | @makeCallable F L Γ arity b parts hr hnd hp hlen hb ih ihb =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def, Nat.zero_add]
    have hcode := invocation_of_body he hlen (fun p hp => ihb p hp)
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt (.closure arity (instantiate arity ρ b)) (parts.map Prod.fst) args)
      (fun hs => CallArguments.Step.makeArgs hs) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.fst
        = parts.map fun p => meaning G p.2.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlenA := ArgsT_length hargs
    have hc : InvocationSpec arity (L.map fun p => (p.1.map (meaning G),meaning G p.2))
        j U (instantiate arity ρ b) :=
      (codeCallsT_code_iff _ arity [] _ j U).mp ((codeCallsT_adm _).mono j _ U hx _
        ((codeCallsT_adm _).down_le n j hj W _ ((codeCallsT_code_iff _ arity [] _ n W).mpr hcode)))
    have hs := make_callable_fields_rule
      (P := parts.map fun p => meaning G p.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      arity j U heap _ args _ hnd (by simpa using hlenA.symm) (by simpa using hlenA.symm)
      hc
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    apply Safe_mono j (fun k _ V v hv => (represents_sem hr k V v).mpr
      ⟨⟨⟨?_, by simp⟩, hv.2⟩, hv.2.1, by simp⟩) U heap _ hs
    case _ =>
      have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
          = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
        simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
      rw [hfam]
      exact hv.1
  | @callCallable Γ f F P Ps L S xs B Us hf hr hp ha hu ihf iha ihu =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := call_safe_short (B := meaning G B) (f := instantiate 0 ρ f)
      (xs.map fun p => (meaning G p.1,instantiate 0 ρ p.2)) (Us.map (meaning G))
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_adm G q.1)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_valOnly G q.1)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q)
      hw hh
    apply (by simpa only [List.map_map,Function.comp_def] using hs)
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      simpa only [List.map_map,Function.comp_def,List.map_append] using
        callsT_select (((represents_sem hr k U v).mp hv).1.2)
          (List.mem_map.mpr ⟨(xs.map Prod.fst ++ Us,B), hp,
            by simp [List.map_append, List.map_map, Function.comp_def]⟩)
    · intro p hp'
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
      intro j hj U hx hu' heap hok
      exact iha q hq j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro A hA
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA
      intro j hj U hx hu' heap hok
      exact ihu q hq j U heap ρ (he.transfer j hj U hx) hu' hok
  | @readCallable Γ a Ref P Ps L S f A ha hr hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    exact bag_read (meaning_valOnly G A) (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
      ((represents_sem hr j U v).mp ha').1.1.1 hu hok
  | @writeCallable Γ a Ref P Ps L S f A b N ha hr hm hb hn iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .writeAt f a (instantiate 0 ρ b)) Step.writeC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.writeAt f av) (Step.writeC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G Ref).mono k _ V hy av ((meaning_adm G Ref).down_le j k hk U av ha')
    apply Safe_mono k (fun i _ X v hval => (represents_sem hn i X v).mpr hval)
    exact bag_write (meaning_adm G A) (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
      ((represents_sem hr k V av).mp ha'').1.1.1 hb' hbval hv hok'
  | @app Γ f F L S xs B Us hf hr hp ha hu ihf iha ihu =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := call_safe_short (B := meaning G B) (f := instantiate 0 ρ f)
      (xs.map fun p => (meaning G p.1,instantiate 0 ρ p.2)) (Us.map (meaning G))
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_adm G q.1)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_valOnly G q.1)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q)
      hw hh
    apply (by simpa only [List.map_map,Function.comp_def] using hs)
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      simpa only [List.map_map,Function.comp_def,List.map_append] using
        callsT_select ((represents_sem hr k U v).mp hv).1
          (List.mem_map.mpr ⟨(xs.map Prod.fst ++ Us,B), hp,
            by simp [List.map_append, List.map_map, Function.comp_def]⟩)
    · intro p hp'
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
      intro j hj U hx hu' heap hok
      exact iha q hq j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro A hA
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA
      intro j hj U hx hu' heap hok
      exact ihu q hq j U heap ρ (he.transfer j hj U hx) hu' hok
  | @letE Γ a A b B ha hb iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .letE a (instantiate 1 ρ b)) Step.letC n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    cases j with
    | zero => trivial
    | succ k =>
      apply let_rule _ _ hav k U heap hu hok
      rw [instantiate_beta ρ he.1]
      have he' := ((he.transfer (k+1) hj U hx).push ha').transfer k (Nat.le_succ k)
        (trunc k (Nat.le_succ k) U) (WExt_refl _)
      exact ihb k _ heap (push av ρ) he' (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
  | @alloc Γ Ref parts hnd hp hr ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt .absent (parts.map Prod.fst) args)
      (fun hs => CallArguments.Step.makeArgs hs) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.fst
        = parts.map fun p => meaning G p.2.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlen := ArgsT_length hargs
    apply make_fields_rule
      (As := parts.map fun p => meaning G p.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      j U heap .absent _ args hnd (by simpa using hlen.symm) (by simpa using hlen.symm)
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    intro k hk V hy hrec
    refine (represents_sem hr k V _).mpr ⟨⟨?_, by simp⟩, fun f T hm => by simp [ReferenceConjunctions.famsOf] at hm⟩
    have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
        = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
    rw [hfam]
    exact hrec
  | @read Γ a Ref fs vs f A ha hr hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) ((represents_sem hr j U v).mp ha').1.1
    exact read_rule (meaning_valOnly G A) j U heap l hu hok hf hl hag
  | @readView Γ a Ref fs vs f A ha hr hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ :=
      viewT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) ((represents_sem hr j U v).mp ha').2
    exact read_view_rule (meaning_valOnly G A) j U heap l hu hok hf hl hag
  | @arrLit Γ L T xs hr hreq hbound hpos hx ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hmap : (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.snd
        = xs.map fun x => instantiate 0 ρ x.2 := by simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.1)
      (fun args => .arrLit args) (fun hs => CallArguments.Step.arrArgs hs) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.fst
        = xs.map fun p => meaning G p.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlen := ArgsT_length hargs
    apply arr_alloc_rule (As := xs.map fun p => meaning G p.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.1)
      j U heap args hlen.symm
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    intro k hk V hy hl
    refine (represents_sem hr k V _).mpr ⟨?_, by simp⟩
    rw [hlen]
    apply listT_alloc
    · simpa [tupleFams] using hreq
    · intro hn
      simp only [tupleFams, List.length_map, Option.map_eq_none_iff] at hn ⊢
      exact hbound hn
    · intro i A hA
      rw [positionFam_tupleFams]
      simp only [List.getElem?_map, Option.map_eq_some_iff] at hA
      obtain ⟨p, hp, rfl⟩ := hA
      have := hpos (p, i) (by simpa [List.mem_zipIdx_iff_getElem?] using hp)
      simp [this]
    · exact hl
  | @elem Γ a i L I A T b k ha hr hi hI hk hA iha ihi =>
    intro n W h ρ he hw hh
    apply bind (fun a => .elemAt a (instantiate 0 ρ i)) Step.elemC1 n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.elemAt av) (Step.elemC2 hav) j U heap _ hu hok
      (ihi j U heap ρ (he.transfer j hj U hx) hu hok)
    intro m hm V hy hv heap' iv hok' hival hi'
    have ha'' := (meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U av ha')
    obtain ⟨ls, rfl, -, -, hreq, -, -⟩ := ((represents_sem hr m V av).mp ha'').1
    simp only [tupleFams, List.length_map, List.getElem?_map] at hreq
    have hb : iv = .num b := (represents_sem hI m V iv).mp hi'
    subst hb
    obtain ⟨l, c, hl, hw', hag⟩ := hreq k (meaning G A) (by simp [hA])
    exact elem_read_rule (meaning_valOnly G A) m V heap' l hv hok' (by simp [elemLoc, hk, hl]) hw'
      (fun j hj U u => (hag j hj U u).1)
  | @elemOpt Γ a i L I A U T b k ha hr hi hI hk hnone hA hU iha ihi =>
    intro n W h ρ he hw hh
    apply bind (fun a => .elemAt a (instantiate 0 ρ i)) Step.elemC1 n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U' hx hu heap av hok hav ha'
    apply bind (.elemAt av) (Step.elemC2 hav) j U' heap _ hu hok
      (ihi j U' heap ρ (he.transfer j hj U' hx) hu hok)
    intro m hm V hy hv heap' iv hok' hival hi'
    have ha'' := (meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U' av ha')
    obtain ⟨ls, rfl, -, -, -, hopt, hrest⟩ := ((represents_sem hr m V av).mp ha'').1
    simp only [tupleFams, List.length_map, List.getElem?_map] at hopt hrest
    have hb : iv = .num b := (represents_sem hI m V iv).mp hi'
    subst hb
    have hundef : ∀ m' (U'' : WorldT m'), meaning G (A ++ U) m' U'' .undef := fun m' U'' =>
      (meaning_append G A U m' U'' _).mpr (Or.inr ((represents_sem hU m' U'' _).mpr rfl))
    cases hloc : elemLoc ls b with
    | none => exact elem_absent_rule m V heap' hv hok' hloc hundef
    | some l =>
      have hl : ls[k]? = some (some l) := by
        simp only [elemLoc, hk, Option.bind_some] at hloc
        cases hls : ls[k]? with
        | none => simp [hls] at hloc
        | some o => cases o with
          | none => simp [hls] at hloc
          | some l' => simp [hls] at hloc; subst hloc; rfl
      have hpos := hA
      simp only [positionTy, hnone] at hpos
      have key : ∃ c : Ctr m, lookup V l = some c ∧
          ∀ (j : Nat) (hj : j < m) (W' : WorldT j) (u : Val), SlotContract T.readonly (c j hj W' u) (meaning G A j W' u) := by
        split at hpos
        · rename_i hopt'
          cases hpos
          have hk' : T.required.length + (k - T.required.length) = k := by
            have := (List.getElem?_eq_none_iff.mp hnone); omega
          exact hopt (k - T.required.length) (meaning G A) l
            (by simp [hopt']) (by rw [hk']; exact hl)
        · split at hpos
          · rename_i hge
            obtain ⟨E, c, hE, hw', hag⟩ := hrest k l hge hl
            simp only [Option.map_eq_some_iff] at hE
            obtain ⟨e, he, rfl⟩ := hE
            rw [he] at hpos
            cases hpos
            exact ⟨c, hw', hag⟩
          · cases hpos
      obtain ⟨c, hw', hag⟩ := key
      apply Safe_mono m (fun m' _ U'' u hu => (meaning_append G A U m' U'' u).mpr (Or.inl hu))
      exact elem_read_rule (meaning_valOnly G A) m V heap' l hv hok' hloc hw' (fun j hj U u => (hag j hj U u).1)
  | @elemAny Γ a i L I E U ha hr hi hq hU iha ihi =>
    intro n W h ρ he hw hh
    apply bind (fun a => .elemAt a (instantiate 0 ρ i)) Step.elemC1 n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U' hx hu heap av hok hav ha'
    apply bind (.elemAt av) (Step.elemC2 hav) j U' heap _ hu hok
      (ihi j U' heap ρ (he.transfer j hj U' hx) hu hok)
    intro m hm V hy hv heap' iv hok' hival hi'
    have ha'' := (meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U' av ha')
    obtain ⟨ls, rfl, -, -, -, -, hrest⟩ := ((represents_sem hr m V av).mp ha'').1
    have hnum := answers_sound hq hi'
    obtain ⟨b, rfl⟩ : ∃ b, iv = .num b := by
      cases iv <;> simp [tagHolds] at hnum; exact ⟨_, rfl⟩
    have hundef : ∀ m' (U'' : WorldT m'), meaning G (E ++ U) m' U'' .undef := fun m' U'' =>
      (meaning_append G E U m' U'' _).mpr (Or.inr ((represents_sem hU m' U'' _).mpr rfl))
    cases hloc : elemLoc ls b with
    | none => exact elem_absent_rule m V heap' hv hok' hloc hundef
    | some l =>
      obtain ⟨k, hk, hl⟩ : ∃ k, indexOfBits b = some k ∧ ls[k]? = some (some l) := by
        simp only [elemLoc] at hloc
        cases hkb : indexOfBits b with
        | none => simp [hkb] at hloc
        | some k =>
          simp only [hkb, Option.bind_some] at hloc
          cases hls : ls[k]? with
          | none => simp [hls] at hloc
          | some o => cases o with
            | none => simp [hls] at hloc
            | some l' => simp [hls] at hloc; subst hloc; exact ⟨k, rfl, hls⟩
      obtain ⟨E', c, hE, hw', hag⟩ := hrest k l (by simp [tupleFams]) hl
      simp only [tupleFams, List.map_nil, Option.map_some, Option.some.injEq] at hE
      subst hE
      apply Safe_mono m (fun m' _ U'' u hu => (meaning_append G E U m' U'' u).mpr (Or.inl hu))
      exact elem_read_rule (meaning_valOnly G E) m V heap' l hv hok' hloc hw' (fun j hj U u => (hag j hj U u).1)
  | @setElem Γ a i v L I A T b k ha hr hi hI hk hA hro hv iha ihi ihv =>
    intro n W h ρ he hw hh
    apply bind (fun a => .setElem a (instantiate 0 ρ i) (instantiate 0 ρ v)) Step.setC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (fun i => .setElem av i (instantiate 0 ρ v)) (Step.setC2 hav) j U heap _ hu hok
      (ihi j U heap ρ (he.transfer j hj U hx) hu hok)
    intro m hm V hy hvw heap' iv hok' hival hi'
    apply bind (.setElem av iv) (Step.setC3 hav hival) m V heap' _ hvw hok'
      (ihv m V heap' ρ ((he.transfer j hj U hx).transfer m hm V hy) hvw hok')
    intro p hp X hz hxw heap'' vv hok'' hvval hv'
    have hav' := (meaning_adm G L).mono p _ X hz av ((meaning_adm G L).down_le m p hp V av
      ((meaning_adm G L).mono m _ V hy av ((meaning_adm G L).down_le j m hm U av ha')))
    have hlist := ((represents_sem hr p X av).mp hav').1
    obtain ⟨ls, rfl, -, -, hreq, hopt, hrest⟩ := hlist
    simp only [tupleFams, List.length_map, List.getElem?_map] at hreq hopt hrest
    have rwContract : ∀ P Q : Prop, SlotContract T.readonly P Q ↔ (P ↔ Q) := by
      intro P Q; simp [SlotContract, hro, iff_def]
    simp only [rwContract] at hreq hopt hrest
    have hb : iv = .num b := (meaning_adm G I).mono p _ X hz iv ((meaning_adm G I).down_le m p hp V iv hi')
      |> (represents_sem hI p X iv).mp
    subst hb
    have hkeep : ∀ j' (hj' : j' < p) (U' : WorldT j'), WExt (trunc j' (Nat.le_of_lt hj') X) U' →
        meaning G L j' U' (.arr ls) := fun j' hj' U' hx' =>
      (meaning_adm G L).mono j' _ U' hx' _ ((meaning_adm G L).down_le p j' (by omega) X _ hav')
    cases hloc : elemLoc ls b with
    | some l =>
      have hl : ls[k]? = some (some l) := by
        simp only [elemLoc, hk, Option.bind_some] at hloc
        cases hls : ls[k]? with
        | none => simp [hls] at hloc
        | some o => cases o with
          | none => simp [hls] at hloc
          | some l' => simp [hls] at hloc; subst hloc; rfl
      have key : ∃ c : Ctr p, lookup X l = some c ∧
          ∀ (j : Nat) (hj : j < p) (W' : WorldT j) (u : Val), c j hj W' u ↔ meaning G A j W' u := by
        have hpos := hA
        simp only [positionTy] at hpos
        split at hpos
        · rename_i hreq'
          cases hpos
          obtain ⟨l', c, hl', hw', hag⟩ := hreq k (meaning G A) (by simp [hreq'])
          cases Option.some.inj (Option.some.inj (hl.symm.trans hl'))
          exact ⟨c, hw', hag⟩
        · rename_i hnone
          split at hpos
          · rename_i hopt'
            cases hpos
            have hk' : T.required.length + (k - T.required.length) = k := by
              have := (List.getElem?_eq_none_iff.mp hnone); omega
            exact hopt (k - T.required.length) (meaning G A) l
              (by simp [hopt']) (by rw [hk']; exact hl)
          · split at hpos
            · rename_i hge
              obtain ⟨E, c, hE, hw', hag⟩ := hrest k l hge hl
              simp only [Option.map_eq_some_iff] at hE
              obtain ⟨e, he, rfl⟩ := hE
              rw [he] at hpos
              cases hpos
              exact ⟨c, hw', hag⟩
            · cases hpos
      obtain ⟨c, hw', hag⟩ := key
      exact set_present_rule (meaning_adm G A) p X heap'' l vv hvval hxw hok'' hloc hw' hag hv' hkeep
    | none =>
      apply set_grow_rule (meaning_adm G A) p X heap'' vv hvval hxw hok'' hk hloc hv'
      intro j' hj' U' hx' hm'
      refine (represents_sem hr j' U' _).mpr ⟨?_, by simp⟩
      have hold := ((represents_sem hr j' U' _).mp (hkeep j' hj' U' hx')).1
      apply listT_grow hold
      · rw [positionFam_tupleFams, hA]; rfl
      · simp only [elemLoc, hk, Option.bind_some] at hloc; exact hloc
      · exact hm'
  | @len Γ a L N T ha hr hn ih =>
    intro n W h ρ he hw hh
    apply bind Tm.lenOf Step.lenC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    obtain ⟨ls, rfl, -⟩ := ((represents_sem hr j U av).mp ha').1
    exact len_rule j U heap hu hok (fun m U' => (represents_sem hn m U' _).mpr ⟨_, rfl⟩)
  | @test Γ a A B k ha ht hf ih =>
    intro n W h ρ he hw hh
    apply bind (.test k) Step.testC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    cases j with
    | zero => trivial
    | succ p =>
      apply Safe_mono (p+1) (fun m _ X v hv => ?_) U heap _ (test_value_safe k av hav p U heap hu hok)
      rcases hv with rfl | rfl
      · exact (expand_sem G B m X _).mpr (by simp only [semList, setSem]; exact ⟨_, ht, rfl⟩)
      · exact (expand_sem G B m X _).mpr (by simp only [semList, setSem]; exact ⟨_, hf, rfl⟩)
  | @arith Γ a A b B N op ha hqa hb hqb hn iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .arith op a (instantiate 0 ρ b)) Step.arithC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.arith op av) (Step.arithC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G A).mono k _ V hy av ((meaning_adm G A).down_le j k hk U av ha')
    have hna := answers_sound hqa ha''
    have hnb := answers_sound hqb hb'
    obtain ⟨x, rfl⟩ : ∃ x, av = .num x := by
      cases av <;> simp [tagHolds] at hna; exact ⟨_, rfl⟩
    obtain ⟨y, rfl⟩ : ∃ y, bv = .num y := by
      cases bv <;> simp [tagHolds] at hnb; exact ⟨_, rfl⟩
    exact arith_value_safe op x y k V heap' hv hok'
      (fun m U => (represents_sem hn m U _).mpr ⟨_, rfl⟩)
  | @write Γ a Ref fs vs f A b N ha hr hm hb hn iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .writeAt f a (instantiate 0 ρ b)) Step.writeC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.writeAt f av) (Step.writeC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G Ref).mono k _ V hy av ((meaning_adm G Ref).down_le j k hk U av ha')
    obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) ((represents_sem hr k V av).mp ha'').1.1
    apply Safe_mono k (fun i _ X v hval => (represents_sem hn i X v).mpr hval)
    exact write_rule (meaning_adm G A) k V heap' l bv hbval hv hok' hf hl hag hb'
  | @ifBool Γ c C t A e hc hbool ht he ihc iht ihe =>
    intro n W h ρ henv hw hh
    apply bind (fun c => .ite c (instantiate 0 ρ t) (instantiate 0 ρ e)) Step.iteC
      n W h _ hw hh (ihc n W h ρ henv hw hh)
    intro j hj U hx hu heap v hok hv ha
    have hb := answers_sound hbool ha
    have shape : v = .tru ∨ v = .fls := by cases v <;> simp_all [tagHolds]
    rcases shape with rfl | rfl
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ t,
          WExt_refl _, WorldAdm_trunc _ hu, .iteT, HeapOk_trunc k U heap hok, ?_⟩
        exact iht k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ e,
          WExt_refl _, WorldAdm_trunc _ hu, .iteF, HeapOk_trunc k U heap hok, ?_⟩
        exact ihe k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
  | @ifKnown Γ c C q t e A hc hq ht ihc iht =>
    intro n W h ρ henv hw hh
    apply bind (fun c => .ite c (instantiate 0 ρ t) (instantiate 0 ρ e)) Step.iteC
      n W h _ hw hh (ihc n W h ρ henv hw hh)
    intro j hj U hx hu heap v hok hv ha
    have hvalue := (represents_sem hq j U v).mp ha
    cases q <;> simp only [sem] at hvalue <;> subst v
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ e,
          WExt_refl _, WorldAdm_trunc _ hu, .iteF, HeapOk_trunc k U heap hok, ?_⟩
        exact iht k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
    · cases j with
      | zero => trivial
      | succ k =>
        refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ t,
          WExt_refl _, WorldAdm_trunc _ hu, .iteT, HeapOk_trunc k U heap hok, ?_⟩
        exact iht k _ heap ρ ((henv.transfer (k+1) hj U hx).transfer k (Nat.le_succ k)
          _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
  | @ifBoolVar Γ i C T F t A e hi hb hT hF ht he iht ihe =>
    intro n W h ρ henv hw hh
    have hshape := answers_sound hb (henv.2 i C hi)
    have shape : ρ i = .tru ∨ ρ i = .fls := by
      cases hv : ρ i <;> simp_all [tagHolds]
    simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ k =>
      rcases shape with hv | hv
      · have refined := henv.refine hi ((represents_sem hT (k+1) W (ρ i)).mpr (by simpa [hv, sem, boolT]))
        rw [hv]
        refine Or.inr ⟨trunc k (Nat.le_succ k) W,h,instantiate 0 ρ t,WExt_refl _,
          WorldAdm_trunc _ hw,.iteT,HeapOk_trunc k W h hh,?_⟩
        exact iht k _ h ρ (refined.transfer k (Nat.le_succ k) _ (WExt_refl _))
          (WorldAdm_trunc _ hw) (HeapOk_trunc k W h hh)
      · have refined := henv.refine hi ((represents_sem hF (k+1) W (ρ i)).mpr (by simpa [hv, sem, boolT]))
        rw [hv]
        refine Or.inr ⟨trunc k (Nat.le_succ k) W,h,instantiate 0 ρ e,WExt_refl _,
          WorldAdm_trunc _ hw,.iteF,HeapOk_trunc k W h hh,?_⟩
        exact ihe k _ h ρ (refined.transfer k (Nat.le_succ k) _ (WExt_refl _))
          (WorldAdm_trunc _ hw) (HeapOk_trunc k W h hh)
  | @ifTag Γ i A tag q u B e hi hq ht he iht ihe =>
    intro n W h ρ henv hw hh
    have hval := (meaning_value (henv.2 i A hi)).1
    have htag := answers_sound hq (henv.2 i A hi)
    simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ n =>
      cases n with
      | zero =>
        exact Or.inr ⟨trunc 0 (by omega) W, h, _, WExt_refl _, WorldAdm_trunc _ hw,
          .iteC (.testV hval), HeapOk_trunc 0 W h hh, trivial⟩
      | succ k =>
        apply ite_test_rule tag (ρ i) hval _ _ k W h hw hh
        · intro ht
          exact iht (htag.symm.trans ht) k _ h ρ
            (henv.transfer k (by omega) _ (WExt_refl _))
            (WorldAdm_trunc _ hw) (by simpa only [trunc_trunc] using HeapOk_trunc k _ h (HeapOk_trunc (k+1) W h hh))
        · intro he
          exact ihe (htag.symm.trans he) k _ h ρ
            (henv.transfer k (by omega) _ (WExt_refl _))
            (WorldAdm_trunc _ hw) (by simpa only [trunc_trunc] using HeapOk_trunc k _ h (HeapOk_trunc (k+1) W h hh))
  | @unionVar Γ i C t A hi ht ih =>
    intro n W h ρ henv hw hh
    obtain ⟨a, ha, hv⟩ := henv.2 i C hi
    apply ih a ha n W h ρ (henv.refine hi ?_) hw hh
    exact ⟨a, by simp, hv⟩
  | @funRest Γ F L As k b hr hlen hsig hb ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_cons, List.map_nil, Nat.zero_add]
    apply make_rule nulT_adm n W h (.variadic k _) .nul rfl hw hh rfl
    intro j hj U hx _
    have hinv : Invocable (.obj h.length (.variadic k (instantiate (k + 1) ρ b))) :=
      ⟨_, _, rfl, by simp, by simpa [Scoped] using instantiate_scoped ρ he.1 b (k + 1)⟩
    refine (represents_sem hr j U _).mpr ⟨⟨hinv, by simp⟩, hinv, ?_⟩
    intro s' hs'
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    have hiA : i < As.length := hlen ▸ hi
    have hp : (L[i], As[i]) ∈ L.zip As :=
      List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr
        ⟨List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiA⟩)
    obtain ⟨hk, harr⟩ := hsig _ hp
    exact (RestCalls.restsT_of_restSpec _ (restSpec_of_premise he hk harr (ih _ hp)
      (Nat.le_of_lt hj) hx)).2 _ (List.mem_singleton_self _)
  | @makeCallableRest Γ F parts L As k b hr hnd hp hlen hsig hb ih ihb =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def, Nat.zero_add]
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt (.variadic k (instantiate (k + 1) ρ b)) (parts.map Prod.fst) args)
      (fun hs => CallArguments.Step.makeArgs hs) hw hh
      (by
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        intro j hj U hx hu heap hok
        exact ih r hr' j U heap ρ (he.transfer j hj U hx) hu hok)
    intro j hj U hx hu heap args hok hargs
    have hAs : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.fst
        = parts.map fun p => meaning G p.2.1 := by simp [List.map_map, Function.comp_def]
    rw [hAs] at hargs
    have hlenA := ArgsT_length hargs
    apply make_fields_rule (As := parts.map fun p => meaning G p.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      j U heap (.variadic k _) _ args hnd (by simpa using hlenA.symm) (by simpa using hlenA.symm)
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    intro k' hk' V hy hrec
    have hinv : Invocable (.objAt (slots heap.length (parts.map Prod.fst))
        (.variadic k (instantiate (k + 1) ρ b))) :=
      ⟨_, _, rfl, by simp, by simpa [Scoped] using instantiate_scoped ρ he.1 b (k + 1)⟩
    have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
        = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
    refine (represents_sem hr k' V _).mpr
      ⟨⟨⟨⟨_, _, rfl, rfl, by rw [hfam]; exact hrec⟩, by simp⟩, hinv, by simp⟩, hinv, ?_⟩
    intro s' hs'
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hs'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    have hp' := zip_getElem_mem hi (hlen ▸ hi)
    obtain ⟨hk, harr⟩ := hsig _ hp'
    have hWV : WExt (trunc k' (by omega) W) V := by
      apply WExt_trans _ hy
      simpa only [trunc_trunc] using WExt_trunc (Nat.le_of_lt hk') hx
    exact (RestCalls.restsT_of_restSpec _ (restSpec_of_premise he hk harr (ihb _ hp')
      (by omega) hWV)).2 _ (List.mem_singleton_self _)
  | @arrCopy Γ s S T E hs hsp hr ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_cons, List.map_nil]
    have := copy_safe (spreadsInto_sound hsp) (meaning_adm G E) (meaning_valOnly G E) hw hh
      (ih n W h ρ he hw hh)
    apply Safe_mono n _ W h _ this
    intro k _ U v hv
    exact (represents_sem hr k U v).mpr ⟨by simpa [tupleFams] using hv, by simp⟩
  | @callRest Γ f F xs Us E B parts hf hmem hx hu hshort hp hplain hspread ihf ihx ihu ihp =>
    intro n W h ρ he hw hh
    have hterm : instantiate 0 ρ (.call f (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2)))
        = .call (instantiate 0 ρ f) ((xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.snd ++
          (parts.map fun p => ((if p.1 then some (meaning G p.2.1) else none), instantiate 0 ρ p.2.2)).map
            RestCalls.partTerm) := by
      simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map, Function.comp_def,
        instantiate_spreadTerm]
      congr 2
      apply List.map_congr_left
      intro p _
      rcases p with ⟨_ | _, A, t⟩ <;> rfl
    rw [hterm]
    apply rest_call_safe (Ps := xs.map fun p => meaning G p.1) (Us := Us.map (meaning G))
      (E := meaning G E) (R := meaning G B)
      (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q.1)
      (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q.1)
      (meaning_adm G E) (meaning_valOnly G E)
      (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      _ (by simp [List.map_map, Function.comp_def]) _
      (by rcases hshort with h | h <;> simp [h])
      (by
        intro q hq S hS
        obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
        rcases p with ⟨_ | _, A, t⟩
        · simp at hS
        · simp only [if_true, Option.some.injEq] at hS
          subst hS
          exact ⟨meaning_adm G A, spreadsInto_sound (hspread _ hp' rfl)⟩)
      hw hh
      (Safe_mono n (fun m _ U v hv => by
        have := restsT_of_restSigs hmem hv
        simpa [List.map_map, List.map_append, Function.comp_def] using this) W h _
        (ihf n W h ρ he hw hh))
    · intro q hq j hj U hxU hu heap hok
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
      exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
    · intro q hq j hj U hxU hu heap hok
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
      rcases p with ⟨_ | _, A, t⟩
      · have hA : A = E := hplain _ hp' rfl
        subst hA
        exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
      · exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
    · intro A hA j hj U hxU hu' heap hok
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
      exact ihu q hq j U heap ρ (he.transfer j hj U hxU) hu' hok
  | sub ht hc ih =>
    intro n W h ρ he hw hh
    exact Safe_mono n (fun k _ V v hv => (PositiveCertificates.check_sound hc).sound k V v hv)
      W h _ (ih n W h ρ he hw hh)

/-- Syntactically typed bodies establish exact-arity list signatures, including
zero parameters, without encoding the function as nested unary closures. -/
theorem HasTy.invocationSpec {G : NormalGraph ι} {Γ ρ n W b arity}
    {L : List (List (Ty ι) × Ty ι)} (he : EnvOk G Γ ρ n W)
    (hlen : ∀ p ∈ L, p.1.length = arity)
    (hb : ∀ p ∈ L, HasTy G (p.1 ++ Γ) b p.2) :
    InvocationSpec arity (L.map fun p => (p.1.map (meaning G), meaning G p.2))
      n W (instantiate arity ρ b) :=
  invocation_of_body he hlen (fun p hp => (hb p hp).sound)

/-- The closed-program interface requires scope explicitly, so free source
variables cannot be silently filled by the total semantic environment. -/
theorem HasTy.closed_safe {G : NormalGraph ι} {t A} (ht : HasTy G [] t A)
    (hc : Scoped 0 t) (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaning G A) n W h t := by
  have he : EnvOk G [] (fun _ => .nul) n W := ⟨fun _ => trivial, by simp⟩
  simpa only [instantiate_above hc] using ht.sound n W h _ he hw hh

#print axioms bind_list
#print axioms call_safe
#print axioms invocation_of_body
#print axioms HasTy.invocationSpec
#print axioms HasTy.sound
#print axioms HasTy.closed_safe
#print axioms tagClause_sound

end Verification.ExperimentState.ProgramTyping
