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

theorem meaning_value {G : NormalGraph ι} {A n W v} (h : meaning G A n W v) :
    isVal v = true ∧ Scoped 0 v := by
  obtain ⟨c, _, hc⟩ := (expand_sem G A n W v).mp h
  cases c with
  | nul => subst v; exact ⟨rfl, trivial⟩
  | bool => rcases hc with rfl | rfl <;> exact ⟨rfl, trivial⟩
  | boolLit b => cases b <;> cases hc <;> exact ⟨rfl, trivial⟩
  | refs a rest => obtain ⟨l, _, rfl, _⟩ := hc.1; exact ⟨rfl, trivial⟩
  | arrs L => exact ⟨hc.1.val, hc.1.scoped⟩
  | callable a bs L => exact ⟨hc.2.1.val,hc.2.1.scoped⟩
  | undef => subst v; exact ⟨rfl, trivial⟩

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

/-- Unary graph clauses use the same parameter-environment proof. -/
theorem code_of_body {G : NormalGraph ι} {Γ ρ n W b}
    {L : List (Ty ι × Ty ι)} (he : EnvOk G Γ ρ n W)
    (hb : ∀ p ∈ L, ∀ j U heap env, EnvOk G (p.1 :: Γ) env j U →
      WorldAdm U → HeapOk j U heap → Safe (meaning G p.2) j U heap (instantiate 0 env b)) :
    CodeSpec (L.map fun p => (meaning G p.1, meaning G p.2)) n W (instantiate 1 ρ b) := by
  have hs := invocation_of_body (arity := 1) (L := L.map fun p => ([p.1], p.2)) he
    (by intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; rfl)
    (by intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; exact hb q hq)
  simpa only [CodeSpec, List.map_map, Function.comp_def, List.map_cons, List.map_nil] using hs

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

/-- Unary application is a specialization of effectful list evaluation. -/
theorem app_safe {A B : Fam} (hA : Adm A) (hAv : ValOnly A)
    {n W heap f a} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe (arrowT A B) n W heap f) (ha : FutureSafe A n W a) :
    Safe B n W heap (.app f a) := by
  apply call_safe [(A,a)] (by intro p hp; cases List.mem_singleton.mp hp; exact hA)
    (by intro p hp; cases List.mem_singleton.mp hp; exact hAv) hw hh
  · apply Safe_mono n _ W heap f hf
    intro k hk U v hv
    exact (arrowsT_callsT [(A,B)] k U v).mp ((arrowsT_singleton A B k U v).mpr hv)
  · intro p hp; cases List.mem_singleton.mp hp; exact ha

def tagShape (tag : Tag) (s : Nat) : Bool :=
  match tag with
  | .isNul => s == 0 | .isBool => s == 1 | .isRef => s == 2
  -- A function object is a function to `typeof`, as a lambda is.
  | .isFun => s == 3 | .isUndef => s == 4 | .isNullish => s == 0 || s == 4

/-- A finite syntactic check; it neither executes a term nor queries membership. -/
def Answers (G : NormalGraph ι) (A : Ty ι) (tag : Tag) (q : Bool) : Prop :=
  ∀ c ∈ expand G A, tagShape tag (shape c) = q

theorem answers_sound {G : NormalGraph ι} {A tag q n W v}
    (hq : Answers G A tag q) (hv : meaning G A n W v) : tagHolds tag v = q := by
  obtain ⟨c, hc, hv⟩ := (expand_sem G A n W v).mp hv
  have htag : tagHolds tag v = tagShape tag (valueShape v) := by
    -- An object's answer depends on what sits in its call slot. `cases v`
    -- re-introduces the membership hypothesis after the object's two fields.
    cases tag <;> cases v <;> first | rfl | (rename_i l c h; cases c <;> rfl)
  rw [htag, sem_shape hv]
  exact hq c hc

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
  | funE : Represents G F (.arrs L) →
      (∀ p ∈ L, HasTy G (p.1 :: Γ) b p.2) → HasTy G Γ (.funE b) F
  | makeCallable : Represents G F (.callable P [] L) → HasTy G Γ a P →
      (∀ p ∈ L, HasTy G (p.1 :: Γ) b p.2) → HasTy G Γ (.attach b a) F
  | callCallable : HasTy G Γ f F → Represents G F (.callable P Ps L) → (A,B) ∈ L →
      HasTy G Γ a A → HasTy G Γ (.app f a) B
  | readCallable : HasTy G Γ a F → Represents G F (.callable P Ps L) →
      HasTy G Γ (.read a) P
  | writeCallable : HasTy G Γ a F → Represents G F (.callable P Ps L) → HasTy G Γ b P →
      Represents G N .nul → HasTy G Γ (.write a b) N
  | app : HasTy G Γ f F → Represents G F (.arrs L) → (A, B) ∈ L →
      HasTy G Γ a A → HasTy G Γ (.app f a) B
  | letE : HasTy G Γ a A → HasTy G (A :: Γ) b B → HasTy G Γ (.letE a b) B
  | alloc : HasTy G Γ a A → Represents G Ref (.refs A []) → HasTy G Γ (.alloc a) Ref
  | read : HasTy G Γ a Ref → Represents G Ref (.refs A []) → HasTy G Γ (.read a) A
  | write : HasTy G Γ a Ref → Represents G Ref (.refs A []) → HasTy G Γ b A →
      Represents G N .nul → HasTy G Γ (.write a b) N
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
  | @funE F L Γ b hr hb ih =>
    intro n W h ρ he hw hh
    have hcode : CodeSpec (L.map fun p => (meaning G p.1, meaning G p.2))
        n W (instantiate 1 ρ b) := by
      exact code_of_body he (fun p hp => ih p hp)
    have hs := attach_rule nulT_adm n W h _ .nul hcode rfl hw hh rfl
    exact Safe_mono n (fun k _ U v hv => (represents_sem hr k U v).mpr hv.2) W h _ hs
  | @makeCallable F P L Γ a b hr ha hb iha ihb =>
    intro n W h ρ he hw hh
    have hcode : CodeSpec (L.map fun p => (meaning G p.1,meaning G p.2))
        n W (instantiate 1 ρ b) := by
      exact code_of_body he (fun p hp => ihb p hp)
    apply bind (Tm.attach (instantiate 1 ρ b)) Step.makeC n W h _ hw hh (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    have hc : CodeSpec (L.map fun p => (meaning G p.1,meaning G p.2)) j U (instantiate 1 ρ b) :=
      (arrowsT_code_iff _ 0 _ j U).mp ((arrowsT_adm _).mono j _ U hx _
        ((arrowsT_adm _).down_le n j hj W _ ((arrowsT_code_iff _ 0 _ n W).mpr hcode)))
    have hs := attach_rule (meaning_adm G P) j U heap _ av hc hav hu hok ha'
    exact Safe_mono j (fun k _ V v hv => (represents_sem hr k V v).mpr ⟨⟨hv.1,by simp⟩,hv.2⟩) U heap _ hs
  | @callCallable Γ f F P Ps L A B a hf hr hp ha ihf iha =>
    intro n W h ρ he hw hh
    apply app_safe (meaning_adm G A) (meaning_valOnly G A) hw hh
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      have hm := ((represents_sem hr k U v).mp hv).2
      exact ⟨hm.1, hm.2 _ (List.mem_map.mpr ⟨(A,B), hp, rfl⟩)⟩
    · intro j hj U hx hu heap hok
      exact iha j U heap ρ (he.transfer j hj U hx) hu hok
  | @readCallable Γ a Ref A Ps L ha hr ih =>
    intro n W h ρ he hw hh
    apply bind Tm.read Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    exact bag_read (meaning_valOnly G A) ((represents_sem hr j U v).mp ha').1.1 hu hok
  | @writeCallable Γ a Ref A Ps L b N ha hr hb hn iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .write a (instantiate 0 ρ b)) Step.writeC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.write av) (Step.writeC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G Ref).mono k _ V hy av ((meaning_adm G Ref).down_le j k hk U av ha')
    apply Safe_mono k (fun i _ X v hval => (represents_sem hn i X v).mpr hval)
    exact bag_write (meaning_adm G A) ((represents_sem hr k V av).mp ha'').1.1 hb' hbval hv hok'
  | @app Γ f F L A B a hf hr hp ha ihf iha =>
    intro n W h ρ he hw hh
    apply app_safe (meaning_adm G A) (meaning_valOnly G A) hw hh
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      have hm := (represents_sem hr k U v).mp hv
      exact ⟨hm.1, hm.2 _ (List.mem_map.mpr ⟨(A,B), hp, rfl⟩)⟩
    · intro j hj U hx hu heap hok
      exact iha j U heap ρ (he.transfer j hj U hx) hu hok
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
  | @alloc Γ a A Ref ha hr ih =>
    intro n W h ρ he hw hh
    apply bind Tm.alloc Step.makeC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    apply Safe_mono j (fun k _ V v hv => (represents_sem hr k V v).mpr ⟨hv, by simp⟩)
    exact alloc_rule (meaning_adm G A) j U heap v hv hu hok ha'
  | @read Γ a Ref A ha hr ih =>
    intro n W h ρ he hw hh
    apply bind Tm.read Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    obtain ⟨l, c, rfl, hl, hag⟩ := ((represents_sem hr j U v).mp ha').1
    exact read_rule (meaning_valOnly G A) j U heap l hu hok hl hag
  | @write Γ a Ref A b N ha hr hb hn iha ihb =>
    intro n W h ρ he hw hh
    apply bind (fun a => .write a (instantiate 0 ρ b)) Step.writeC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj U hx hu heap av hok hav ha'
    apply bind (.write av) (Step.writeC2 hav) j U heap _ hu hok
      (ihb j U heap ρ (he.transfer j hj U hx) hu hok)
    intro k hk V hy hv heap' bv hok' hbval hb'
    have ha'' := (meaning_adm G Ref).mono k _ V hy av ((meaning_adm G Ref).down_le j k hk U av ha')
    obtain ⟨l, c, rfl, hl, hag⟩ := ((represents_sem hr k V av).mp ha'').1
    apply Safe_mono k (fun i _ X v hval => (represents_sem hn i X v).mpr hval)
    exact write_rule (meaning_adm G A) k V heap' l bv hbval hv hok' hl hag hb'
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
#print axioms app_safe
#print axioms invocation_of_body
#print axioms code_of_body
#print axioms HasTy.invocationSpec
#print axioms HasTy.sound
#print axioms HasTy.closed_safe
end Verification.ExperimentState.ProgramTyping
