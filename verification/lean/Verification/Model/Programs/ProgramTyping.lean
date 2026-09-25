import Verification.Model.Programs.CallableObjects
import Verification.Model.Types.PositiveCertificates

/-!
# Program typing over positive recursive types

Types are finite unions of graph labels. Constructor rules inspect a singleton
expanded clause; subsumption is justified by the existing checked certificates.
The typing judgement is syntactic. Semantic environments enter only its soundness
proof, not its rules.
-/
namespace Verification.Model.ProgramTyping
open PositiveNormalization PositiveGraphs PositiveRules Tower

variable {ι : Type}

abbrev Ty (ι : Type) := List ι

def Represents (G : NormalGraph ι) (A : Ty ι) (c : Clause (Ty ι)) : Prop :=
  expand G A = [c]

/-- A type represented by a clause is of clause rows. -/
theorem Represents.plain {G : NormalGraph ι} {A c} (hr : Represents G A c) :
    G.plainTy A = true :=
  plain_of_mem_expand (c := c) (by simp [show expand G A = [c] from hr])

theorem represents_sem {G : NormalGraph ι} {A c} (hr : Represents G A c) (n W v) :
    meaning G A n W v ↔ clauseSem G c n W v := by
  rw [expand_sem G A hr.plain, show expand G A = [c] from hr]
  simp [semList, setSem]

theorem meaning_adm (G : NormalGraph ι) (A : Ty ι) : Adm (meaning G A) :=
  setSem_adm (normalDenote_adm G) A

theorem argMeaning_adm (G : NormalGraph ι) (P : Ty ι) : Adm (argMeaning G P) :=
  graphArguments_adm G G.env _ (fun S => meaning_adm G S) P

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
  obtain ⟨_, _, hv⟩ := h
  exact normalDenote_value hv

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

/-- The context a closure body is checked in at one signature: the
receiver, then the parameters the code takes, then the captures. -/
abbrev bodyFrame (arity : Nat) (p : Ty ι × List (Ty ι) × Ty ι) (Γ : List (Ty ι)) : List (Ty ι) :=
  p.1 :: p.2.1.take arity ++ Γ

/-- The rows a closure's code is checked at: its fixed signatures, then each
variadic signature's receiver, fixed parameters and result. Code of fixed
arity meets a variadic signature whose fixed parameters cover its arity:
binding discards the actuals past them (`restsT_of_invocationSpec`). -/
def offerRows (L : List (Ty ι × List (Ty ι) × Ty ι)) (S : List (Ty ι × List (Ty ι) × Ty ι × Ty ι)) :
    List (Ty ι × List (Ty ι) × Ty ι) :=
  L ++ S.map fun s => (s.1, s.2.1, s.2.2.2)

/-- Each signature offers at least the code's arity: the check every
code-creating rule, certificate and search makes. -/
def offersArity (arity : Nat) (L : List (Ty ι × List (Ty ι) × Ty ι)) : Bool :=
  L.all fun p => arity ≤ p.2.1.length

/-- A body safe under every declared parameter and receiver environment
establishes the native invocation contract, through
`invocationSpec_of_instantiated`: each signature offers at least the code's
arity, and the body sees the parameters the code takes. -/
theorem invocation_of_body {G : NormalGraph ι} {Γ ρ n W b arity}
    {L : List (Ty ι × List (Ty ι) × Ty ι)} (he : EnvOk G Γ ρ n W)
    (hlen : ∀ p ∈ L, arity ≤ p.2.1.length)
    (hb : ∀ p ∈ L, ∀ j U heap env, EnvOk G (bodyFrame arity p Γ) env j U →
      WorldAdm U → HeapOk j U heap → Safe (meaning G p.2.2) j U heap (instantiate 0 env b)) :
    InvocationSpec arity (L.map fun p => (meaning G p.1, p.2.1.map (meaning G), meaning G p.2.2))
      n W (instantiate (arity + 1) ρ b) := by
  have hscoped : ∀ (As : List (Ty ι)) j U args, ArgsT (As.map (meaning G)) j U args →
      ∀ a ∈ args, Scoped 0 a := by
    intro As
    induction As with
    | nil => intro j U args ha; cases args <;> simp_all [ArgsT]
    | cons A As ih =>
      intro j U args ha
      cases args with
      | nil => exact False.elim ha
      | cons a args =>
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact (meaning_value ha.1).2
        · exact ih j U args ha.2 v hv
  apply invocationSpec_of_instantiated he.1
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simpa using hlen q hq
  · intro p hp j U r args hr ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hscoped (q.1 :: q.2.1.take arity) j U (r :: args) ⟨hr, by simpa [List.map_take] using ha⟩
  · intro p hp j hj U hx hu heap hok r args hr ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hall : ArgsT ((q.1 :: q.2.1.take arity).map (meaning G)) j U (r :: args) :=
      ⟨hr, by simpa [List.map_take] using ha⟩
    have henv := (he.transfer j (Nat.le_of_lt hj) U hx).prepend hall
    exact hb q hq j U heap _ (by simpa [bodyFrame, List.append_assoc] using henv) hu hok

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

/-- A family holds of a saved value across two later worlds. -/
theorem adm_transfer2 {A : Fam} (hA : Adm A) {j i k : Nat} {U : WorldT j} {X : WorldT i}
    {V : WorldT k} {v : Val} (ha : A j U v) (hi : i ≤ j) (hy : WExt (trunc i hi U) X)
    (hk : k ≤ i) (hz : WExt (trunc k hk X) V) : A k V v :=
  hA.mono k _ V hz v (hA.down_le i k hk X v (hA.mono i _ X hy v (hA.down_le j i hi U v ha)))

/-- `new f(args)`: the constructor runs first, then the actuals left to right;
the construct step then enters the class's body, which the constructor's
signature makes safe one level down. The signature may declare trailing
positions `Us` the source omits: each admits `undefined`, which is what the
step binds there, so the body entered is the one the padded list enters. -/
theorem construct_safe {B : Fam} (xs : List (Fam × Tm)) (Us : List Fam)
    (hA : ∀ p ∈ xs, Adm p.1) (hAv : ∀ p ∈ xs, ValOnly p.1)
    (hUA : ∀ A ∈ Us, Adm A)
    {n W heap f} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe (ctorsT [(xs.map Prod.fst ++ Us, B)]) n W heap f)
    (ha : ∀ p ∈ xs, FutureSafe p.1 n W p.2)
    (hu : ∀ A ∈ Us, FutureSafe A n W .undef) :
    Safe B n W heap (.construct f (xs.map Prod.snd)) := by
  apply bind (fun f => .construct f (xs.map Prod.snd)) Step.constructL n W heap f hw hh hf
  intro j hj U hx hw' heap' v hok hv hctor
  apply bind_list xs hA (Tm.construct v) (fun hs => CallArguments.Step.constructArgs hv hs) hw' hok
    (fun p hp => (ha p hp).transfer hj hx)
  intro k hk V hz hv' heap3 args hok3 hargs
  cases k with
  | zero => trivial
  | succ k =>
    have hc := adm_transfer2 (ctorsT_adm _) hctor (Nat.le_refl j)
      (by rw [trunc_id]; exact WExt_refl _) hk hz
    have hAm : ∀ A ∈ xs.map Prod.fst ++ Us, Adm A := by
      intro A hA'
      rcases List.mem_append.mp hA' with hA' | hA'
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hA'; exact hA p hp
      · exact hUA A hA'
    have hAvm : ∀ A ∈ xs.map Prod.fst, ValOnly A := by
      intro A hA'; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hA'; exact hAv p hp
    have hvals : CallArguments.Values args := ArgsT_values hAvm hargs
    have hundef : ∀ A ∈ Us, A (k+1) V .undef := by
      intro A hA'
      exact safe_value_mem rfl
        ((((hu A hA').transfer hj hx)).transfer hk hz (k+1) (Nat.le_refl _) V
          (by rw [trunc_id]; exact WExt_refl _) hv' heap3 hok3)
    have hpad : ∀ a ∈ List.replicate Us.length Tm.undef, a = .undef :=
      fun _ h => List.eq_of_mem_replicate h
    have hall := ArgsT_append hargs (ArgsT_undef hundef)
    have hpvals : CallArguments.Values (args ++ List.replicate Us.length .undef) := by
      intro a h
      rcases List.mem_append.mp h with h | h
      · exact hvals a h
      · rw [hpad a h]; rfl
    obtain ⟨result, ⟨fs, arity, b, rfl, rfl⟩, hsafe⟩ :=
      hc.2 _ (List.mem_singleton_self _) k (Nat.lt_succ_self k) (trunc k (Nat.le_succ k) V)
        (WExt_refl _) (WorldAdm_trunc _ hv') heap3 (HeapOk_trunc k V heap3 hok3) _ hpvals
        (ArgsT_transfer hAm hall k (Nat.le_succ k) _ (WExt_refl _))
    rw [CallArguments.bindParameters_pad _ _ _ _ _ hpad] at hsafe
    exact Or.inr ⟨trunc k (Nat.le_succ k) V, heap3, _, WExt_refl _, WorldAdm_trunc _ hv',
      .constructV hvals, HeapOk_trunc k V heap3 hok3, hsafe⟩

/-- A call that writes fewer actuals than its selected signature declares. The
callee runs first, then the receiver, then the actuals. The omitted positions
are exactly the ones whose contract admits `undefined`, which is the value the
machine binds there; nothing is added to the source term. -/
theorem call_safe_short {Rc B : Fam} (xs : List (Fam × Tm)) (Us : List Fam)
    (hRc : Adm Rc) (hRcv : ValOnly Rc)
    (hA : ∀ p ∈ xs, Adm p.1) (hAv : ∀ p ∈ xs, ValOnly p.1)
    (hUA : ∀ A ∈ Us, Adm A) (hUAv : ∀ A ∈ Us, ValOnly A)
    {n W heap f r} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe (callsT [(Rc, xs.map Prod.fst ++ Us, B)]) n W heap f)
    (hr : FutureSafe Rc n W r)
    (ha : ∀ p ∈ xs, FutureSafe p.1 n W p.2)
    (hu : ∀ A ∈ Us, FutureSafe A n W .undef) :
    Safe B n W heap (.invoke f r (xs.map Prod.snd)) := by
  apply bind (fun f => .invoke f r (xs.map Prod.snd)) Step.callL n W heap f hw hh hf
  intro j hj U hx hw' heap' v hok hv hfun
  apply bind (fun r => .invoke v r (xs.map Prod.snd)) (Step.callRecv hv) j U heap' r hw' hok
    ((hr.transfer hj hx) j (Nat.le_refl _) U (by rw [trunc_id]; exact WExt_refl _) hw' heap' hok)
  intro i hi X hy hX heap'' rv hok'' hrv hrm
  apply bind_list xs hA (Tm.invoke v rv)
    (fun hs => (CallArguments.Prepare.args hv hrv hs).step) hX hok''
    (fun p hp => ((ha p hp).transfer hj hx).transfer hi hy)
  intro k hk V hz hv' heap3 args hok3 hargs
  cases k with
  | zero => trivial
  | succ k =>
    have hf' := adm_transfer2 (callsT_adm _) hfun hi hy hk hz
    have hr' := adm_transfer2 hRc hrm (Nat.le_refl i) (by rw [trunc_id]; exact WExt_refl _) hk hz
    have hundef : ∀ A ∈ Us, A (k+1) V .undef := by
      intro A hA'
      exact safe_value_mem rfl
        ((((hu A hA').transfer hj hx).transfer hi hy).transfer hk hz (k+1) (Nat.le_refl _) V
          (by rw [trunc_id]; exact WExt_refl _) hv' heap3 hok3)
    refine call_elim_short (p := (Rc, xs.map Prod.fst ++ Us, B))
      (pad := List.replicate Us.length .undef) hRc
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
      (by intro a h; exact List.eq_of_mem_replicate h) hrv
      hf' (List.mem_singleton_self _) hr'
      (ArgsT_append hargs (ArgsT_undef hundef)) hv' hok3

/-- Native call compatibility includes the callee, the receiver and every
effectful actual, then uses the invocation contract only after all operands
have become values. -/
theorem call_safe {Rc B : Fam} (xs : List (Fam × Tm)) (hRc : Adm Rc) (hRcv : ValOnly Rc)
    (hA : ∀ p ∈ xs, Adm p.1) (hAv : ∀ p ∈ xs, ValOnly p.1)
    {n W heap f r} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe (callsT [(Rc, xs.map Prod.fst, B)]) n W heap f)
    (hr : FutureSafe Rc n W r)
    (ha : ∀ p ∈ xs, FutureSafe p.1 n W p.2) :
    Safe B n W heap (.invoke f r (xs.map Prod.snd)) :=
  call_safe_short xs [] hRc hRcv hA hAv (by simp) (by simp) hw hh (by simpa using hf) hr ha (by simp)

/-- A shape-only test has a fixed answer. Numeric equality needs the
singleton bits; the whole number family has no uniform answer. -/
def tagShape (tag : Tag) (s : Nat) : Option Bool :=
  match tag with
  | .isNul => some (s == 0) | .isBool => some (s == 1) | .isRef => some (s == 2)
  -- A class value (shape 11) is a function to `typeof`, as a callable is.
  | .isFun => some (s == 3 || s == 11) | .isUndef => some (s == 4)
  | .isNullish => some (s == 0 || s == 4) | .isNum => some (s == 5)
  | .numEq _ => if s == 5 then none else some false
  | .isStr => some (s == 6)
  | .strEq _ => if s == 6 then none else some false
  | .isBigint => some (s == 9)
  | .isSymbol => some (s == 10)

def tagClause (tag : Tag) (c : Clause α) : Option Bool :=
  match tag, c with
  | _, .top => none
  | .numEq bits, .numLit value => some (numberEqual value bits)
  | .strEq s, .strLit t => some (s == t)
  | _, _ => tagShape tag (shape c)

/-- A finite syntactic check; unknown numeric answers cannot establish either
branch. It neither executes a term nor queries semantic membership. `A` must be
of clause rows: a parameter row's members could be anything. -/
def Answers (G : NormalGraph ι) (A : Ty ι) (tag : Tag) (q : Bool) : Prop :=
  G.plainTy A = true ∧ ∀ c ∈ expand G A, tagClause tag c = some q

theorem tagClause_sound {S : α → Fam} {P : α → ArgFam} {c tag q n W v}
    (hq : tagClause tag c = some q) (hv : semWithArgs S P c n W v) : tagHolds tag v = q := by
  cases ht : tag with
  | numEq bits =>
    cases c <;> simp [ht, tagClause, tagShape, shape] at hq
    all_goals subst q
    case numLit value =>
      change v = .num value at hv
      subst v
      rfl
    all_goals
      have hs := semWithArgs_shape (by simp) hv
      cases v <;> simp_all [ht,valueShape,tagHolds,shape]
  | strEq s =>
    cases c <;> simp [ht, tagClause, tagShape, shape] at hq
    all_goals subst q
    case strLit t =>
      change v = .str t at hv
      subst v
      rfl
    all_goals
      have hs := semWithArgs_shape (by simp) hv
      cases v <;> simp_all [ht,valueShape,tagHolds,shape]
  | isNul | isBool | isRef | isFun | isUndef | isNullish | isNum | isStr | isBigint | isSymbol =>
    by_cases hc : c = .top
    · subst hc; simp [ht, tagClause] at hq
    have htag : some (tagHolds tag v) = tagShape tag (valueShape v) := by
      rw [ht]
      cases v <;> first | rfl | (rename_i fs code; cases code <;> first | rfl | (rename_i kind; cases kind <;> rfl))
    rw [semWithArgs_shape hc hv, ht] at htag
    exact Option.some.inj (htag.trans (by simpa only [ht,tagClause] using hq))

theorem answers_sound {G : NormalGraph ι} {A tag q n W v}
    (hq : Answers G A tag q) (hv : meaning G A n W v) : tagHolds tag v = q := by
  obtain ⟨c, hc, hv⟩ := (expand_sem G A hq.1 n W v).mp hv
  exact tagClause_sound (hq.2 c hc) hv

/-! ## Variadic functions

A variadic body finds the actuals past its fixed parameters in a fresh array in
slot 0. The array's type is an object whose one field holds a store of any
length at the element type; a spread reads a store whose every position's type
is among the element type's labels, and `undefined` must be among them when the
store may have a hole. -/

/-- The variadic signatures a callable type carries, fixed or callable object
alike; none for any other type. -/
def restSigs (G : NormalGraph ι) (F : Ty ι) : List (Ty ι × List (Ty ι) × Ty ι × Ty ι) :=
  match expand G F with
  | [.arrs _ S] | [.callable _ _ _ S] => S
  | _ => []

theorem restsT_of_restSigs {G : NormalGraph ι} {F : Ty ι} {s} (hs : s ∈ restSigs G F) {n W v}
    (hv : meaning G F n W v) :
    restsT [(meaning G s.1, s.2.1.map (meaning G), argMeaning G s.2.2.1, meaning G s.2.2.2)] n W v := by
  unfold restSigs at hs
  split at hs
  · rename_i L S hF
    have hv' := ((represents_sem hF n W v).mp hv).2
    exact restsT_select hv' (List.mem_map_of_mem hs)
  · rename_i P Ps L S hF
    have hv' := ((represents_sem hF n W v).mp hv).2
    exact restsT_select hv' (List.mem_map_of_mem hs)
  · cases hs

/-- The member a type's one object clause names by a key: a host-relative
method, whose contract holds when it is invoked on the object it is read from. -/
def memberOf (G : NormalGraph ι) (O : Ty ι) (k : PropKey) : Option (MethodMembers.Sig (Ty ι)) :=
  match expand G O with
  | [.refs _ _ _ _ ms _] | [.dict _ _ _ _ _ ms _ _] => ms.find? (·.key == k)
  | _ => none

/-- A fixed signature covered by one of a member's: each claimed parameter
within the member's, and the member's result within the claimed one, by
checked proofs. The claimed types may be other rows for the same types, such as
a producer's copy of a declared array type. -/
def CoveredCall [DecidableEq ι] (G : NormalGraph ι) (q : Ty ι × List (Ty ι) × Ty ι)
    (c : List (Ty ι) × Ty ι) : Prop :=
  q.2.1.length = c.1.length ∧
    (∀ x ∈ q.2.1.zip c.1, ∃ p, PositiveCertificates.check G x.1 x.2 p = true) ∧
    ∃ p, PositiveCertificates.check G c.2 q.2.2 p = true

/-- Parameters each within the member's, as families. -/
theorem CoveredCall.params [DecidableEq ι] {G : NormalGraph ι} :
    ∀ {Ds Cs : List (Ty ι)}, Ds.length = Cs.length →
      (∀ x ∈ Ds.zip Cs, ∃ p, PositiveCertificates.check G x.1 x.2 p = true) →
      ArgsLe (Ds.map (meaning G)) (Cs.map (meaning G))
  | [], [], _, _ => .nil
  | D :: Ds, C :: Cs, hl, h => by
    obtain ⟨p, hp⟩ := h (D, C) (by simp)
    exact .cons (PositiveCertificates.accepted hp)
      (CoveredCall.params (by simpa using hl) fun x hx => h x (by simp [hx]))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- A member of a host's type is found by the member's key on the host, whose
contract implies the member's signatures invoked on that host. -/
theorem memberOf_at {G : NormalGraph ι} {O : Ty ι} {k : PropKey} {m : MethodMembers.Sig (Ty ι)}
    (hm : memberOf G O k = some m) {n W v} (hv : meaning G O n W v) :
    m.key = k ∧ MethodMembers.memberT (MethodMembers.Member.of (meaning G) (argMeaning G) m) n W v := by
  unfold memberOf at hm
  split at hm
  all_goals try contradiction
  all_goals
    rename_i ms hO
    have hmem := List.mem_of_find?_eq_some hm
    have hkey : m.key = k := by simpa using List.find?_some hm
    have hs := (represents_sem (show Represents G O _ from hO) n W v).mp hv
    exact ⟨hkey, MethodMembers.methodT_at (List.mem_map_of_mem hmem)
      (by first | exact hs.2.2.2.1 | exact hs.2.2.2.2.1)⟩

/-- **Reading a member.** The read finds the key on the host, or, one step
later, on the object the host's prototype location holds; either way the
value read meets the member's signatures invoked on the host. -/
theorem member_read_safe {m : MethodMembers.Member} {n : Nat} {W : WorldT n} {h : Heap} {v : Val}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hm : MethodMembers.memberT m n W v) :
    Safe (MethodMembers.onHost v m) n W h (.readAt m.key v) := by
  have hval : ValOnly (MethodMembers.onHost v m) := fun _ _ _ hv => hv.1.1.val
  rcases hm with ⟨flds, l, c, rfl, hf, hl, hag⟩ | ⟨flds, rfl, hmiss, hp⟩
  · exact read_view_rule_ext hval n W h l hw hh hf hl hag
  · obtain ⟨pf, lp, cp, hρ, hpf, hlp, hpag⟩ := hp
    cases hρ
    cases n with
    | zero => trivial
    | succ q =>
      obtain ⟨pv, hpv, hmem⟩ := hh.2 lp cp hlp
      have hU := WorldAdm_trunc (Nat.le_succ q) hw
      have hH := HeapOk_trunc q W h hh
      obtain ⟨qf, l, c, rfl, hf, hl, hag⟩ :=
        hpag q (by omega) _ (WExt_refl _) pv (hmem q (by omega))
      exact Or.inr ⟨trunc q (Nat.le_succ q) W, h, .readAt m.key (.objAt qf .absent), WExt_refl _,
        hU, .readProto hmiss hpf hpv, hH, read_view_rule_ext hval q _ h l hU hH hf hl hag⟩

/-- The fixed signatures a callable type carries, fixed or callable object
alike; none for any other type. -/
def callSigs (G : NormalGraph ι) (F : Ty ι) : List (Ty ι × List (Ty ι) × Ty ι) :=
  match expand G F with
  | [.arrs L _] | [.callable _ _ L _] => L
  | _ => []

theorem callsT_of_callSigs {G : NormalGraph ι} {F : Ty ι} {p} (hp : p ∈ callSigs G F) {n W v}
    (hv : meaning G F n W v) :
    callsT [(meaning G p.1, p.2.1.map (meaning G), meaning G p.2.2)] n W v := by
  unfold callSigs at hp
  split at hp
  · rename_i L S hF
    have hv' := ((represents_sem hF n W v).mp hv).1
    exact callsT_select hv' (List.mem_map_of_mem hp)
  · rename_i P Ps L S hF
    have hv' := ((represents_sem hF n W v).mp hv).1.2
    exact callsT_select hv' (List.mem_map_of_mem hp)
  · cases hp

/-- Saved slots, in order, at the contracts the environment gives them. -/
theorem ArgsT_slots {G : NormalGraph ι} {Γ ρ n W} (he : EnvOk G Γ ρ n W) :
    ∀ {slots : List Nat} {Ps : List (Ty ι)}, slots.map (Γ[·]?) = Ps.map some →
      ArgsT (Ps.map (meaning G)) n W (slots.map ρ)
  | [], [], _ => trivial
  | i :: slots, P :: Ps, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨he.2 _ _ h.1, ArgsT_slots he h.2⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The type of the store a variadic body receives for a rest type: the rest's
one tuple contract, as a writable store, since the store is fresh. -/
def RestStore (G : NormalGraph ι) (S P : Ty ι) : Prop :=
  match expand G P with
  | [.pack T []] => Represents G S (.list { T with readonly := false } [])
  | _ => False

/-- A store type whose elements a spread passes at `E`. -/
def SpreadsInto (G : NormalGraph ι) (S E : Ty ι) : Prop :=
  match expand G S with
  | [.list T []] => ∀ A ∈ T.required ++ T.optional ++ T.rest.toList, ∀ i ∈ A, i ∈ E
  | _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (S P : Ty ι) : Decidable (RestStore G S P) := by
  unfold RestStore; split <;> (try dsimp only [Represents]) <;> infer_instance

instance [DecidableEq ι] (G : NormalGraph ι) (S E : Ty ι) : Decidable (SpreadsInto G S E) := by
  unfold SpreadsInto; split <;> (try dsimp only [Represents]) <;> infer_instance

/-- An actual as a call writes it: itself, or a spread of it. -/
def spreadTerm (p : Bool × Tm) : Tm := if p.1 then .spread p.2 else p.2

theorem instantiate_spreadTerm (d : Nat) (ρ : Env) (p : Bool × Tm) :
    instantiate d ρ (spreadTerm p) = spreadTerm (p.1, instantiate d ρ p.2) := by
  rcases p with ⟨_ | _, t⟩ <;> simp [spreadTerm, instantiate]

theorem positionTy_eq (T : Tuple (Ty ι)) (i : Nat) :
    positionTy T i = PositiveNormalization.Tuple.position T i := by
  rcases hr : T.required[i]? with _ | A <;>
    rcases ho : T.optional[i - T.required.length]? with _ | B <;>
    simp [positionTy, PositiveNormalization.Tuple.position, hr, ho]

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
    have hl := RestCalls.listT_spreads (T := tupleFams (meaning G) T) (E := meaning G E)
      (by
        intro i A hA
        rw [positionFam_tupleFams] at hA
        obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp hA
        rintro n W v ⟨k, hk, hv⟩
        exact ⟨k, h A' (positionTy_mem hA') k hk, hv⟩)
    intro n W heap v hh hv
    exact hl n W heap v hh ((represents_sem hS n W v).mp hv).1
  · exact h.elim

/-- A prefix covering a signature's first fixed positions, then its element
past them: its first positions are the signature's, the rest the element. -/
theorem prefix_take_drop {α : Type} (Ps : List α) (k : Nat) (E : α) :
    (Ps.take k ++ List.replicate (k - Ps.length) E).take Ps.length = Ps.take k ∧
    (Ps.take k ++ List.replicate (k - Ps.length) E).drop Ps.length =
      List.replicate (k - Ps.length) E := by
  by_cases hk : k ≤ Ps.length
  · have h0 : k - Ps.length = 0 := by omega
    rw [h0, List.replicate_zero, List.append_nil]
    refine ⟨List.take_of_length_le (by simp; omega), List.drop_eq_nil_of_le (by simp; omega)⟩
  · rw [List.take_of_length_le (show Ps.length ≤ k by omega)]
    simp

/-- **Allocating the rest store.** A store of the actuals past the fixed ones
meets a rest-store type when the actuals as one pack meet the rest type. -/
theorem restStore_safe {G : NormalGraph ι} {S P : Ty ι} (hS : RestStore G S P)
    {n : Nat} {W : WorldT n} {h : Heap} {extra : List Tm} (hw : WorldAdm W) (hh : HeapOk n W h)
    (he : argMeaning G P n W extra) (hvals : CallArguments.Values extra) :
    Safe (meaning G S) n W h (.arrLit extra) := by
  unfold RestStore at hS
  split at hS
  · rename_i T hP
    have hpos : ∀ i B, positionFam (tupleFams (meaning G) T) i = some B → Adm B := by
      intro i B hB
      rw [PositiveNormalization.positionFam_tupleFams] at hB
      obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp hB
      exact meaning_adm G b
    have := RestCalls.argument_alloc_safe hpos hw hh ((mixed_pack_args hP).mp he) hvals
    apply Safe_mono n _ W h _ this
    intro k _ V v hv
    exact (represents_sem hS k V v).mpr ⟨by simpa [tupleFams] using hv, by simp⟩
  · exact hS.elim

/-- The parts a variadic call writes past its fixed actuals fit its rest. With
a spread among them, the rest is an element rest, each plain part at its
element and each spread spreading into it. Without one, the rest is a pack of
one tuple contract, and the parts are at its positions, within its bounds. -/
def RestParts (G : NormalGraph ι) (P : Ty ι) (parts : List (Bool × Ty ι)) : Prop :=
  if parts.any (·.1) then
    match restElem G P with
    | some E => ∀ p ∈ parts, if p.1 then SpreadsInto G p.2 E else p.2 = E
    | none => False
  else
    match expand G P with
    | [.pack T []] => T.required.length ≤ parts.length ∧
        (T.rest = none → parts.length ≤ T.required.length + T.optional.length) ∧
        ∀ i ∈ List.range parts.length, positionTy T i = (parts[i]?).map (·.2)
    | _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (P : Ty ι) (parts : List (Bool × Ty ι)) :
    Decidable (RestParts G P parts) := by
  unfold RestParts
  split
  · split <;> infer_instance
  · split <;> infer_instance

/-- Plain actuals at the positions of a rest's one tuple contract, within its
bounds, form a pack of the rest. -/
theorem restParts_pack {G : NormalGraph ι} {P : Ty ι} {T : Tuple (Ty ι)}
    (hP : expand G P = [.pack T []]) {Qs : List (Ty ι)}
    (hreq : T.required.length ≤ Qs.length)
    (hbound : T.rest = none → Qs.length ≤ T.required.length + T.optional.length)
    (hpos : ∀ i ∈ List.range Qs.length, positionTy T i = Qs[i]?)
    {k : Nat} {W : WorldT k} {extra : List Tm} (ha : ArgsT (Qs.map (meaning G)) k W extra) :
    argMeaning G P k W extra := by
  have hlen : extra.length = Qs.length := by simpa using ArgsT_length ha
  refine (mixed_pack_args hP).mpr ⟨by simpa [tupleFams, hlen] using hreq,
    by simpa [tupleFams, hlen] using hbound, ?_⟩
  intro i u B hu hB
  have hi : i < Qs.length := hlen ▸ (List.getElem?_eq_some_iff.mp hu).1
  rw [PositiveNormalization.positionFam_tupleFams] at hB
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hB
  have hq : Qs[i]? = some b := by
    rw [← hpos i (List.mem_range.mpr hi), positionTy_eq]
    exact hb
  exact ArgsT_getElem? (A := meaning G b) ha (by simp [List.getElem?_map, hq]) hu

theorem ArgStep_append {h h' : Heap} {args args' : List Tm} (rest : List Tm)
    (s : CallArguments.ArgStep h args h' args') :
    CallArguments.ArgStep h (args ++ rest) h' (args' ++ rest) := by
  induction s with
  | head hs => exact .head hs
  | tail hv _ ih => exact .tail hv ih

/-- **A variadic call with a spread.** The callee, the receiver, the fixed
actuals, then the further parts run left to right; the call meets the
signature's result. Each further actual is at the element contract `E`, and
actuals at `E` form a pack of the rest `P`. -/
theorem rest_call_safe {Rc : Fam} {Ps : List Fam} {E R : Fam} {P : ArgFam}
    (hRc : Adm Rc)
    (hA : ∀ A ∈ Ps, Adm A) (hAv : ∀ A ∈ Ps, ValOnly A) (hE : Adm E) (hEv : ValOnly E)
    (hP : Adm P) (hEP : ∀ k W xs, (∀ e ∈ xs, E k W e) → P k W xs)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps) (parts : List (Option Fam × Tm))
    (hS : ∀ p ∈ parts, ∀ S, p.1 = some S → Adm S ∧ RestCalls.Spreads S E)
    {n W heap f r} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe (restsT [(Rc, Ps, P, R)]) n W heap f)
    (hr : FutureSafe Rc n W r)
    (hx : ∀ p ∈ xs, FutureSafe p.1 n W p.2) (hp : ∀ p ∈ parts, FutureSafe (p.1.getD E) n W p.2) :
    Safe R n W heap (.invoke f r (xs.map Prod.snd ++ parts.map RestCalls.partTerm)) := by
  apply bind (fun f => .invoke f r (xs.map Prod.snd ++ parts.map RestCalls.partTerm)) Step.callL
    n W heap f hw hh hf
  intro j0 hj0 U0 hx0 hu0 heap0 v hok0 hv hfun0
  apply bind (fun r => .invoke v r (xs.map Prod.snd ++ parts.map RestCalls.partTerm))
    (Step.callRecv hv) j0 U0 heap0 r hu0 hok0
    ((hr.transfer hj0 hx0) j0 (Nat.le_refl _) U0 (by rw [trunc_id]; exact WExt_refl _) hu0 heap0 hok0)
  intro j hj1 U hy1 hu' heap' rv hok hrv hrm
  have hfun := adm_transfer2 (restsT_adm _) hfun0 hj1 hy1 (Nat.le_refl j)
    (by rw [trunc_id]; exact WExt_refl _)
  have hxU : WExt (trunc j (Nat.le_trans hj1 hj0) W) U := by
    apply WExt_trans _ hy1
    simpa only [trunc_trunc] using WExt_trunc hj1 hx0
  have hj : j ≤ n := Nat.le_trans hj1 hj0
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (fun args => .invoke v rv (args ++ parts.map RestCalls.partTerm))
    (fun hs => (CallArguments.Prepare.args hv hrv (ArgStep_append _ hs)).step) hu' hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  apply RestCalls.spread_parts_safe hE hEv hv hrv parts k V heap'' args hS hv' hok'
    (ArgsT_values hAv hargs) (fun p hm => ((hp p hm).transfer hj hxU).transfer hk hy)
  intro i hi X hz hX heap3 extra hh3 hext
  have hUX : WExt (trunc i (Nat.le_trans hi hk) U) X := by
    apply WExt_trans _ hz
    simpa only [trunc_trunc] using WExt_trunc hi hy
  have hfX := (restsT_adm _).mono i _ X hUX v
    ((restsT_adm _).down_le j i (Nat.le_trans hi hk) U v hfun)
  have hrX := hRc.mono i _ X hUX rv (hRc.down_le j i (Nat.le_trans hi hk) U rv hrm)
  exact RestCalls.call_elim_rest (s := (Rc, Ps, P, R)) (by simp) hRc hA hAv hP hrv hrX hfX
    (ArgsT_transfer hA hargs i hi X hz) (hEP i X extra hext) (fun e he => hEv i X e (hext e he))
    hX hh3

/-- **A variadic call writing no spread.** The callee, the receiver and every
actual run left to right; the fixed ones meet the signature's parameters, less
trailing ones `Us` the call omits, each admitting `undefined`, and the further
ones, at `Qs`, form a pack of the rest `P`. A call that omits a fixed position
writes no further actual. -/
theorem pack_call_safe {Rc : Fam} {Ps Us Qs : List Fam} {R : Fam} {P : ArgFam}
    (hRc : Adm Rc) (hA : ∀ A ∈ Ps ++ Qs, Adm A) (hAv : ∀ A ∈ Ps ++ Qs, ValOnly A)
    (hUA : ∀ A ∈ Us, Adm A)
    (hpack : ∀ k W extra, ArgsT Qs k W extra → P k W extra)
    (xs : List (Fam × Tm)) (hxs : xs.map Prod.fst = Ps ++ Qs) (hshort : Us = [] ∨ Qs = [])
    {n W heap f r} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe (restsT [(Rc, Ps ++ Us, P, R)]) n W heap f)
    (hr : FutureSafe Rc n W r) (hx : ∀ p ∈ xs, FutureSafe p.1 n W p.2)
    (hu : ∀ A ∈ Us, FutureSafe A n W .undef) :
    Safe R n W heap (.invoke f r (xs.map Prod.snd)) := by
  apply bind (fun f => .invoke f r (xs.map Prod.snd)) Step.callL n W heap f hw hh hf
  intro j0 hj0 U0 hx0 hu0 heap0 v hok0 hv hfun0
  apply bind (fun r => .invoke v r (xs.map Prod.snd)) (Step.callRecv hv) j0 U0 heap0 r hu0 hok0
    ((hr.transfer hj0 hx0) j0 (Nat.le_refl _) U0 (by rw [trunc_id]; exact WExt_refl _) hu0 heap0 hok0)
  intro j hj1 U hy1 hu' heap' rv hok hrv hrm
  have hfun := adm_transfer2 (restsT_adm _) hfun0 hj1 hy1 (Nat.le_refl j)
    (by rw [trunc_id]; exact WExt_refl _)
  have hxU : WExt (trunc j (Nat.le_trans hj1 hj0) W) U := by
    apply WExt_trans _ hy1
    simpa only [trunc_trunc] using WExt_trunc hj1 hx0
  have hj : j ≤ n := Nat.le_trans hj1 hj0
  apply bind_list xs (by intro p hm; exact hA p.1 (hxs ▸ List.mem_map_of_mem hm))
    (fun args => .invoke v rv args)
    (fun hs => (CallArguments.Prepare.args hv hrv hs).step) hu' hok
    (fun p hm => (hx p hm).transfer hj hxU)
  intro k hk V hy hv' heap'' args hok' hargs
  rw [hxs] at hargs
  cases k with
  | zero => trivial
  | succ k =>
    let X := trunc k (Nat.le_succ k) V
    have hX : WorldAdm X := WorldAdm_trunc _ hv'
    have hhX : HeapOk k X heap'' := HeapOk_trunc k V heap'' hok'
    have hfV := (restsT_adm _).mono (k + 1) _ V hy v
      ((restsT_adm _).down_le j (k + 1) hk U v hfun)
    have hrV := hRc.down k V rv (hRc.mono (k + 1) _ V hy rv (hRc.down_le j (k + 1) hk U rv hrm))
    have hargsX := ArgsT_transfer hA hargs k (Nat.le_succ k) X (WExt_refl _)
    have hsplit := ArgsT_take_drop Ps.length hargsX
    simp only [List.take_left', List.drop_left', List.take_append_of_le_length (Nat.le_refl _),
      List.take_length, List.drop_append_of_le_length (Nat.le_refl _), List.drop_length,
      List.nil_append] at hsplit
    have hacc : ArgsRest (Ps ++ Us) P k X args := by
      rcases hshort with rfl | rfl
      · have := ArgsRest_of_exact_extra (Ps := Ps) hsplit.1 (hpack k X _ hsplit.2)
        simpa only [List.append_nil, List.take_append_drop] using this
      · have hundef : ∀ A ∈ Us, A k X .undef := by
          intro A hA'
          have := safe_value_mem rfl
            (((hu A hA').transfer hj hxU).transfer hk hy (k + 1) (Nat.le_refl _) V
              (by rw [trunc_id]; exact WExt_refl _) hv' heap'' hok')
          exact (hUA A hA').down k V _ this
        simp only [List.append_nil] at hargsX
        have hshortX : ArgsShort (Ps ++ Us) k X args :=
          ArgsShort_of_pad (pad := List.replicate Us.length .undef)
            (fun a hm => List.eq_of_mem_replicate hm)
            (ArgsT_append hargsX (ArgsT_undef hundef))
        have hl : args.length ≤ (Ps ++ Us).length := hshortX.1
        refine ⟨by rwa [List.take_of_length_le hl], ?_⟩
        rw [List.drop_eq_nil_of_le hl]
        exact hpack k X [] trivial
    obtain ⟨body, hi, hsafe⟩ := hfV.2 (Rc, Ps ++ Us, P, R) (by simp) k (Nat.lt_succ_self k) X
      (WExt_refl _) hX heap'' hhX rv hrv hrV args (ArgsT_values hAv hargsX) hacc
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

/-- Variadic code built from a body checked with the rest store in slot 0,
then the receiver and the fixed parameters, meets its code contract at any
later world and budget. -/
theorem restSpec_of_premise {G : NormalGraph ι} {Γ : List (Ty ι)} {ρ : Env} {n : Nat}
    {W : WorldT n} {k : Nat} {b : Tm} {s : Ty ι × List (Ty ι) × Ty ι × Ty ι} {A : Ty ι}
    (he : EnvOk G Γ ρ n W) (hk : s.2.1.length = k) (harr : RestStore G A s.2.2.1)
    (ih : ∀ j U heap env, EnvOk G (A :: s.1 :: s.2.1 ++ Γ) env j U → WorldAdm U →
      HeapOk j U heap → Safe (meaning G s.2.2.2) j U heap (instantiate 0 env b))
    {j : Nat} (hj : j ≤ n) {U : WorldT j} (hx : WExt (trunc j hj W) U) :
    RestCalls.RestSpec k (meaning G s.1) (s.2.1.map (meaning G)) (argMeaning G s.2.2.1)
      (meaning G s.2.2.2) j U (instantiate (k + 2) ρ b) := by
  apply RestCalls.restSpec_of_body (instantiate_scoped ρ he.1 b (k + 2)) (by simpa using hk)
    (meaning_adm G s.1)
    (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
    (meaning_adm G A) (fun j' U' heap extra hu' hh' hext => restStore_safe harr hu' hh' hext)
  intro j' hj' U' hx' hu' heap hh' r hr args a hargs harr' _
  have hall : ArgsT ((s.1 :: s.2.1).map (meaning G)) j' U' (r :: args) := ⟨hr, hargs⟩
  have hsc := ArgsT_scoped hall
  have hl : args.length = k := by rw [ArgsT_length hargs]; simpa using hk
  have hbeta := instantiate_beta _ (prependArgs_scoped hsc he.1) a b 0
  rw [Nat.zero_add] at hbeta
  rw [show k + 2 = 1 + (r :: args).length by simp; omega, instantiate_args ρ he.1 hsc b 1, hbeta]
  have hWU : WExt (trunc j' (by omega) W) U' := WExt_trans
    (by simpa only [trunc_trunc] using WExt_trunc (Nat.le_of_lt hj') hx) hx'
  have henv := ((he.transfer j' (by omega) U' hWU).prepend hall).push harr'
  exact ih j' U' heap _ (by simpa [List.append_assoc] using henv) hu' hh'

/-- The pair of a signature and its rest-store type, by index. -/
theorem zip_getElem_mem {α β : Type} {L : List α} {As : List β} {i : Nat} (hi : i < L.length)
    (hiA : i < As.length) : (L[i], As[i]) ∈ L.zip As :=
  List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr
    ⟨List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiA⟩)

/-- The named fields and readonly views of an object of one record operand:
a record's, or a dictionary's, whose named members hold beside its index. -/
def namedMembers : Clause α → Option (List (PropKey × α) × List (PropKey × α))
  | .refs fs [] vs _ _ _ => some (fs, vs)
  | .dict fs [] vs _ _ _ _ _ => some (fs, vs)
  | _ => none

/-- A value of a type with named members holds each named field as a cell of
its contract and each view as a location whose contents meet its bound. -/
theorem namedMembers_sem {G : NormalGraph ι} {A : Ty ι} {c : Clause (Ty ι)}
    {fs vs : List (PropKey × Ty ι)} (hr : Represents G A c)
    (hc : namedMembers c = some (fs, vs)) {n W v} (h : meaning G A n W v) :
    recT (ReferenceConjunctions.famsOf (meaning G) fs) n W v ∧
      viewT (ReferenceConjunctions.famsOf (meaning G) vs) n W v := by
  have hs := (represents_sem hr n W v).mp h
  match c, hc with
  | .refs _ [] _ _ _ _, rfl => exact ⟨hs.1.1, hs.2.1⟩
  | .dict _ [] _ _ _ _ _ _, rfl => exact ⟨hs.1.1, hs.2.1⟩

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
  /-- **A function.** Each signature `(receiver, parameters, result)` checks the
  body with its receiver, then its parameters, before the captures. A signature
  may offer more parameters than the code takes: the body is checked at the
  first `arity`, and actuals past them are discarded at binding, as JavaScript
  discards them. So the code also meets a variadic signature whose fixed
  parameters cover its arity, checked at that signature's fixed row
  (`offerRows`): the actuals past them, however many, are discarded. -/
  | funE {Γ : List (Ty ι)} {F : Ty ι} {L : List (Ty ι × List (Ty ι) × Ty ι)}
      {S : List (Ty ι × List (Ty ι) × Ty ι × Ty ι)} {arity : Nat}
      {b : Tm} : Represents G F (.arrs L S) → (∀ p ∈ offerRows L S, arity ≤ p.2.1.length) →
      (∀ p ∈ offerRows L S, HasTy G (bodyFrame arity p Γ) b p.2.2) →
      HasTy G Γ (.make (.closure arity b) .nul) F
  /-- A class value: construct-only code, its body typed at each construct
  signature with `undefined` for the receiver `new` passes. -/
  | ctorE {Γ : List (Ty ι)} {F U : Ty ι} {L : List (List (Ty ι) × Ty ι)} {arity : Nat}
      {b : Tm} :
      Represents G F (.ctors L) → Represents G U .undef → (∀ p ∈ L, arity ≤ p.1.length) →
      (∀ p ∈ L, HasTy G (U :: p.1.take arity ++ Γ) b p.2) →
      HasTy G Γ (.make (.closure arity b .construct) .nul) F
  /-- `new f(args)`: `f` at a construct signature, each actual at its
  parameter. As a call may, `new` may omit trailing positions whose contracts
  admit `undefined`, the value the machine binds there. -/
  | construct {Γ : List (Ty ι)} {f : Tm} {F B : Ty ι} {L : List (List (Ty ι) × Ty ι)}
      {xs : List (Ty ι × Tm)} {Us : List (Ty ι)} :
      HasTy G Γ f F → Represents G F (.ctors L) → (xs.map Prod.fst ++ Us, B) ∈ L →
      (∀ p ∈ xs, HasTy G Γ p.2 p.1) → (∀ A ∈ Us, HasTy G Γ .undef A) →
      HasTy G Γ (.construct f (xs.map Prod.snd)) B
  /-- A callable object: the same allocation as a record, with invocation code
  attached. Its bag is a record like any other, so its fields are named by the
  program rather than fixed here. -/
  | makeCallable {Γ : List (Ty ι)} {F : Ty ι} {L : List (Ty ι × List (Ty ι) × Ty ι)}
      {arity : Nat} {b : Tm} {parts : List (PropKey × Ty ι × Tm)} :
      Represents G F (.callable (parts.map fun p => (p.1, p.2.1)) [] L []) →
      (parts.map Prod.fst).Nodup →
      (∀ p ∈ parts, HasTy G Γ p.2.2 p.2.1) →
      (∀ p ∈ L, arity ≤ p.2.1.length) →
      (∀ p ∈ L, HasTy G (bodyFrame arity p Γ) b p.2.2) →
      HasTy G Γ (.makeAt (.closure arity b) (parts.map Prod.fst)
        (parts.map fun p => p.2.2)) F
  /-- A call writes the actuals it writes, and passes the receiver `r`, typed
  at the selected signature's receiver. `Us` are the trailing positions the
  signature declares and this call omits; each admits `undefined`, which is
  the value the machine binds there. `Us = []` is the exact-arity call. -/
  | callCallable {Γ : List (Ty ι)} {f r : Tm} {F Rt B : Ty ι} {P : List (PropKey × Ty ι)}
      {Ps : List (List (PropKey × Ty ι))} {L : List (Ty ι × List (Ty ι) × Ty ι)}
      {S : List (Ty ι × List (Ty ι) × Ty ι × Ty ι)} {xs : List (Ty ι × Tm)} {Us : List (Ty ι)} :
      HasTy G Γ f F → Represents G F (.callable P Ps L S) →
      (Rt, xs.map Prod.fst ++ Us, B) ∈ L → HasTy G Γ r Rt →
      (∀ p ∈ xs, HasTy G Γ p.2 p.1) → (∀ A ∈ Us, HasTy G Γ .undef A) →
      HasTy G Γ (.invoke f r (xs.map Prod.snd)) B
  | readCallable : HasTy G Γ a F → Represents G F (.callable P Ps L S) → (f, A) ∈ P →
      HasTy G Γ (.readAt f a) A
  | writeCallable : HasTy G Γ a F → Represents G F (.callable P Ps L S) → (f, A) ∈ P →
      HasTy G Γ b A → Represents G N .nul → HasTy G Γ (.writeAt f a b) N
  | app {Γ : List (Ty ι)} {f r : Tm} {F Rt B : Ty ι} {L : List (Ty ι × List (Ty ι) × Ty ι)}
      {S : List (Ty ι × List (Ty ι) × Ty ι × Ty ι)} {xs : List (Ty ι × Tm)} {Us : List (Ty ι)} :
      HasTy G Γ f F → Represents G F (.arrs L S) →
      (Rt, xs.map Prod.fst ++ Us, B) ∈ L → HasTy G Γ r Rt →
      (∀ p ∈ xs, HasTy G Γ p.2 p.1) → (∀ A ∈ Us, HasTy G Γ .undef A) →
      HasTy G Γ (.invoke f r (xs.map Prod.snd)) B
  | letE : HasTy G Γ a A → HasTy G (A :: Γ) b B → HasTy G Γ (.letE a b) B
  /-- **Allocation.** One object, one fresh location per named field. The field
  names are distinct, which is what makes the object a map from them. Its own
  keys are exactly those names, so any bound holding them holds of it. -/
  | alloc {parts : List (PropKey × Ty ι × Tm)} {ks : List (List PropKey)} :
      (parts.map Prod.fst).Nodup →
      (∀ p ∈ parts, HasTy G Γ p.2.2 p.2.1) →
      Represents G Ref (.refs (parts.map fun p => (p.1, p.2.1)) [] [] [] [] ks) →
      (∀ K ∈ ks, ∀ p ∈ parts, p.1 ∈ K) →
      HasTy G Γ (.makeAt .absent (parts.map Prod.fst) (parts.map fun p => p.2.2)) Ref
  /-- A named field, of a record or of a dictionary, reads at its contract. -/
  | read : HasTy G Γ a Ref → Represents G Ref c → namedMembers c = some (fs, vs) →
      (f, A) ∈ fs → HasTy G Γ (.readAt f a) A
  /-- A view field reads at its bound: a capability, never a write permission. -/
  | readView : HasTy G Γ a Ref → Represents G Ref c → namedMembers c = some (fs, vs) →
      (f, A) ∈ vs → HasTy G Γ (.readAt f a) A
  /-- **A read through the prototype.** A key outside one of the object's key
  bounds is not its own, so the read continues at the prototype, which the
  object holds under the reserved key at `P`; the prototype's field or view
  for the key gives the type. -/
  | readProto {a : Tm} {Ref P : Ty ι} {fs vs : List (PropKey × Ty ι)} {os : List (OptionalField (Ty ι))}
      {ms : List (MethodMembers.Sig (Ty ι))} {ks : List (List PropKey)} {K : List PropKey}
      {gs ws : List (PropKey × Ty ι)} {os' : List (OptionalField (Ty ι))}
      {ms' : List (MethodMembers.Sig (Ty ι))}
      {ks' : List (List PropKey)} {f : PropKey} {A : Ty ι} :
      HasTy G Γ a Ref → Represents G Ref (.refs fs [] vs os ms ks) → K ∈ ks → f ∉ K →
      (CallArguments.protoField, P) ∈ fs ++ vs → Represents G P (.refs gs [] ws os' ms' ks') →
      (f, A) ∈ gs ++ ws → HasTy G Γ (.readAt f a) A
  /-- An optional field, writable or readonly, reads at its type or, where the
  object lacks the key, as `undefined`. -/
  | readOptional {a : Tm} {Ref : Ty ι} {fs vs : List (PropKey × Ty ι)} {os : List (OptionalField (Ty ι))}
      {ms : List (MethodMembers.Sig (Ty ι))} {ks : List (List PropKey)} {f : PropKey} {r : Bool}
      {A U : Ty ι} :
      HasTy G Γ a Ref → Represents G Ref (.refs fs [] vs os ms ks) → ⟨f, r, A⟩ ∈ os →
      Represents G U .undef → HasTy G Γ (.readAt f a) (A ++ U)
  /-- A dictionary read may miss even when every present value has type `A`.
  A string index signature says nothing of a symbol-keyed field, so only a
  string key is read through one. -/
  | readDict {f : String} : HasTy G Γ a Ref → Represents G Ref (.dict fs [] vs ix os ms ks cs) →
      A ∈ ix → Represents G U .undef →
      HasTy G Γ (.readAt (.str f) a) (A ++ U)
  | indexDict : HasTy G Γ a Ref → Represents G Ref (.dict fs [] vs ix os ms ks cs) →
      HasTy G Γ key K → Represents G K .str →
      A ∈ ix → Represents G U .undef →
      HasTy G Γ (.indexAt a key) (A ++ U)
  | write : HasTy G Γ a Ref → Represents G Ref (.refs fs [] vs os ms ks) → (f, A) ∈ fs →
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
  contract: into the element's location, or a fresh one the store records.
  The index is at most the required length, so the write is in bounds or
  appends at the end: it never leaves a hole, and the store stays dense. -/
  | setElem {Γ : List (Ty ι)} {a i v : Tm} {L I A : Ty ι} {T : Tuple (Ty ι)} {b : UInt64} {k : Nat} :
      HasTy G Γ a L → Represents G L (.list T []) → HasTy G Γ i I → Represents G I (.numLit b) →
      indexOfBits b = some k → positionTy T k = some A → k ≤ T.required.length →
      T.readonly = false → HasTy G Γ v A → HasTy G Γ (.setElem a i v) L
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
  /-- **A variadic function.** Each signature `(receiver, fixed, element,
result)` checks the body with, in slot 0, a fresh store holding the actuals
past the fixed ones at the rest's tuple contract, then the fixed parameters
and the receiver. -/
  | funRest {Γ : List (Ty ι)} {F : Ty ι} {L : List (Ty ι × List (Ty ι) × Ty ι × Ty ι)}
      {As : List (Ty ι)} {n : Nat} {b : Tm} :
      Represents G F (.arrs [] L) → L.length = As.length →
      (∀ p ∈ L.zip As, p.1.2.1.length = n ∧ RestStore G p.2 p.1.2.2.1) →
      (∀ p ∈ L.zip As, HasTy G (p.2 :: p.1.1 :: p.1.2.1 ++ Γ) b p.1.2.2.2) →
      HasTy G Γ (.make (.variadic n b) .nul) F
  /-- **A variadic callable object.** The bag is allocated as a record's is,
  and the code is variadic: each signature's body is checked as `funRest`
  checks it. -/
  | makeCallableRest {Γ : List (Ty ι)} {F : Ty ι} {parts : List (PropKey × Ty ι × Tm)}
      {L : List (Ty ι × List (Ty ι) × Ty ι × Ty ι)} {As : List (Ty ι)} {n : Nat} {b : Tm} :
      Represents G F (.callable (parts.map fun p => (p.1, p.2.1)) [] [] L) →
      (parts.map Prod.fst).Nodup → (∀ p ∈ parts, HasTy G Γ p.2.2 p.2.1) →
      L.length = As.length →
      (∀ p ∈ L.zip As, p.1.2.1.length = n ∧ RestStore G p.2 p.1.2.2.1) →
      (∀ p ∈ L.zip As, HasTy G (p.2 :: p.1.1 :: p.1.2.1 ++ Γ) b p.1.2.2.2) →
      HasTy G Γ (.makeAt (.variadic n b) (parts.map Prod.fst) (parts.map fun p => p.2.2)) F
  /-- **A copy of a spread.** `[...s]` allocates a fresh store holding the
  elements of the store `s` evaluates to, read where it is written. -/
  | arrCopy {Γ : List (Ty ι)} {s : Tm} {S T E : Ty ι} :
      HasTy G Γ s S → SpreadsInto G S E → Represents G T (.list ⟨[], [], some E, false⟩ []) →
      HasTy G Γ (.arrLit [.spread s]) T
  /-- **A variadic call.** The fixed actuals meet the selected signature's
  parameters, less trailing ones `Us` the call omits, each admitting
  `undefined`, and a call that omits a fixed position writes nothing further.
  The further parts fit the rest (`RestParts`): with a spread, each part is at
  the element rest's element or spreads into it; without one, the parts are
  at the positions of the rest's tuple contract. The signature may be a
  function's or a callable object's. -/
  | callRest {Γ : List (Ty ι)} {f r : Tm} {F Rt : Ty ι}
      {xs : List (Ty ι × Tm)} {Us : List (Ty ι)} {P B : Ty ι} {parts : List (Bool × Ty ι × Tm)} :
      HasTy G Γ f F → (Rt, xs.map Prod.fst ++ Us, P, B) ∈ restSigs G F → HasTy G Γ r Rt →
      (∀ p ∈ xs, HasTy G Γ p.2 p.1) → (∀ A ∈ Us, HasTy G Γ .undef A) → (Us = [] ∨ parts = []) →
      (∀ p ∈ parts, HasTy G Γ p.2.2 p.2.1) →
      RestParts G P (parts.map fun p => (p.1, p.2.1)) →
      HasTy G Γ (.invoke f r (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2))) B
  /-- **A bound function.** `.bind` saved its target, receiver and prefix in
  slots; allocation stores those values, as they are, in a forwarding
  descriptor with no fields. The result takes the positions the target's
  selected signature has after the prefix, with any receiver: the one it is
  later called with is dropped for the saved one. -/
  | bindE {Γ : List (Ty ι)} {F T Rt R Rc : Ty ι} {t r : Nat} {slots : List Nat}
      {Ps Ds : List (Ty ι)} :
      Γ[t]? = some T → (Rt, Ps ++ Ds, R) ∈ callSigs G T →
      Γ[r]? = some Rt → slots.map (Γ[·]?) = Ps.map some →
      Represents G F (.arrs [(Rc, Ds, R)] []) →
      HasTy G Γ (.makeAt (.bound (.var t) (.var r) (slots.map .var)) [] []) F
  /-- **A bound variadic function.** As `bindE`, for a variadic signature of
  the target whose rest is an element rest: the prefix takes its first fixed
  positions, and past them the element; the result is the positions left, then
  the rest, at any receiver. -/
  | bindRestE {Γ : List (Ty ι)} {F T Rt E El R Rc : Ty ι} {t r : Nat} {slots : List Nat}
      {Ps Qs : List (Ty ι)} :
      Γ[t]? = some T → (Rt, Ps, E, R) ∈ restSigs G T → restElem G E = some El →
      Γ[r]? = some Rt → slots.map (Γ[·]?) = Qs.map some →
      Qs = Ps.take slots.length ++ List.replicate (slots.length - Ps.length) El →
      Represents G F (.arrs [] [(Rc, Ps.drop slots.length, E, R)]) →
      HasTy G Γ (.makeAt (.bound (.var t) (.var r) (slots.map .var)) [] []) F
  /-- **A member bound to its host.** The member is read from the object in a
  slot, before anything else runs, and bound to that same object: the bound
  function meets the member's signatures whatever receiver it is later given,
  and each fixed signature one of them covers. This is how a method call
  `o.m(args)` keeps JavaScript's order, reading the member before the actuals,
  while the member's contract stays host-relative. -/
  | bindMember {Γ : List (Ty ι)} {F O : Ty ι} {i : Nat} {k : PropKey}
      {m : MethodMembers.Sig (Ty ι)} {L : List (Ty ι × List (Ty ι) × Ty ι)}
      {S : List (Ty ι × List (Ty ι) × Ty ι × Ty ι)} :
      Γ[i]? = some O → memberOf G O k = some m → Represents G F (.arrs L S) →
      (∀ q ∈ L, ∃ c ∈ m.calls, CoveredCall G q c) →
      (∀ s ∈ S, (s.2.1, s.2.2.1, s.2.2.2) ∈ m.rests) →
      HasTy G Γ (.letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])) F
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
  | @funE Γ F L S arity b hr hlen hb ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, Nat.zero_add]
    have hcode := invocation_of_body he hlen (fun p hp => ih p hp)
    have hs := make_closure_rule nulT_adm arity n W h _ .nul hcode
      (S := S.map fun s => (meaning G s.1, s.2.1.map (meaning G),
        argMeaning G s.2.2.1, meaning G s.2.2.2))
      (by
        intro s hs
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
        have hrow : (q.1, q.2.1, q.2.2.2) ∈ offerRows L S :=
          List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
        exact ⟨by simpa using hlen _ hrow, List.mem_map.mpr ⟨_, hrow, rfl⟩⟩)
      rfl hw hh rfl
    exact Safe_mono n (fun k _ U v hv => (represents_sem hr k U v).mpr
      ⟨⟨hv.2.1.1, fun p hp => hv.2.1.2 p (by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact List.mem_map.mpr ⟨q, List.mem_append_left _ hq, rfl⟩)⟩, hv.2.2⟩) W h _ hs
  | @ctorE Γ F U L arity b hr hu hlen hb ih =>
    intro n W h ρ he hw hh
    simp only [instantiate, Nat.zero_add]
    have hcode := invocation_of_body (L := L.map fun p => (U, p.1, p.2)) he
      (by intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; exact hlen q hq)
      (by intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp; exact ih q hq)
    apply make_rule nulT_adm n W h _ .nul rfl hw hh rfl
    intro j hj V hx _
    refine (represents_sem hr j V _).mpr ⟨ctorsT_of_body ?_ ?_, ctorRestsT_nil ?_⟩
    · simpa [Scoped, Nat.add_comm] using hcode.1
    · intro p hp i hi V' hx' hu' heap hok args ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hWV : WExt (trunc i (by omega) W) V' := WExt_trans
        (by simpa only [trunc_trunc] using WExt_trunc (Nat.le_of_lt hi) hx) hx'
      exact hcode.2 _ (List.mem_map.mpr ⟨(U, q.1, q.2), List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩)
        i (by omega) V' hWV hu' heap hok .undef ((represents_sem hu i V' _).mpr rfl) args
        (by simpa using ha)
    · exact ⟨_, _, _, rfl, by simpa [Scoped, Nat.add_comm] using hcode.1⟩
  | @construct Γ f F B L xs Us hf hr hp hx hu ihf ihx ihu =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := construct_safe (B := meaning G B)
      (xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)) (Us.map (meaning G))
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_adm G q.1)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_valOnly G q.1)
      (by intro A hA; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
      hw hh (f := instantiate 0 ρ f) ?_ ?_ ?_
    · simpa only [List.map_map, Function.comp_def] using hs
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      simpa only [List.map_map, Function.comp_def, List.map_append] using
        ctorsT_select ((represents_sem hr k U v).mp hv).1
          (List.mem_map.mpr ⟨(xs.map Prod.fst ++ Us, B), hp,
            by simp [List.map_append, List.map_map, Function.comp_def]⟩)
    · intro p hp'
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp'
      intro j hj U hx hu' heap hok
      exact ihx q hq j U heap ρ (he.transfer j hj U hx) hu' hok
    · intro A hA
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hA
      intro j hj U hx hu' heap hok
      exact ihu q hq j U heap ρ (he.transfer j hj U hx) hu' hok
  | @makeCallable Γ F L arity b parts hr hnd hp hlen hb ih ihb =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def, Nat.zero_add]
    have hcode := invocation_of_body he hlen (fun p hp => ihb p hp)
    have hmap : (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2)).map Prod.snd
        = parts.map fun x => instantiate 0 ρ x.2.2 := by
      simp [List.map_map, Function.comp_def]
    rw [← hmap]
    apply bind_list (parts.map fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))
      (by intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; exact meaning_adm G r.2.1)
      (fun args => .makeAt (.closure arity (instantiate (arity + 1) ρ b)) (parts.map Prod.fst) args)
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
    have hc : InvocationSpec arity
        (L.map fun p => (meaning G p.1, p.2.1.map (meaning G), meaning G p.2.2))
        j U (instantiate (arity + 1) ρ b) :=
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
  | @callCallable Γ f r F Rt B P Ps L S xs Us hf hr hp hrt ha hu ihf ihrt iha ihu =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := call_safe_short (Rc := meaning G Rt) (B := meaning G B) (f := instantiate 0 ρ f)
      (r := instantiate 0 ρ r)
      (xs.map fun p => (meaning G p.1,instantiate 0 ρ p.2)) (Us.map (meaning G))
      (meaning_adm G Rt) (meaning_valOnly G Rt)
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
          (List.mem_map.mpr ⟨(Rt, xs.map Prod.fst ++ Us,B), hp,
            by simp [List.map_append, List.map_map, Function.comp_def]⟩)
    · intro j hj U hx hu' heap hok
      exact ihrt j U heap ρ (he.transfer j hj U hx) hu' hok
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
  | @app Γ f r F Rt B L S xs Us hf hr hp hrt ha hu ihf ihrt iha ihu =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := call_safe_short (Rc := meaning G Rt) (B := meaning G B) (f := instantiate 0 ρ f)
      (r := instantiate 0 ρ r)
      (xs.map fun p => (meaning G p.1,instantiate 0 ρ p.2)) (Us.map (meaning G))
      (meaning_adm G Rt) (meaning_valOnly G Rt)
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
          (List.mem_map.mpr ⟨(Rt, xs.map Prod.fst ++ Us,B), hp,
            by simp [List.map_append, List.map_map, Function.comp_def]⟩)
    · intro j hj U hx hu' heap hok
      exact ihrt j U heap ρ (he.transfer j hj U hx) hu' hok
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
  | @alloc Γ Ref parts ks hnd hp hr hbound ih =>
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
    refine (represents_sem hr k V _).mpr ⟨⟨?_, by simp⟩, fun f T hm => by simp [ReferenceConjunctions.famsOf] at hm,
      ⟨by simpa [ReferenceConjunctions.famsOf] using optT_nil, MethodMembers.methodT_nil _ _ _,
        fun K hK => ownKeysT_slots fun n hn => by
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
          exact hbound K hK p hp⟩⟩
    have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
        = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
      simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
    rw [hfam]
    exact hrec
  | @read Γ a Ref c fs vs f A ha hr hc hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ :=
      recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) (namedMembers_sem hr hc ha').1
    exact read_rule (meaning_valOnly G A) j U heap l hu hok hf hl hag
  | @readView Γ a Ref c fs vs f A ha hr hc hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ :=
      viewT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) (namedMembers_sem hr hc ha').2
    exact read_view_rule (meaning_valOnly G A) j U heap l hu hok hf hl hag
  | @readProto Γ a Ref P fs vs os ms ks K gs ws os' ms' ks' f A ha hr hK hf hpr hP hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    have hs := (represents_sem hr j U v).mp ha'
    have hloc : ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr j), v = .objAt flds .absent ∧
        flds.lookup CallArguments.protoField = some l ∧ lookup U l = some c ∧
        ∀ (i : Nat) (hi : i < j) (V : WorldT i) (u : Val), c i hi V u → meaning G P i V u := by
      rcases List.mem_append.mp hpr with hpr | hpr
      · obtain ⟨flds, l, c, he, hf', hl, hag⟩ :=
          recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨P, hpr, rfl⟩) hs.1.1
        exact ⟨flds, l, c, he, hf', hl, fun i hi V u hu => (hag i hi V u).mp hu⟩
      · exact viewT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨P, hpr, rfl⟩) hs.2.1
    obtain ⟨flds, l, c, rfl, hpf, hl, hag⟩ := hloc
    have hmiss := ownKeysT_lookup (hs.2.2.2.2 K hK) hf
    apply read_proto_rule j U heap l hu hok hmiss hpf hl hag
    intro i V h' hV hh' u hu
    have hp := (represents_sem hP i V u).mp hu
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨flds', l', c', rfl, hf', hl', hag'⟩ :=
        recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) hp.1.1
      exact read_rule (meaning_valOnly G A) i V h' l' hV hh' hf' hl' hag'
    · obtain ⟨flds', l', c', rfl, hf', hl', hag'⟩ :=
        viewT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩) hp.2.1
      exact read_view_rule (meaning_valOnly G A) i V h' l' hV hh' hf' hl' hag'
  | @readOptional Γ a Ref fs vs os ms ks f r A U ha hr hm hUnd ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj V hx hv heap v hok hval ha'
    have hs := (represents_sem hr j V v).mp ha'
    obtain ⟨flds, rfl, _⟩ := hs.1.1
    apply Safe_mono j (fun k _ X u hu => (meaning_append G A U k X u).mpr
      (hu.elim Or.inl (fun h => Or.inr ((represents_sem hUnd k X u).mpr h)))) V heap _
      (read_optional_rule (meaning_valOnly G A) j V heap hv hok
        (optT_no_proto (List.mem_map_of_mem hm) hs.2.2.1)
        (fun l hl => by
          obtain ⟨c, hc, hag⟩ := optT_present (List.mem_map_of_mem hm) hs.2.2.1 hl
          exact ⟨c, hc, fun i hi U u hu => (hag i hi U u).1 hu⟩))

  | @readDict Γ a Ref fs vs ix os ms ks cs A U f ha hr hm hUnd ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt (.str f)) Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj V hx hv heap v hok hval ha'
    have hd := ((represents_sem hr j V v).mp ha').2.2.1.1 A hm
    obtain ⟨flds, rfl, _⟩ := ((represents_sem hr j V v).mp ha').1.1
    apply Safe_mono j (fun k _ X u hu => (meaning_append G A U k X u).mpr
      (hu.elim Or.inl (fun h => Or.inr ((represents_sem hUnd k X u).mpr h)))) V heap _
      (read_dict_rule (meaning_valOnly G A) j V heap hv hok hd)
  | @indexDict Γ a Ref fs vs ix os ms ks cs key K A U ha hr hk hStr hm hUnd iha ihk =>
    intro n W h ρ he hw hh
    apply bind (fun v => .indexAt v (instantiate 0 ρ key)) Step.indexC1 n W h _ hw hh
      (iha n W h ρ he hw hh)
    intro j hj V hx hv heap av hok hav ha'
    apply bind (Tm.indexAt av) (Step.indexC2 hav) j V heap _ hv hok
      (ihk j V heap ρ (he.transfer j hj V hx) hv hok)
    intro k hk X hy hX heap' kv hok' hkv hk'
    have ha'' := (meaning_adm G Ref).mono k _ X hy av
      ((meaning_adm G Ref).down_le j k hk V av ha')
    obtain ⟨s, rfl⟩ := (represents_sem hStr k X kv).mp hk'
    have hd := ((represents_sem hr k X av).mp ha'').2.2.1.1 A hm
    obtain ⟨flds, rfl, _⟩ := ((represents_sem hr k X av).mp ha'').1.1
    apply Safe_mono k (fun i _ Y u hu => (meaning_append G A U i Y u).mpr
      (hu.elim Or.inl (fun h => Or.inr ((represents_sem hUnd i Y u).mpr h)))) X heap' _
      (index_dict_rule (meaning_valOnly G A) k X heap' hX hok' hd)
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
    obtain ⟨ls, rfl, -, -, -, hreq, -, -⟩ := ((represents_sem hr m V av).mp ha'').1
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
    obtain ⟨ls, rfl, -, -, -, -, hopt, hrest⟩ := ((represents_sem hr m V av).mp ha'').1
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
    obtain ⟨ls, rfl, -, -, -, -, -, hrest⟩ := ((represents_sem hr m V av).mp ha'').1
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
  | @setElem Γ a i v L I A T b k ha hr hi hI hk hA hkle hro hv iha ihi ihv =>
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
    obtain ⟨ls, rfl, -, hlen, -, hreq, hopt, hrest⟩ := hlist
    simp only [tupleFams, List.length_map, List.getElem?_map] at hreq hopt hrest hlen
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
      · omega
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
      · exact expand_sem_mpr ⟨_, expand_sub ht, rfl⟩
      · exact expand_sem_mpr ⟨_, expand_sub hf, rfl⟩
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
  | @write Γ a Ref fs vs os ms ks f A b N ha hr hm hb hn iha ihb =>
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
    cases q <;> simp only [clauseSem, semWithArgs] at hvalue <;> subst v
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
      · have refined := henv.refine hi ((represents_sem hT (k+1) W (ρ i)).mpr (by simpa [hv, clauseSem, semWithArgs, boolT]))
        rw [hv]
        refine Or.inr ⟨trunc k (Nat.le_succ k) W,h,instantiate 0 ρ t,WExt_refl _,
          WorldAdm_trunc _ hw,.iteT,HeapOk_trunc k W h hh,?_⟩
        exact iht k _ h ρ (refined.transfer k (Nat.le_succ k) _ (WExt_refl _))
          (WorldAdm_trunc _ hw) (HeapOk_trunc k W h hh)
      · have refined := henv.refine hi ((represents_sem hF (k+1) W (ρ i)).mpr (by simpa [hv, clauseSem, semWithArgs, boolT]))
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
    have hinv : Invocable (.obj h.length (.variadic k (instantiate (k + 2) ρ b))) :=
      ⟨_, _, rfl, rfl, by simpa [Scoped] using instantiate_scoped ρ he.1 b (k + 2)⟩
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
      (fun args => .makeAt (.variadic k (instantiate (k + 2) ρ b)) (parts.map Prod.fst) args)
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
        (.variadic k (instantiate (k + 2) ρ b))) :=
      ⟨_, _, rfl, rfl, by simpa [Scoped] using instantiate_scoped ρ he.1 b (k + 2)⟩
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
  | @callRest Γ f r F Rt xs Us P B parts hf hmem hrt hx hu hshort hp hparts
      ihf ihrt ihx ihu ihp =>
    intro n W h ρ he hw hh
    have hfF : Safe (restsT [(meaning G Rt, (xs.map Prod.fst ++ Us).map (meaning G), argMeaning G P,
        meaning G B)]) n W h (instantiate 0 ρ f) :=
      Safe_mono n (fun m _ U v hv => restsT_of_restSigs hmem hv) W h _ (ihf n W h ρ he hw hh)
    unfold RestParts at hparts
    split at hparts
    · -- A spread: the rest is an element rest.
      rename_i hany
      split at hparts
      · rename_i E hel
        have hUs : Us = [] := by
          rcases hshort with h | h
          · exact h
          · subst h; simp at hany
        subst hUs
        have hterm : instantiate 0 ρ (.invoke f r
              (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2)))
            = .invoke (instantiate 0 ρ f) (instantiate 0 ρ r)
              ((xs.map fun p => (meaning G p.1, instantiate 0 ρ p.2)).map Prod.snd ++
              (parts.map fun p => ((if p.1 then some (meaning G p.2.1) else none),
                instantiate 0 ρ p.2.2)).map RestCalls.partTerm) := by
          simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map,
            Function.comp_def, instantiate_spreadTerm]
          congr 2
          apply List.map_congr_left
          intro p _
          rcases p with ⟨_ | _, A, t⟩ <;> rfl
        have hpart : ∀ p ∈ parts, if p.1 then SpreadsInto G p.2.1 E else p.2.1 = E :=
          fun p hp' => hparts (p.1, p.2.1) (List.mem_map_of_mem hp')
        rw [hterm]
        apply rest_call_safe (Rc := meaning G Rt) (Ps := xs.map fun p => meaning G p.1)
          (E := meaning G E) (P := argMeaning G P) (R := meaning G B)
          (meaning_adm G Rt)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q.1)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q.1)
          (meaning_adm G E) (meaning_valOnly G E) (argMeaning_adm G P)
          (fun k W xs hxs => (restElem_args hel).mpr hxs)
          _ (by simp [List.map_map, Function.comp_def]) _
          (by
            intro q hq S hS
            obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
            rcases p with ⟨_ | _, A, t⟩
            · simp at hS
            · simp only [if_true, Option.some.injEq] at hS
              subst hS
              have := hpart _ hp'
              simp only [if_true] at this
              exact ⟨meaning_adm G A, spreadsInto_sound this⟩)
          hw hh (by simpa [List.map_map, Function.comp_def] using hfF)
        · intro j hj U hxU hu heap hok
          exact ihrt j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro q hq j hj U hxU hu heap hok
          obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro q hq j hj U hxU hu heap hok
          obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          rcases p with ⟨_ | _, A, t⟩
          · have hA : A = E := by simpa using hpart _ hp'
            subst hA
            exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
          · exact ihp _ hp' j U heap ρ (he.transfer j hj U hxU) hu hok
      · exact hparts.elim
    · -- No spread: the parts are at the positions of the rest's tuple contract.
      rename_i hany
      split at hparts
      · rename_i T hPT
        obtain ⟨hreq, hbound, hpos⟩ := hparts
        simp only [List.any_map, List.any_eq_true, not_exists, not_and, Function.comp_def,
          Bool.not_eq_true] at hany
        have hterm : instantiate 0 ρ (.invoke f r
              (xs.map Prod.snd ++ parts.map fun p => spreadTerm (p.1, p.2.2)))
            = .invoke (instantiate 0 ρ f) (instantiate 0 ρ r)
              ((xs.map (fun p => (meaning G p.1, instantiate 0 ρ p.2)) ++
                parts.map (fun p => (meaning G p.2.1, instantiate 0 ρ p.2.2))).map Prod.snd) := by
          simp only [instantiate, instantiateArgs_eq_map, List.map_append, List.map_map,
            Function.comp_def, instantiate_spreadTerm]
          congr 2
          apply List.map_congr_left
          intro p hp'
          simp [spreadTerm, hany p hp']
        rw [hterm]
        apply pack_call_safe (Rc := meaning G Rt) (Ps := xs.map fun p => meaning G p.1)
          (Us := Us.map (meaning G)) (Qs := parts.map fun p => meaning G p.2.1)
          (P := argMeaning G P) (R := meaning G B)
          (meaning_adm G Rt)
          (by
            intro A hA
            rcases List.mem_append.mp hA with hA | hA <;>
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA <;> exact meaning_adm G _)
          (by
            intro A hA
            rcases List.mem_append.mp hA with hA | hA <;>
              obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA <;> exact meaning_valOnly G _)
          (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
          (fun k W extra ha => restParts_pack hPT (Qs := parts.map (·.2.1))
            (by simpa using hreq) (by simpa using hbound)
            (by
              intro i hi
              have := hpos i (by simpa using hi)
              simpa [List.getElem?_map, Option.map_map, Function.comp_def] using this)
            (by simpa [List.map_map, Function.comp_def] using ha))
          _ (by simp [List.map_map, Function.comp_def])
          (by rcases hshort with h | h <;> simp [h])
          hw hh (by simpa [List.map_map, Function.comp_def] using hfF)
        · intro j hj U hxU hu heap hok
          exact ihrt j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro q hq j hj U hxU hu heap hok
          rcases List.mem_append.mp hq with hq | hq <;> obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
          · exact ihx p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
          · exact ihp p hp' j U heap ρ (he.transfer j hj U hxU) hu hok
        · intro A hA j hj U hxU hu' heap hok
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hA
          exact ihu q hq j U heap ρ (he.transfer j hj U hxU) hu' hok
      · exact hparts.elim
  | @bindE Γ F T Rt R Rc t r saved Ps Ds ht hsig hr hpre hF =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def,
      Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ m =>
      have hcall := callsT_of_callSigs hsig (he.2 t T ht)
      simp only [List.map_append, List.map_map, Function.comp_def] at hcall
      have hpv := ArgsT_slots he hpre
      have hbound := callsT_bound (Rc := meaning G Rc) (fs := [])
        (meaning_adm G Rt) (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
        (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
        hcall (meaning_value (he.2 r Rt hr)).1 (he.1 r) (he.2 r Rt hr) hpv
        (ArgsT_values (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q) hpv)
        (by intro a ha; obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha; exact he.1 q)
      have hdown := (callsT_adm _).down m W _ hbound
      refine Or.inr ⟨trunc m (Nat.le_succ m) W, h,
        .objAt [] (.bound (ρ t) (ρ r) (saved.map ρ)), WExt_refl _, WorldAdm_trunc _ hw, ?_,
        HeapOk_trunc m W h hh, value_safe _ _ _ _ _ rfl ?_⟩
      · simpa [Model.slots] using (Step.makeFields (h := h) (ns := []) (vs := [])
          (c := .bound (ρ t) (ρ r) (saved.map ρ)) (by simp) rfl)
      · exact (represents_sem hF m _ _).mpr ⟨by simpa using hdown, hdown.1, by simp⟩
  | @bindRestE Γ F T Rt E El R Rc t r saved Ps Qs ht hsig hel hr hpre hQs hF =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def,
      Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    cases n with
    | zero => trivial
    | succ m =>
      have hrest := restsT_of_restSigs hsig (he.2 t T ht)
      have hpv := ArgsT_slots he hpre
      subst hQs
      have hlen : (saved.map ρ).length = saved.length := List.length_map _
      have hvals := ArgsT_values (by
        intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_valOnly G q) hpv
      have hsplit := ArgsT_take_drop Ps.length hpv
      rw [← List.map_take, ← List.map_drop, (prefix_take_drop Ps saved.length El).1,
        (prefix_take_drop Ps saved.length El).2, List.map_replicate] at hsplit
      have hpv' : ArgsT ((Ps.map (meaning G)).take (saved.map ρ).length) (m + 1) W
          ((saved.map ρ).take (Ps.map (meaning G)).length) := by
        simpa [List.map_take, hlen] using hsplit.1
      have hext : ∀ j (hj : j ≤ m + 1) (U : WorldT j), WExt (trunc j hj W) U →
          ∀ ys, argMeaning G E j U ys →
            argMeaning G E j U ((saved.map ρ).drop (Ps.map (meaning G)).length ++ ys) := by
        intro j hj U hx ys hy
        refine mixed_restElem_append hel (fun u hu => ?_) hy
        have hu' := ArgsT_replicate_all hsplit.2 u (by simpa using hu)
        exact (meaning_adm G El).transfer hu' j hj U hx
      have hbound := restsT_bound (Rc := meaning G Rc) (fs := [])
        (meaning_adm G Rt) (by intro A hA; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G q)
        (argMeaning_adm G E) hrest (meaning_value (he.2 r Rt hr)).1 (he.1 r) (he.2 r Rt hr) hpv'
        hext hvals (by intro a ha; obtain ⟨q, _, rfl⟩ := List.mem_map.mp ha; exact he.1 q)
      have hdown := (restsT_adm _).down m W _ hbound
      refine Or.inr ⟨trunc m (Nat.le_succ m) W, h,
        .objAt [] (.bound (ρ t) (ρ r) (saved.map ρ)), WExt_refl _, WorldAdm_trunc _ hw, ?_,
        HeapOk_trunc m W h hh, value_safe _ _ _ _ _ rfl ?_⟩
      · simpa [Model.slots] using (Step.makeFields (h := h) (ns := []) (vs := [])
          (c := .bound (ρ t) (ρ r) (saved.map ρ)) (by simp) rfl)
      · refine (represents_sem hF m _ _).mpr ⟨⟨hdown.1, by simp⟩, ?_⟩
        simpa [List.map_drop, hlen] using hdown
  | @bindMember Γ F O i k m L S hi hmo hF hL hS =>
    intro n W h ρ he hw hh
    obtain ⟨hkey, hmem⟩ := memberOf_at hmo (he.2 i O hi)
    have hscope : Scoped 0 (ρ i) := he.1 i
    have hvalρ : isVal (ρ i) = true := (meaning_value (he.2 i O hi)).1
    have hterm : instantiate 0 ρ
        (.letE (.readAt k (.var i)) (.makeAt (.bound (.var 0) (.var (i + 1)) []) [] [])) =
        .letE (.readAt k (ρ i)) (.makeAt (.bound (.var 0) (ρ i) []) [] []) := by
      simp [instantiate, instantiateArgs_eq_map]
    rw [hterm]
    have hread : Safe (MethodMembers.onHost (ρ i) (MethodMembers.Member.of (meaning G) (argMeaning G) m))
        n W h (.readAt k (ρ i)) := by
      have := member_read_safe hw hh hmem
      rwa [show (MethodMembers.Member.of (meaning G) (argMeaning G) m).key = k from hkey] at this
    apply bind (fun a => Tm.letE a (.makeAt (.bound (.var 0) (ρ i) []) [] [])) Step.letC
      n W h _ hw hh hread
    intro j hj U hx hu h' u hok hval hon
    cases j with
    | zero => trivial
    | succ p =>
      apply let_rule _ u hval p U h' hu hok
      have hsub : subst 0 u (.makeAt (.bound (.var 0) (ρ i) []) [] []) =
          .makeAt (.bound u (ρ i) []) [] [] := by
        simp [subst, substArgs_eq_map, subst_above hscope (Nat.zero_le 0)]
      rw [hsub]
      cases p with
      | zero => trivial
      | succ q =>
        have hinv : Invocable (.objAt [] (.bound u (ρ i) [])) :=
          ⟨[], _, rfl, rfl, by simp only [Scoped, scopedArgs_iff]; exact ⟨hon.1.1.scoped, hscope, by simp⟩⟩
        have hcalls : callsT (L.map fun p => (meaning G p.1, p.2.1.map (meaning G), meaning G p.2.2))
            (q + 2) U (.objAt [] (.bound u (ρ i) [])) := by
          refine callsT_of_signatures hinv fun x hx => ?_
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          obtain ⟨c, hc, hlen, hps, pr, hpr⟩ := hL y hy
          have hc' := callsT_select hon.1 (List.mem_map_of_mem (List.mem_map_of_mem hc))
          have hle := CoveredCall.params hlen hps
          have ht : callsT [(MethodMembers.hostT (ρ i), y.2.1.map (meaning G), meaning G y.2.2)]
              (q + 2) U u :=
            ⟨hc'.1, fun p hp => by
              cases List.mem_singleton.mp hp
              exact (hc'.2 _ (List.mem_singleton_self _)).weaken (fun _ _ _ r h => h)
                (fun _ _ _ args ha => ArgsShort_mono hle ha)
                (fun m _ V w hw => PositiveCertificates.accepted hpr m V w hw)⟩
          exact callsT_bound (Ps := []) (MethodMembers.hostT_adm _) (by simp)
            (fun A hA => by obtain ⟨b, -, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G b)
            ht hvalρ hscope rfl trivial (by simp [CallArguments.Values]) (by simp)
        have hrests : restsT (S.map fun s => (meaning G s.1, s.2.1.map (meaning G), argMeaning G s.2.2.1,
            meaning G s.2.2.2)) (q + 2) U (.objAt [] (.bound u (ρ i) [])) := by
          refine restsT_of_signatures hinv fun x hx => ?_
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          have ht := restsT_select hon.2 (List.mem_map_of_mem (List.mem_map_of_mem (hS y hy)))
          have hb := restsT_bound (Rc := meaning G y.1) (pvs := []) (fs := [])
            (MethodMembers.hostT_adm _)
            (fun A hA => by obtain ⟨b, -, rfl⟩ := List.mem_map.mp hA; exact meaning_adm G b)
            (argMeaning_adm G _)
            (show restsT [(MethodMembers.hostT (ρ i), y.2.1.map (meaning G), argMeaning G y.2.2.1,
              meaning G y.2.2.2)] (q + 2) U u from ht)
            hvalρ hscope rfl (by simp only [List.take_nil, List.take_zero, List.length_nil]; exact trivial)
            (fun _ _ _ _ ys hys => by simpa using hys)
            (by simp [CallArguments.Values]) (by simp)
          simpa using hb
        have hmem : meaning G F (q + 2) U (.objAt [] (.bound u (ρ i) [])) :=
          (represents_sem hF (q + 2) U _).mpr ⟨hcalls, hrests⟩
        have hdown := (meaning_adm G F).down_le (q + 2) q (by omega) U _ hmem
        refine Or.inr ⟨trunc q (Nat.le_succ q) (trunc (q + 1) (Nat.le_succ (q + 1)) U), h',
          .objAt [] (.bound u (ρ i) []), WExt_refl _, WorldAdm_trunc _ (WorldAdm_trunc _ hu), ?_,
          HeapOk_trunc q _ h' (HeapOk_trunc (q + 1) U h' hok), value_safe _ _ _ _ _ rfl ?_⟩
        · simpa [Model.slots] using (Step.makeFields (h := h') (ns := []) (vs := [])
            (c := .bound u (ρ i) []) (by simp) rfl)
        · rw [trunc_trunc]
          exact hdown
  | sub ht hc ih =>
    intro n W h ρ he hw hh
    exact Safe_mono n (fun k _ V v hv => (PositiveCertificates.check_sound hc).sound k V v hv)
      W h _ (ih n W h ρ he hw hh)

/-- Syntactically typed bodies establish list signatures offering at least
the code's arity, including zero parameters, without encoding the function as
nested unary closures. -/
theorem HasTy.invocationSpec {G : NormalGraph ι} {Γ ρ n W b arity}
    {L : List (Ty ι × List (Ty ι) × Ty ι)} (he : EnvOk G Γ ρ n W)
    (hlen : ∀ p ∈ L, arity ≤ p.2.1.length)
    (hb : ∀ p ∈ L, HasTy G (bodyFrame arity p Γ) b p.2.2) :
    InvocationSpec arity (L.map fun p => (meaning G p.1, p.2.1.map (meaning G), meaning G p.2.2))
      n W (instantiate (arity + 1) ρ b) :=
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

end Verification.Model.ProgramTyping
