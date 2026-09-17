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
  cases c with
  | nul => subst v; exact ⟨rfl, trivial⟩
  | bool => rcases hc with rfl | rfl <;> exact ⟨rfl, trivial⟩
  | boolLit b => cases b <;> cases hc <;> exact ⟨rfl, trivial⟩
  | num => obtain ⟨b, rfl⟩ := hc; exact ⟨rfl, trivial⟩
  | numLit b => subst v; exact ⟨rfl, trivial⟩
  | refs a rest => obtain ⟨flds, rfl, _⟩ := hc.1.1; exact ⟨rfl, trivial⟩
  | arrs L => exact ⟨(callsT_callable hc).val, (callsT_callable hc).scoped⟩
  | callable a bs L => exact ⟨(callsT_callable hc.2).val,(callsT_callable hc.2).scoped⟩
  | undef => subst v; exact ⟨rfl, trivial⟩
  | top => exact hc
  | list a bs => obtain ⟨ls, rfl, _⟩ := hc.1; exact ⟨rfl, trivial⟩
  | str => obtain ⟨s, rfl⟩ := hc; exact ⟨rfl, trivial⟩
  | strLit s => subst v; exact ⟨rfl, trivial⟩

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
  | funE : Represents G F (.arrs L) → (∀ p ∈ L, p.1.length = arity) →
      (∀ p ∈ L, HasTy G (p.1 ++ Γ) b p.2) → HasTy G Γ (.make (.closure arity b) .nul) F
  /-- A callable object: the same allocation as a record, with invocation code
  attached. Its bag is a record like any other, so its fields are named by the
  program rather than fixed here. -/
  | makeCallable {parts : List (String × Ty ι × Tm)} :
      Represents G F (.callable (parts.map fun p => (p.1, p.2.1)) [] L) →
      (parts.map Prod.fst).Nodup →
      (∀ p ∈ parts, HasTy G Γ p.2.2 p.2.1) →
      (∀ p ∈ L, p.1.length = arity) →
      (∀ p ∈ L, HasTy G (p.1 ++ Γ) b p.2) →
      HasTy G Γ (.makeAt (.closure arity b) (parts.map Prod.fst)
        (parts.map fun p => p.2.2)) F
  | callCallable : HasTy G Γ f F → Represents G F (.callable P Ps L) → ((xs : List (Ty ι × Tm)).map Prod.fst,B) ∈ L →
      (∀ p ∈ xs, HasTy G Γ p.2 p.1) → HasTy G Γ (.call f (xs.map Prod.snd)) B
  | readCallable : HasTy G Γ a F → Represents G F (.callable P Ps L) → (f, A) ∈ P →
      HasTy G Γ (.readAt f a) A
  | writeCallable : HasTy G Γ a F → Represents G F (.callable P Ps L) → (f, A) ∈ P →
      HasTy G Γ b A → Represents G N .nul → HasTy G Γ (.writeAt f a b) N
  | app : HasTy G Γ f F → Represents G F (.arrs L) → ((xs : List (Ty ι × Tm)).map Prod.fst, B) ∈ L →
      (∀ p ∈ xs, HasTy G Γ p.2 p.1) → HasTy G Γ (.call f (xs.map Prod.snd)) B
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
    exact Safe_mono n (fun k _ U v hv => (represents_sem hr k U v).mpr hv.2) W h _ hs
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
      (callsT_code_iff _ arity [] _ j U).mp ((callsT_adm _).mono j _ U hx _
        ((callsT_adm _).down_le n j hj W _ ((callsT_code_iff _ arity [] _ n W).mpr hcode)))
    have hs := make_callable_fields_rule
      (P := parts.map fun p => meaning G p.2.1)
      (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_adm G r.2.1)
      arity j U heap _ args _ hnd (by simpa using hlenA.symm) (by simpa using hlenA.symm)
      hc
      (ArgsT_values
        (by intro A hA'; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hA'; exact meaning_valOnly G r.2.1)
        hargs)
      hu hok (ArgsT_zip hargs)
    apply Safe_mono j (fun k _ V v hv => (represents_sem hr k V v).mpr ⟨⟨?_, by simp⟩, hv.2⟩) U heap _ hs
    case _ =>
      have hfam : ReferenceConjunctions.famsOf (meaning G) (parts.map fun p => (p.1, p.2.1))
          = (parts.map Prod.fst).zip (parts.map fun p => meaning G p.2.1) := by
        simp [ReferenceConjunctions.famsOf, List.map_map, Function.comp_def, List.zip_map']
      rw [hfam]
      exact hv.1
  | @callCallable Γ f F P Ps L xs B hf hr hp ha ihf iha =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := call_safe (B := meaning G B) (f := instantiate 0 ρ f)
      (xs.map fun p => (meaning G p.1,instantiate 0 ρ p.2))
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_adm G q.1)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_valOnly G q.1)
      hw hh
    apply (by simpa only [List.map_map,Function.comp_def] using hs)
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      simpa only [List.map_map,Function.comp_def] using
        callsT_select (((represents_sem hr k U v).mp hv).2) (List.mem_map.mpr ⟨(xs.map Prod.fst,B), hp, rfl⟩)
    · intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      intro j hj U hx hu heap hok
      exact iha q hq j U heap ρ (he.transfer j hj U hx) hu hok
  | @readCallable Γ a Ref P Ps L f A ha hr hm ih =>
    intro n W h ρ he hw hh
    apply bind (Tm.readAt f) Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
    intro j hj U hx hu heap v hok hv ha'
    exact bag_read (meaning_valOnly G A) (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
      ((represents_sem hr j U v).mp ha').1.1 hu hok
  | @writeCallable Γ a Ref P Ps L f A b N ha hr hm hb hn iha ihb =>
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
      ((represents_sem hr k V av).mp ha'').1.1 hb' hbval hv hok'
  | @app Γ f F L xs B hf hr hp ha ihf iha =>
    intro n W h ρ he hw hh
    simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
    have hs := call_safe (B := meaning G B) (f := instantiate 0 ρ f)
      (xs.map fun p => (meaning G p.1,instantiate 0 ρ p.2))
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_adm G q.1)
      (by intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact meaning_valOnly G q.1)
      hw hh
    apply (by simpa only [List.map_map,Function.comp_def] using hs)
    · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
      intro k hk U v hv
      simpa only [List.map_map,Function.comp_def] using
        callsT_select ((represents_sem hr k U v).mp hv) (List.mem_map.mpr ⟨(xs.map Prod.fst,B), hp, rfl⟩)
    · intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      intro j hj U hx hu heap hok
      exact iha q hq j U heap ρ (he.transfer j hj U hx) hu hok
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
