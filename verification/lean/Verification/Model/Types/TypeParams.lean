import Verification.Model.Types.PositiveRules
import Verification.Model.Semantics.Rules
import Verification.Model.Programs.ProgramTyping

/-! First-order rigid parameters over the existing positive graphs.

A parameter is a graph label whose meaning is supplied by an assignment `η`,
not by unfolding a row. Substituting a type argument for that label must mean
the same thing as interpreting the original syntax under the updated
assignment. This is the substitution contract. Source extraction of
`id<T>(x: T): T { return x }` and of `type Id<T> = T` / `type Box<T> = { value: T }`
is connected, including `T extends boolean` as `T ≤ boolean` and bodies that
copy `T` through `const` and extra parameters. It is not yet higher-rank
polymorphism or parameter-changing recursion.

`T extends boolean` is the upper bound `T ≤ boolean`. It does not yield
`boolean ≤ T` or `true ≤ T`: `T` may be `false`. -/
namespace Verification.Model.TypeParams
open PositiveNormalization PositiveGraphs PositiveRules Tower ProgramTyping

variable {ι : Type}

def substTy [DecidableEq ι] (p : ι) (A : List ι) : List ι → List ι
  | [] => []
  | i :: S => (if i = p then A else [i]) ++ substTy p A S

/-- Substitution reaches a record's fields one by one; the names are data. -/
def substFields [DecidableEq ι] (p : ι) (A : List ι)
    (fs : List (PropKey × List ι)) : List (PropKey × List ι) :=
  fs.map fun q => (q.1, substTy p A q.2)

def substTuple [DecidableEq ι] (p : ι) (A : List ι) (t : Tuple (List ι)) : Tuple (List ι) :=
  ⟨t.required.map (substTy p A), t.optional.map (substTy p A), t.rest.map (substTy p A), t.readonly⟩

def substClause [DecidableEq ι] (p : ι) (A : List ι) : Clause (List ι) → Clause (List ι)
  | .top => .top
  | .list a bs => .list (substTuple p A a) (bs.map (substTuple p A))
  | .pack a bs => .pack (substTuple p A a) (bs.map (substTuple p A))
  | .nul => .nul
  | .undef => .undef
  | .bool => .bool
  | .boolLit b => .boolLit b
  | .num => .num
  | .numLit v => .numLit v
  | .str => .str
  | .strLit v => .strLit v
  | .bigint => .bigint
  | .bigintLit v => .bigintLit v
  | .symbol => .symbol
  | .refs a bs vs os ms ks => .refs (substFields p A a) (bs.map (substFields p A)) (substFields p A vs)
      (os.map (·.map (substTy p A))) (ms.map (MethodMembers.Sig.map (substTy p A))) ks
  | .dict a bs vs ds os ms ks cs => .dict (substFields p A a) (bs.map (substFields p A))
      (substFields p A vs) (ds.map (substTy p A)) (os.map (·.map (substTy p A)))

      (ms.map (MethodMembers.Sig.map (substTy p A))) ks (cs.map (substTy p A))
  | .arrs L S => .arrs (L.map fun q => (substTy p A q.1, q.2.1.map (substTy p A), substTy p A q.2.2))
      (S.map fun q => (substTy p A q.1, q.2.1.map (substTy p A), substTy p A q.2.2.1,
        substTy p A q.2.2.2))
  | .ctors L S => .ctors (L.map fun q => (q.1.map (substTy p A), substTy p A q.2))
      (S.map fun q => (q.1.map (substTy p A), substTy p A q.2.1, substTy p A q.2.2))
  | .callable a bs L S =>
      .callable (substFields p A a) (bs.map (substFields p A))
        (L.map fun q => (substTy p A q.1, q.2.1.map (substTy p A), substTy p A q.2.2))
        (S.map fun q => (substTy p A q.1, q.2.1.map (substTy p A), substTy p A q.2.2.1,
          substTy p A q.2.2.2))

def substGraph [DecidableEq ι] (p : ι) (A : List ι) (G : NormalGraph ι) : NormalGraph ι :=
  .ofRows fun i => (G i).map (substClause p A)

def update [DecidableEq ι] (η : ι → Fam) (p : ι) (T : Fam) (i : ι) : Fam :=
  if i = p then T else η i

def paramLayer (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam)
    (X : ι → Fam) (i : ι) : Fam :=
  if P i then η i else normalLayer G X i

theorem param_congr (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam) :
    LayerCongr (paramLayer G P η) := by
  intro X Y n h i W v
  by_cases hp : P i = true
  · simp [paramLayer, hp]
  · have hn : P i = false := eq_false_of_ne_true hp
    simpa [paramLayer, hn, normalLayer] using normal_congr G X Y n h i W v

theorem param_adm (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam)
    (hη : ∀ i, P i = true → Adm (η i)) : LayerAdm (paramLayer G P η) := by
  intro X _ i
  by_cases hp : P i = true
  · simpa [paramLayer, hp] using hη i hp
  · have hn : P i = false := eq_false_of_ne_true hp
    simpa [paramLayer, hn, normalLayer, semList] using
      setSem_adm (fun c => semWithArgs_adm (setSem X) (plainArguments G (setSem X)) c) (G i)

def denoteP (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam) : ι → Fam :=
  Tower.denote (paramLayer G P η)

def meaningP (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam) (S : List ι) : Fam :=
  setSem (denoteP G P η) S

/-- The argument lists of a type under a rigid assignment: its pack clauses'
tuple contracts, at the current level. A rigid parameter is a value
parameter; it admits no argument list. -/
def argsP (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam) (S : List ι) : ArgFam :=
  plainArguments G (meaningP G P η) S

/-- A clause's members under a rigid assignment. -/
abbrev semP (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam) : Clause (List ι) → Fam :=
  semWithArgs (meaningP G P η) (argsP G P η)

theorem unfold_param (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam)
    (i : ι) (n : Nat) (W : WorldT n) (v : Val) :
    denoteP G P η i n W v ↔ paramLayer G P η (denoteP G P η) i n W v :=
  Tower.denote_unfold (param_congr G P η) i n W v

theorem param_denote {G : NormalGraph ι} {P η} {p : ι}
    (hp : P p = true) (n : Nat) (W : WorldT n) (v : Val) :
    denoteP G P η p n W v ↔ η p n W v := by
  rw [unfold_param]
  simp [paramLayer, hp]

theorem meaningP_param {G : NormalGraph ι} {P η} {p : ι}
    (hp : P p = true) (n : Nat) (W : WorldT n) (v : Val) :
    meaningP G P η [p] n W v ↔ η p n W v := by
  simp [meaningP, setSem, param_denote hp]

theorem no_params_layer (G : NormalGraph ι) (η X : ι → Fam) (i : ι) :
    paramLayer G (fun _ => false) η X i = normalLayer G X i := by
  simp [paramLayer, normalLayer]

theorem no_params (G : NormalGraph ι) (hG : G.Plain) (η : ι → Fam) :
    denoteP G (fun _ => false) η = normalDenote G := by
  rw [normalDenote_plain G hG]
  apply congrArg Tower.denote
  funext X i
  exact no_params_layer G η X i

theorem meaningP_ground (G : NormalGraph ι) (hG : G.Plain) (η : ι → Fam) (S : List ι) :
    meaningP G (fun _ => false) η S = meaning G S := by
  simp [meaningP, meaning, no_params G hG]

theorem meaningP_adm (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam)
    (hη : ∀ i, P i = true → Adm (η i)) (S : List ι) : Adm (meaningP G P η S) :=
  setSem_adm (fun i => Tower.denote_adm (param_congr G P η) (param_adm G P η hη) i) S

/-! ## Substitution preserves meaning

The identity alias `type Id<T> = T` and the box alias `type Box<T> = Ref<T>`
are the first-order cases: substituting `A` for `T` is interpreting the original
syntax under `η[T ↦ ⟦A⟧]`. -/

theorem substTy_singleton_eq [DecidableEq ι] (p : ι) (A : List ι) :
    substTy p A [p] = A := by simp [substTy]

/-- Instantiating a parameter is reading the assigned family.
Source `type Id<T> = T` applied to `A` is this theorem. -/
theorem instantiate_param [DecidableEq ι] {G : NormalGraph ι} {P η} {p : ι}
    (hp : P p = true) (T : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    meaningP G P (update η p T) [p] n W v ↔ T n W v := by
  have : update η p T p = T := by simp [update]
  rw [meaningP_param hp, this]

/-- Instantiating `Ref T` is `Ref` of the assigned family.
Source `type Box<T> = { value: T }` applied to `A` is this theorem. -/
theorem instantiate_ref [DecidableEq ι] {G : NormalGraph ι} {P η} {p b : ι}
    (hp : P p = true) (hb : P b = false) (hG : G b = [.refs [(valueField, [p])] [] []])
    (T : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    meaningP G P (update η p T) [b] n W v ↔ refT T n W v := by
  have hη : update η p T p = T := by simp [update]
  have hmem :
      meaningP G P (update η p T) [b] n W v ↔
        ReferenceConjunctions.refsT [(valueField, meaningP G P (update η p T) [p])] [] n W v := by
    simp only [meaningP, setSem, List.mem_singleton, exists_eq_left]
    rw [unfold_param]
    simp [paramLayer, normalLayer, hb, hG, semList, setSem, semWithArgs, ReferenceConjunctions.famsOf, viewT]
    intro h
    obtain ⟨flds, rfl, -⟩ := h.1
    exact ⟨optT_nil, MethodMembers.methodT_nil _ _ _⟩
  have href :
      ReferenceConjunctions.refsT [(valueField, meaningP G P (update η p T) [p])] [] n W v ↔
        refT (meaningP G P (update η p T) [p]) n W v :=
    ReferenceConjunctions.cell _ n W v
  have hAgr : Agree (meaningP G P (update η p T) [p]) T n := by
    intro m hm U u
    simpa [meaningP, setSem, hη] using
      param_denote (G := G) (P := P) (η := update η p T) hp m U u
  rw [hmem, href]
  exact refT_contractive n _ _ hAgr W v

/-! ## Identity at every admissible `T`, and the `extends boolean` trap -/

def trueT : Fam := fun _ _ v => v = .tru
def falseT : Fam := fun _ _ v => v = .fls

theorem trueT_le_boolT : FamLe trueT boolT := fun _ _ _ h => Or.inl h
theorem falseT_le_boolT : FamLe falseT boolT := fun _ _ _ h => Or.inr h

/-- `T extends boolean` is `T ≤ boolean`. It does not give `true ≤ T`. -/
theorem extends_boolean_not_true :
    ¬ ∀ T : Fam, FamLe T boolT → FamLe trueT T := by
  intro h
  have := h falseT falseT_le_boolT 0 (ofList []) .tru rfl
  cases this

def idFn (l : Nat) : Tm := .fn l (.var 1)

theorem Safe_of_mem {T : Fam} {n : Nat} {W : WorldT n} {h v}
    (hv : isVal v = true) (hm : T n W v) : Safe T n W h v := by
  cases n with
  | zero => trivial
  | succ _ => exact Or.inl ⟨hv, hm⟩

/-- The identity inhabits `T → T` for every family `T` of closed values.
Instantiating the scheme is specializing this theorem; it is not a separate
semantic rule. -/
theorem identity_arrow {T : Fam} (hV : ValOnly T)
    (hS : ∀ j (W : WorldT j) a, T j W a → Scoped 0 a) (k : Nat) (W : WorldT k) (l : Nat) :
    arrowT T T k W (idFn l) := by
  refine ⟨⟨1, .var 1, _, rfl, by simp [Scoped]⟩, ?_⟩
  intro j hj U _ _ heap _ a ha
  have hb : callBody (idFn l) a = subst 0 .undef (subst 1 a (.var 1)) := by
    change CallArguments.bindParameters 1 [a] .undef (.var 1) = _
    exact CallArguments.unary_binding a .undef (.var 1)
  have hs : subst 0 .undef (subst 1 a (.var 1)) = a := by
    simpa [subst] using subst_above (hS j U a ha) (Nat.le_refl 0) .undef
  rw [hb, hs]
  exact Safe_of_mem (hV j U a ha) ha

theorem identity_at_boolean (k : Nat) (W : WorldT k) :
    arrowT boolT boolT k W (idFn 0) :=
  identity_arrow boolT_valOnly (fun _ _ _ h => by rcases h with rfl | rfl <;> simp [Scoped]) k W 0

/-- `type Box<T> = Ref<T>` at label 5, with parameter `T` at label 4. -/
def boxG : NormalGraph Nat := .ofRows fun
  | 5 => [.refs [(valueField, [4])] [] []]
  | _ => []

def isT : Nat → Bool := fun i => i == 4

theorem box_instantiate (n : Nat) (W : WorldT n) (v : Val) :
    meaningP boxG isT (update (fun _ => nulT) 4 falseT) [5] n W v ↔
      refT falseT n W v :=
  instantiate_ref (by decide : isT 4 = true) (by decide : isT 5 = false) rfl falseT n W v

/-! ## Typing under a rigid assignment

`HasTy` is unchanged. Soundness of `var` and `funE` is replayed with `meaningP`
so a generic body is checked once, for every admissible `T`. Instantiating the
scheme is specializing that theorem, not a second typing rule. -/

def ClosedAssign (P : ι → Bool) (η : ι → Fam) : Prop :=
  ∀ i, P i = true → Adm (η i) ∧ ValOnly (η i) ∧ ∀ n W v, η i n W v → Scoped 0 v

def EnvOkP (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam)
    (Γ : List (Ty ι)) (ρ : Env) (n : Nat) (W : WorldT n) : Prop :=
  (∀ i, Scoped 0 (ρ i)) ∧ ∀ i A, Γ[i]? = some A → meaningP G P η A n W (ρ i)

theorem EnvOkP.transfer {G : NormalGraph ι} {P η} {Γ ρ n W}
    (hη : ClosedAssign P η) (h : EnvOkP G P η Γ ρ n W)
    (j : Nat) (hj : j ≤ n) (U : WorldT j) (hx : WExt (trunc j hj W) U) :
    EnvOkP G P η Γ ρ j U :=
  ⟨h.1, fun i A hi =>
    (meaningP_adm G P η (fun i hi => (hη i hi).1) A).mono j _ U hx _
      ((meaningP_adm G P η (fun i hi => (hη i hi).1) A).down_le n j hj W _ (h.2 i A hi))⟩

theorem unfold_nonparam {G : NormalGraph ι} {P η} {i : ι}
    (hP : P i = false) (n : Nat) (W : WorldT n) (v : Val) :
    denoteP G P η i n W v ↔ semList (meaningP G P η) (argsP G P η) (G i) n W v := by
  rw [unfold_param]
  simp [paramLayer, hP]
  rfl

theorem meaningP_value {G : NormalGraph ι} {P η} {A n W v}
    (hC : ClosedAssign P η) (h : meaningP G P η A n W v) :
    isVal v = true ∧ Scoped 0 v := by
  obtain ⟨i, _, hv⟩ := h
  by_cases hp : P i = true
  · have hv' := (param_denote hp n W v).mp hv
    exact ⟨(hC i hp).2.1 n W v hv', (hC i hp).2.2 n W v hv'⟩
  · have hn : P i = false := eq_false_of_ne_true hp
    obtain ⟨c, _, hc⟩ := (unfold_nonparam hn n W v).mp hv
    exact semWithArgs_value hc

theorem meaningP_valOnly {G : NormalGraph ι} {P η} (hC : ClosedAssign P η)
    (A : Ty ι) : ValOnly (meaningP G P η A) :=
  fun _ _ _ h => (meaningP_value hC h).1

theorem EnvOkP.push_value {G : NormalGraph ι} {P η} {Γ ρ n W A a}
    (hC : ClosedAssign P η) (h : EnvOkP G P η Γ ρ n W)
    (ha : meaningP G P η A n W a) :
    EnvOkP G P η (A :: Γ) (push a ρ) n W := by
  refine ⟨?_, ?_⟩
  · intro i; cases i with
    | zero => exact (meaningP_value hC ha).2
    | succ i => exact h.1 i
  · intro i B hi; cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst B; exact ha
    | succ i => exact h.2 i B hi

theorem EnvOkP.prepend {G : NormalGraph ι} {P η} {Γ ρ n W As args}
    (hC : ClosedAssign P η) (h : EnvOkP G P η Γ ρ n W)
    (ha : ArgsT (As.map (meaningP G P η)) n W args) :
    EnvOkP G P η (As ++ Γ) (prependArgs args ρ) n W := by
  induction As generalizing args with
  | nil => cases args <;> simp_all [ArgsT, prependArgs]
  | cons A As ih =>
    cases args with
    | nil => exact False.elim ha
    | cons a args => exact (ih ha.2).push_value hC ha.1

theorem expand_semP {G : NormalGraph ι} {P η} {S : List ι}
    (hS : ∀ i ∈ S, P i = false) (n : Nat) (W : WorldT n) (v : Val) :
    meaningP G P η S n W v ↔ semList (meaningP G P η) (argsP G P η) (clausesOf G S) n W v := by
  constructor
  · rintro ⟨i, hi, hv⟩
    obtain ⟨c, hc, hv⟩ := (unfold_nonparam (hS i hi) n W v).mp hv
    exact ⟨c, List.mem_flatMap.mpr ⟨i, hi, hc⟩, hv⟩
  · rintro ⟨c, hc, hv⟩
    obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
    exact ⟨i, hi, (unfold_nonparam (hS i hi) n W v).mpr ⟨c, hc, hv⟩⟩

theorem represents_semP {G : NormalGraph ι} {P η} {A c}
    (hr : Represents G A c) (hA : ∀ i ∈ A, P i = false)
    (n : Nat) (W : WorldT n) (v : Val) :
    meaningP G P η A n W v ↔ semP G P η c n W v := by
  rw [expand_semP hA, ← expand_of_plain hr.plain, show expand G A = [c] from hr]
  simp [semList, setSem]

theorem answers_soundP {G : NormalGraph ι} {P η} {A tag q n W v}
    (hq : Answers G A tag q) (hA : ∀ i ∈ A, P i = false)
    (hv : meaningP G P η A n W v) : tagHolds tag v = q := by
  obtain ⟨c, hc, hv⟩ := (expand_semP hA n W v).mp hv
  exact tagClause_sound (hq.2 c (by rwa [expand_of_plain hq.1])) hv

theorem EnvOkP.refine {G : NormalGraph ι} {P η} {Γ ρ n W i A B}
    (h : EnvOkP G P η Γ ρ n W) (hi : Γ[i]? = some A)
    (hb : meaningP G P η B n W (ρ i)) : EnvOkP G P η (Γ.set i B) ρ n W := by
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

theorem var_safeP {G : NormalGraph ι} {P η} {Γ i A n W h ρ}
    (hC : ClosedAssign P η) (hi : Γ[i]? = some A)
    (he : EnvOkP G P η Γ ρ n W) (_hw : WorldAdm W) (_hh : HeapOk n W h) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ (.var i)) := by
  simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  exact value_safe _ _ _ _ _ (meaningP_value hC (he.2 _ _ hi)).1 (he.2 _ _ hi)

theorem invocation_of_bodyP {G : NormalGraph ι} {P η} {Γ ρ n W b arity}
    {L : List (Ty ι × List (Ty ι) × Ty ι)} (hC : ClosedAssign P η)
    (he : EnvOkP G P η Γ ρ n W) (hlen : ∀ p ∈ L, p.2.1.length = arity)
    (hb : ∀ p ∈ L, ∀ j U heap env, EnvOkP G P η (p.1 :: p.2.1 ++ Γ) env j U →
      WorldAdm U → HeapOk j U heap →
      Safe (meaningP G P η p.2.2) j U heap (instantiate 0 env b)) :
    InvocationSpec arity
      (L.map fun p => (meaningP G P η p.1, p.2.1.map (meaningP G P η), meaningP G P η p.2.2))
      n W (instantiate (arity + 1) ρ b) := by
  have hscoped : ∀ (As : List (Ty ι)) j U args, ArgsT (As.map (meaningP G P η)) j U args →
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
        · exact (meaningP_value hC ha.1).2
        · exact ih j U args ha.2 v hv
  -- Exact arity: the parameters the code takes are all of them.
  have htake : ∀ q ∈ L, q.2.1.take arity = q.2.1 := fun q hq =>
    List.take_of_length_le (Nat.le_of_eq (hlen q hq))
  apply invocationSpec_of_instantiated he.1
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    show arity ≤ (q.2.1.map (meaningP G P η)).length
    rw [List.length_map, hlen q hq]
    exact Nat.le_refl _
  · intro p hp j U r args hr ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    change ArgsT ((q.2.1.map (meaningP G P η)).take arity) j U args at ha
    rw [← List.map_take, htake q hq] at ha
    exact hscoped (q.1 :: q.2.1) j U (r :: args) ⟨hr, ha⟩
  · intro p hp j hj U hx hu heap hok r args hr ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    change ArgsT ((q.2.1.map (meaningP G P η)).take arity) j U args at ha
    rw [← List.map_take, htake q hq] at ha
    have hall : ArgsT ((q.1 :: q.2.1).map (meaningP G P η)) j U (r :: args) := ⟨hr, ha⟩
    have henv := (he.transfer hC j (Nat.le_of_lt hj) U hx).prepend hC hall
    exact hb q hq j U heap _ (by simpa [List.append_assoc] using henv) hu hok

theorem funE_safeP {G : NormalGraph ι} {P η} {Γ F L arity b n W h ρ}
    (hC : ClosedAssign P η) (hr : Represents G F (.arrs L []))
    (hF : ∀ i ∈ F, P i = false) (hlen : ∀ p ∈ L, p.2.1.length = arity)
    (hb : ∀ p ∈ L, ∀ j U heap env, EnvOkP G P η (p.1 :: p.2.1 ++ Γ) env j U →
      WorldAdm U → HeapOk j U heap →
      Safe (meaningP G P η p.2.2) j U heap (instantiate 0 env b))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η F) n W h
      (instantiate 0 ρ (.make (.closure arity b) .nul)) := by
  simp only [instantiate, Nat.zero_add]
  have hcode := invocation_of_bodyP hC he hlen hb
  have hs := make_callable_rule nulT_adm arity n W h _ .nul hcode rfl hw hh rfl
  exact Safe_mono n (fun k _ U v hv => (represents_semP hr hF k U v).mpr
    ⟨hv.2, hv.2.1, by simp⟩) W h _ hs

theorem app_safeP {G : NormalGraph ι} {P η} {Γ F Rt B f r n W h ρ}
    {L : List (Ty ι × List (Ty ι) × Ty ι)} {S : List (Ty ι × List (Ty ι) × Ty ι × Ty ι)}
    {xs : List (Ty ι × Tm)}
    (hC : ClosedAssign P η) (hr : Represents G F (.arrs L S))
    (hF : ∀ i ∈ F, P i = false) (hp : (Rt, xs.map Prod.fst, B) ∈ L)
    (ihf : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η F) n W h (instantiate 0 ρ f))
    (ihr : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η Rt) n W h (instantiate 0 ρ r))
    (iha : ∀ p ∈ xs, ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η p.1) n W h (instantiate 0 ρ p.2))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η B) n W h
      (instantiate 0 ρ (.invoke f r (xs.map Prod.snd))) := by
  simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
  have hs := call_safe (Rc := meaningP G P η Rt) (B := meaningP G P η B) (f := instantiate 0 ρ f)
    (r := instantiate 0 ρ r)
    (xs.map fun p => (meaningP G P η p.1, instantiate 0 ρ p.2))
    (meaningP_adm G P η (fun i hi => (hC i hi).1) Rt) (meaningP_valOnly hC Rt)
    (by intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact meaningP_adm G P η (fun i hi => (hC i hi).1) q.1)
    (by intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact meaningP_valOnly hC q.1)
    hw hh
  apply (by simpa only [List.map_map, Function.comp_def] using hs)
  · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
    intro k hk U v hv
    simpa only [List.map_map, Function.comp_def] using
      callsT_select ((represents_semP hr hF k U v).mp hv).1
        (List.mem_map.mpr ⟨(Rt, xs.map Prod.fst, B), hp, rfl⟩)
  · intro j hj U hx hu heap hok
    exact ihr j U heap ρ (he.transfer hC j hj U hx) hu hok
  · intro p hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
    intro j hj U hx hu heap hok
    exact iha q hq j U heap ρ (he.transfer hC j hj U hx) hu hok

/-- One named field, which is where a parameter under a reference is read. The
general many-field rule is `make_fields_rule`; nothing here depends on the
arity, only on the parameter being interpreted rather than erased. -/
theorem alloc_safeP {G : NormalGraph ι} {P η} {Γ a A Ref f n W h ρ}
    (hC : ClosedAssign P η) (hr : Represents G Ref (.refs [(f, A)] [] []))
    (hRef : ∀ i ∈ Ref, P i = false)
    (ih : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η A) n W h (instantiate 0 ρ a))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η Ref) n W h (instantiate 0 ρ (.makeAt .absent [f] [a])) := by
  simp only [instantiate, instantiateArgs_eq_map, List.map_cons, List.map_nil]
  apply bind (fun t => .makeAt .absent [f] [t])
    (fun hs => CallArguments.Step.makeArgs (.head hs)) n W h _ hw hh (ih n W h ρ he hw hh)
  intro j hj U hx hu heap v hok hv ha'
  apply Safe_mono j (fun k _ V w hw => (represents_semP hr hRef k V w).mpr
    ⟨⟨hw, by simp⟩, fun f T hm => by simp [ReferenceConjunctions.famsOf] at hm,
      by obtain ⟨flds, rfl, -⟩ := hw
         exact ⟨by simpa [ReferenceConjunctions.famsOf] using optT_nil, MethodMembers.methodT_nil _ _ _,
           by simp⟩⟩)
  refine make_fields_rule (As := [meaningP G P η A])
    (by intro X hX; simp only [List.mem_singleton] at hX; subst hX
        exact meaningP_adm G P η (fun i hi => (hC i hi).1) A)
    j U heap .absent [f] [v] (by simp) rfl rfl (by simpa using hv) hu hok
    (by intro q hq
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hq
        subst hq; exact ha') ?_
  intro k hk V hy hrec
  exact hrec

theorem read_safeP {G : NormalGraph ι} {P η} {Γ a A fs f Ref n W h ρ}
    (hC : ClosedAssign P η) (hr : Represents G Ref (.refs fs [] []))
    (hm : (f, A) ∈ fs) (hRef : ∀ i ∈ Ref, P i = false)
    (ih : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η Ref) n W h (instantiate 0 ρ a))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ (.readAt f a)) := by
  simp only [instantiate]
  apply bind (Tm.readAt f) Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
  intro j hj U hx hu heap v hok hv ha'
  obtain ⟨flds, l, c, rfl, hfd, hl, hag⟩ :=
    recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
      ((represents_semP hr hRef j U v).mp ha').1.1
  exact read_rule (meaningP_valOnly hC A) j U heap l hu hok hfd hl hag

theorem write_safeP {G : NormalGraph ι} {P η} {Γ a b A fs f Ref N n W h ρ}
    (hC : ClosedAssign P η) (hr : Represents G Ref (.refs fs [] []))
    (hm : (f, A) ∈ fs)
    (hRef : ∀ i ∈ Ref, P i = false) (hn : Represents G N .nul)
    (hN : ∀ i ∈ N, P i = false)
    (iha : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η Ref) n W h (instantiate 0 ρ a))
    (ihb : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η A) n W h (instantiate 0 ρ b))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η N) n W h (instantiate 0 ρ (.writeAt f a b)) := by
  simp only [instantiate]
  apply bind (fun a => .writeAt f a (instantiate 0 ρ b)) Step.writeC1 n W h _ hw hh
    (iha n W h ρ he hw hh)
  intro j hj U hx hu heap av hok hav ha'
  apply bind (.writeAt f av) (Step.writeC2 hav) j U heap _ hu hok
    (ihb j U heap ρ (he.transfer hC j hj U hx) hu hok)
  intro k hk V hy hv heap' bv hok' hbval hb'
  have ha'' :=
    (meaningP_adm G P η (fun i hi => (hC i hi).1) Ref).mono k _ V hy av
      ((meaningP_adm G P η (fun i hi => (hC i hi).1) Ref).down_le j k hk U av ha')
  obtain ⟨flds, l, c, rfl, hfd, hl, hag⟩ :=
    recT_at (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
      ((represents_semP hr hRef k V av).mp ha'').1.1
  apply Safe_mono k (fun i _ X v hval => (represents_semP hn hN i X v).mpr hval)
  exact write_rule (meaningP_adm G P η (fun i hi => (hC i hi).1) A)
    k V heap' l bv hbval hv hok' hfd hl hag hb'

theorem nul_safeP {G : NormalGraph ι} {P η} {A Γ n W h ρ}
    (hr : Represents G A .nul) (hA : ∀ i ∈ A, P i = false)
    (_he : EnvOkP G P η Γ ρ n W) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ .nul) := by
  simp only [instantiate]
  exact value_safe _ _ _ _ _ rfl ((represents_semP hr hA n W _).mpr rfl)

theorem undef_safeP {G : NormalGraph ι} {P η} {A Γ n W h ρ}
    (hr : Represents G A .undef) (hA : ∀ i ∈ A, P i = false)
    (_he : EnvOkP G P η Γ ρ n W) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ .undef) := by
  simp only [instantiate]
  exact value_safe _ _ _ _ _ rfl ((represents_semP hr hA n W _).mpr rfl)

theorem tru_safeP {G : NormalGraph ι} {P η} {A Γ n W h ρ}
    (hr : Represents G A .bool) (hA : ∀ i ∈ A, P i = false)
    (_he : EnvOkP G P η Γ ρ n W) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ .tru) := by
  simp only [instantiate]
  exact value_safe _ _ _ _ _ rfl ((represents_semP hr hA n W _).mpr (Or.inl rfl))

theorem fls_safeP {G : NormalGraph ι} {P η} {A Γ n W h ρ}
    (hr : Represents G A .bool) (hA : ∀ i ∈ A, P i = false)
    (_he : EnvOkP G P η Γ ρ n W) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ .fls) := by
  simp only [instantiate]
  exact value_safe _ _ _ _ _ rfl ((represents_semP hr hA n W _).mpr (Or.inr rfl))

theorem flsLit_safeP {G : NormalGraph ι} {P η} {A Γ n W h ρ}
    (hr : Represents G A (.boolLit false)) (hA : ∀ i ∈ A, P i = false)
    (_he : EnvOkP G P η Γ ρ n W) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ .fls) := by
  simp only [instantiate]
  exact value_safe _ _ _ _ _ rfl ((represents_semP hr hA n W _).mpr rfl)

theorem ifBool_safeP {G : NormalGraph ι} {P η} {Γ c C t e A n W h ρ}
    (hC : ClosedAssign P η) (hCP : ∀ i ∈ C, P i = false)
    (hbool : Answers G C .isBool true)
    (ihc : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η C) n W h (instantiate 0 ρ c))
    (iht : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η A) n W h (instantiate 0 ρ t))
    (ihe : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η A) n W h (instantiate 0 ρ e))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ (.ite c t e)) := by
  simp only [instantiate]
  apply bind (fun c => .ite c (instantiate 0 ρ t) (instantiate 0 ρ e)) Step.iteC
    n W h _ hw hh (ihc n W h ρ he hw hh)
  intro j hj U hx hu heap v hok hv ha
  have hb := answers_soundP hbool hCP ha
  have shape : v = .tru ∨ v = .fls := by cases v <;> simp_all [tagHolds]
  rcases shape with rfl | rfl
  · cases j with
    | zero => trivial
    | succ k =>
      refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ t,
        WExt_refl _, WorldAdm_trunc _ hu, .iteT, HeapOk_trunc k U heap hok, ?_⟩
      exact iht k _ heap ρ ((he.transfer hC (k + 1) hj U hx).transfer hC k (Nat.le_succ k)
        _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
  · cases j with
    | zero => trivial
    | succ k =>
      refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ e,
        WExt_refl _, WorldAdm_trunc _ hu, .iteF, HeapOk_trunc k U heap hok, ?_⟩
      exact ihe k _ heap ρ ((he.transfer hC (k + 1) hj U hx).transfer hC k (Nat.le_succ k)
        _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)

theorem ifKnown_safeP {G : NormalGraph ι} {P η} {Γ c C q t e A n W h ρ}
    (hC : ClosedAssign P η) (hq : Represents G C (.boolLit q))
    (hCP : ∀ i ∈ C, P i = false)
    (ihc : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η C) n W h (instantiate 0 ρ c))
    (iht : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η A) n W h (instantiate 0 ρ (if q then t else e)))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ (.ite c t e)) := by
  simp only [instantiate]
  apply bind (fun c => .ite c (instantiate 0 ρ t) (instantiate 0 ρ e)) Step.iteC
    n W h _ hw hh (ihc n W h ρ he hw hh)
  intro j hj U hx hu heap v hok hv ha
  have hvalue := (represents_semP hq hCP j U v).mp ha
  cases q <;> simp only [semP, semWithArgs] at hvalue <;> subst v
  · cases j with
    | zero => trivial
    | succ k =>
      refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ e,
        WExt_refl _, WorldAdm_trunc _ hu, .iteF, HeapOk_trunc k U heap hok, ?_⟩
      exact iht k _ heap ρ ((he.transfer hC (k + 1) hj U hx).transfer hC k (Nat.le_succ k)
        _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)
  · cases j with
    | zero => trivial
    | succ k =>
      refine Or.inr ⟨trunc k (Nat.le_succ k) U, heap, instantiate 0 ρ t,
        WExt_refl _, WorldAdm_trunc _ hu, .iteT, HeapOk_trunc k U heap hok, ?_⟩
      exact iht k _ heap ρ ((he.transfer hC (k + 1) hj U hx).transfer hC k (Nat.le_succ k)
        _ (WExt_refl _)) (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)

theorem ifBoolVar_safeP {G : NormalGraph ι} {P η} {Γ i C T F t e A n W h ρ}
    (hCl : ClosedAssign P η) (hi : Γ[i]? = some C)
    (hCP : ∀ i ∈ C, P i = false) (hb : Answers G C .isBool true)
    (hT : Represents G T (.boolLit true)) (hTP : ∀ i ∈ T, P i = false)
    (hF : Represents G F (.boolLit false)) (hFP : ∀ i ∈ F, P i = false)
    (iht : ∀ n W h ρ, EnvOkP G P η (Γ.set i T) ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η A) n W h (instantiate 0 ρ t))
    (ihe : ∀ n W h ρ, EnvOkP G P η (Γ.set i F) ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η A) n W h (instantiate 0 ρ e))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ (.ite (.var i) t e)) := by
  have hshape := answers_soundP hb hCP (he.2 i C hi)
  have shape : ρ i = .tru ∨ ρ i = .fls := by
    cases hv : ρ i <;> simp_all [tagHolds]
  simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  cases n with
  | zero => trivial
  | succ k =>
    rcases shape with hv | hv
    · have refined := he.refine hi ((represents_semP hT hTP (k + 1) W (ρ i)).mpr
        (by simpa [hv, semP, semWithArgs] using rfl))
      rw [hv]
      refine Or.inr ⟨trunc k (Nat.le_succ k) W, h, instantiate 0 ρ t, WExt_refl _,
        WorldAdm_trunc _ hw, .iteT, HeapOk_trunc k W h hh, ?_⟩
      exact iht k _ h ρ (refined.transfer hCl k (Nat.le_succ k) _ (WExt_refl _))
        (WorldAdm_trunc _ hw) (HeapOk_trunc k W h hh)
    · have refined := he.refine hi ((represents_semP hF hFP (k + 1) W (ρ i)).mpr
        (by simpa [hv, semP, semWithArgs] using rfl))
      rw [hv]
      refine Or.inr ⟨trunc k (Nat.le_succ k) W, h, instantiate 0 ρ e, WExt_refl _,
        WorldAdm_trunc _ hw, .iteF, HeapOk_trunc k W h hh, ?_⟩
      exact ihe k _ h ρ (refined.transfer hCl k (Nat.le_succ k) _ (WExt_refl _))
        (WorldAdm_trunc _ hw) (HeapOk_trunc k W h hh)

theorem ifTag_safeP {G : NormalGraph ι} {P η} {Γ i A tag q u e B n W h ρ}
    (hC : ClosedAssign P η) (hi : Γ[i]? = some A)
    (hAP : ∀ i ∈ A, P i = false) (hq : Answers G A tag q)
    (iht : q = true → ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η B) n W h (instantiate 0 ρ u))
    (ihe : q = false → ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η B) n W h (instantiate 0 ρ e))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η B) n W h (instantiate 0 ρ (.ite (.test tag (.var i)) u e)) := by
  have hval := (meaningP_value hC (he.2 i A hi)).1
  have htag := answers_soundP hq hAP (he.2 i A hi)
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
          (he.transfer hC k (by omega) _ (WExt_refl _))
          (WorldAdm_trunc _ hw)
          (by simpa only [trunc_trunc] using HeapOk_trunc k _ h (HeapOk_trunc (k + 1) W h hh))
      · intro he'
        exact ihe (htag.symm.trans he') k _ h ρ
          (he.transfer hC k (by omega) _ (WExt_refl _))
          (WorldAdm_trunc _ hw)
          (by simpa only [trunc_trunc] using HeapOk_trunc k _ h (HeapOk_trunc (k + 1) W h hh))

theorem unionVar_safeP {G : NormalGraph ι} {P η} {Γ i C t A n W h ρ}
    (hC : ClosedAssign P η) (hi : Γ[i]? = some C)
    (ih : ∀ a ∈ C, ∀ n W h ρ, EnvOkP G P η (Γ.set i [a]) ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η A) n W h (instantiate 0 ρ t))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ t) := by
  obtain ⟨a, ha, hv⟩ := he.2 i C hi
  apply ih a ha n W h ρ (he.refine hi ?_) hw hh
  exact ⟨a, by simp, hv⟩

theorem makeCallable_safeP {G : NormalGraph ι} {P η} {Γ F Bag arity a b n W h ρ}
    {L : List (Ty ι × List (Ty ι) × Ty ι)}
    (hC : ClosedAssign P η) (hr : Represents G F (.callable [(valueField, Bag)] [] L []))
    (hF : ∀ i ∈ F, P i = false) (hlen : ∀ p ∈ L, p.2.1.length = arity)
    (iha : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η Bag) n W h (instantiate 0 ρ a))
    (ihb : ∀ p ∈ L, ∀ j U heap env, EnvOkP G P η (p.1 :: p.2.1 ++ Γ) env j U →
      WorldAdm U → HeapOk j U heap →
      Safe (meaningP G P η p.2.2) j U heap (instantiate 0 env b))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η F) n W h
      (instantiate 0 ρ (.make (.closure arity b) a)) := by
  simp only [instantiate, Nat.zero_add]
  have hcode := invocation_of_bodyP hC he hlen ihb
  apply bind (Tm.make (.closure arity (instantiate (arity + 1) ρ b))) Step.makeC n W h _ hw hh
    (iha n W h ρ he hw hh)
  intro j hj U hx hu heap av hok hav ha'
  have hc : InvocationSpec arity
      (L.map fun p => (meaningP G P η p.1, p.2.1.map (meaningP G P η), meaningP G P η p.2.2))
      j U (instantiate (arity + 1) ρ b) :=
    (codeCallsT_code_iff _ arity [] _ j U).mp ((codeCallsT_adm _).mono j _ U hx _
      ((codeCallsT_adm _).down_le n j hj W _ ((codeCallsT_code_iff _ arity [] _ n W).mpr hcode)))
  have hs := make_callable_rule (meaningP_adm G P η (fun i hi => (hC i hi).1) Bag)
    arity j U heap _ av hc hav hu hok ha'
  exact Safe_mono j (fun k _ V v hv => (represents_semP hr hF k V v).mpr
    ⟨⟨⟨hv.1, by simp⟩, hv.2⟩, hv.2.1, by simp⟩) U heap _ hs

theorem callCallable_safeP {G : NormalGraph ι} {P η} {Γ F Bag Ps Rt B f r n W h ρ}
    {L : List (Ty ι × List (Ty ι) × Ty ι)} {S : List (Ty ι × List (Ty ι) × Ty ι × Ty ι)}
    {xs : List (Ty ι × Tm)}
    (hC : ClosedAssign P η) (hr : Represents G F (.callable Bag Ps L S))
    (hF : ∀ i ∈ F, P i = false) (hp : (Rt, xs.map Prod.fst, B) ∈ L)
    (ihf : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η F) n W h (instantiate 0 ρ f))
    (ihr : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η Rt) n W h (instantiate 0 ρ r))
    (iha : ∀ p ∈ xs, ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η p.1) n W h (instantiate 0 ρ p.2))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η B) n W h
      (instantiate 0 ρ (.invoke f r (xs.map Prod.snd))) := by
  simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
  have hs := call_safe (Rc := meaningP G P η Rt) (B := meaningP G P η B) (f := instantiate 0 ρ f)
    (r := instantiate 0 ρ r)
    (xs.map fun p => (meaningP G P η p.1, instantiate 0 ρ p.2))
    (meaningP_adm G P η (fun i hi => (hC i hi).1) Rt) (meaningP_valOnly hC Rt)
    (by intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact meaningP_adm G P η (fun i hi => (hC i hi).1) q.1)
    (by intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact meaningP_valOnly hC q.1)
    hw hh
  apply (by simpa only [List.map_map, Function.comp_def] using hs)
  · apply Safe_mono n _ W h _ (ihf n W h ρ he hw hh)
    intro k hk U v hv
    simpa only [List.map_map, Function.comp_def] using
      callsT_select (((represents_semP hr hF k U v).mp hv).1.2)
        (List.mem_map.mpr ⟨(Rt, xs.map Prod.fst, B), hp, rfl⟩)
  · intro j hj U hx hu heap hok
    exact ihr j U heap ρ (he.transfer hC j hj U hx) hu hok
  · intro p hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
    intro j hj U hx hu heap hok
    exact iha q hq j U heap ρ (he.transfer hC j hj U hx) hu hok

theorem readCallable_safeP {G : NormalGraph ι} {P η} {Γ a F Bag A f Ps L S n W h ρ}
    (hC : ClosedAssign P η) (hr : Represents G F (.callable Bag Ps L S))
    (hm : (f, A) ∈ Bag) (hF : ∀ i ∈ F, P i = false)
    (ih : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η F) n W h (instantiate 0 ρ a))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ (.readAt f a)) := by
  simp only [instantiate]
  apply bind (Tm.readAt f) Step.readC n W h _ hw hh (ih n W h ρ he hw hh)
  intro j hj U hx hu heap v hok hv ha'
  exact bag_read (meaningP_valOnly hC A) (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
    ((represents_semP hr hF j U v).mp ha').1.1.1 hu hok

theorem writeCallable_safeP {G : NormalGraph ι} {P η} {Γ a b F Bag A f Ps L S N n W h ρ}
    (hC : ClosedAssign P η) (hr : Represents G F (.callable Bag Ps L S))
    (hm : (f, A) ∈ Bag) (hF : ∀ i ∈ F, P i = false) (hn : Represents G N .nul)
    (hN : ∀ i ∈ N, P i = false)
    (iha : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η F) n W h (instantiate 0 ρ a))
    (ihb : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η A) n W h (instantiate 0 ρ b))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η N) n W h (instantiate 0 ρ (.writeAt f a b)) := by
  simp only [instantiate]
  apply bind (fun a => .writeAt f a (instantiate 0 ρ b)) Step.writeC1 n W h _ hw hh
    (iha n W h ρ he hw hh)
  intro j hj U hx hu heap av hok hav ha'
  apply bind (.writeAt f av) (Step.writeC2 hav) j U heap _ hu hok
    (ihb j U heap ρ (he.transfer hC j hj U hx) hu hok)
  intro k hk V hy hv heap' bv hok' hbval hb'
  have ha'' :=
    (meaningP_adm G P η (fun i hi => (hC i hi).1) F).mono k _ V hy av
      ((meaningP_adm G P η (fun i hi => (hC i hi).1) F).down_le j k hk U av ha')
  apply Safe_mono k (fun i _ X v hval => (represents_semP hn hN i X v).mpr hval)
  exact bag_write (meaningP_adm G P η (fun i hi => (hC i hi).1) A)
    (ReferenceConjunctions.mem_famsOf.mpr ⟨A, hm, rfl⟩)
    ((represents_semP hr hF k V av).mp ha'').1.1.1 hb' hbval hv hok'

/-- Generic identity: `function id<T>(x: T): T { return x }`. Label 0 is the
scheme `T → T` for calls whose receiver is label 2, `undefined`; label 1 is the
rigid parameter. -/
def idG : NormalGraph Nat := .ofRows fun
  | 0 => [.arrs [([2], [ [1] ], [1])] []]
  | 2 => [.undef]
  | _ => []

def idP : Nat → Bool := fun i => i == 1

def idSig : List Nat × List (List Nat) × List Nat := ([2], [ [1] ], [1])

theorem id_represents : Represents idG [0] (.arrs [idSig] []) := rfl

theorem id_hasTy : HasTy idG [] (.make (.closure 1 (.var 1)) .nul) [0] :=
  HasTy.funE id_represents
    (fun p hp => by
      have : p = idSig := List.mem_singleton.mp hp
      subst this; decide)
    (fun p hp => by
      have : p = idSig := List.mem_singleton.mp hp
      subst this
      exact HasTy.var rfl)

/-- Source `function fst<T>(x: T, y: T): T { return x }`. -/
theorem fst_generic {η : Nat → Fam} (hC : ClosedAssign idP η)
    (n : Nat) (W : WorldT n) (h : Heap) (ρ : Env)
    (he : EnvOkP idG idP η [[1], [1]] ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP idG idP η [1]) n W h (instantiate 0 ρ (.var 0)) :=
  var_safeP hC rfl he hw hh

theorem id_generic {η : Nat → Fam} (hC : ClosedAssign idP η)
    (n : Nat) (W : WorldT n) (h : Heap) (ρ : Env)
    (he : EnvOkP idG idP η [] ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP idG idP η [0]) n W h
      (instantiate 0 ρ (.make (.closure 1 (.var 1)) .nul)) :=
  funE_safeP hC id_represents
    (fun i hi => by
      have : i = 0 := List.mem_singleton.mp hi
      subst this; rfl)
    (fun p hp => by
      have : p = idSig := List.mem_singleton.mp hp
      subst this; rfl)
    (fun p hp j U heap env he' hu' hh' => by
      have : p = idSig := List.mem_singleton.mp hp
      subst this
      exact var_safeP hC rfl he' hu' hh')
    he hw hh

/-- Instantiating the scheme is specializing the rigid-parameter theorem. -/
theorem id_at_boolean (n : Nat) (W : WorldT n) (h : Heap)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP idG idP (update (fun _ => nulT) 1 boolT) [0]) n W h
      (.make (.closure 1 (.var 1)) .nul) := by
  have hC : ClosedAssign idP (update (fun _ => nulT) 1 boolT) := by
    intro i hi
    have : i = 1 := by simp [idP] at hi; exact hi
    subst i
    simp [update]
    refine ⟨boolT_adm, ?_, ?_⟩
    · intro n W v hv; rcases hv with hv | hv <;> cases hv <;> rfl
    · intro n W v hv; rcases hv with hv | hv <;> cases hv <;> trivial
  have he : EnvOkP idG idP (update (fun _ => nulT) 1 boolT) [] (fun _ => .nul) n W :=
    ⟨fun _ => trivial, fun i A hi => by cases hi⟩
  simpa [instantiate] using id_generic hC n W h (fun _ => .nul) he hw hh

/-- Explicit instantiation: `id<boolean>(true)` is safe at `boolean`. -/
theorem id_call_true (n : Nat) (W : WorldT n) (h : Heap)
    (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP idG idP (update (fun _ => nulT) 1 boolT) [1]) n W h
      (.call (.make (.closure 1 (.var 1)) .nul) [.tru]) := by
  have hC : ClosedAssign idP (update (fun _ => nulT) 1 boolT) := by
    intro i hi
    have : i = 1 := by simp [idP] at hi; exact hi
    subst i
    simp [update]
    refine ⟨boolT_adm, ?_, ?_⟩
    · intro n W v hv; rcases hv with hv | hv <;> cases hv <;> rfl
    · intro n W v hv; rcases hv with hv | hv <;> cases hv <;> trivial
  have he : EnvOkP idG idP (update (fun _ => nulT) 1 boolT) [] (fun _ => .nul) n W :=
    ⟨fun _ => trivial, fun i A hi => by cases hi⟩
  have happ := app_safeP (xs := [([1], Tm.tru)]) (r := .undef) hC id_represents
    (fun i hi => by have : i = 0 := List.mem_singleton.mp hi; subst this; rfl)
    (List.mem_singleton.mpr rfl)
    (fun n W h ρ he hw hh => id_generic hC n W h ρ he hw hh)
    (fun n W h ρ he hw hh => by
      simp only [instantiate]
      exact value_safe _ _ _ _ _ rfl
        ((represents_semP (G := idG) (P := idP) (A := [2]) (c := .undef) rfl
          (fun i hi => by simp at hi; subst hi; rfl) n W .undef).mpr rfl))
    (fun p hp n W h ρ he hw hh => by
      have : p = ([1], Tm.tru) := List.mem_singleton.mp hp
      subst this
      simp only [instantiate]
      exact value_safe _ _ _ _ _ rfl
        ((meaningP_param (by decide : idP 1 = true) n W .tru).mpr (Or.inl rfl)))
    he hw hh
  simpa [instantiate] using happ

/-! ## `extends` as an assumption

A bound `T extends U` is an assumption `T ≤ U` in `Δ`. Successful subtyping
under `Δ` is inclusion for every assignment that satisfies those assumptions.
`T extends boolean` therefore gives `T ≤ boolean`, not `true ≤ T`. -/

def isPrim : Clause α → Bool
  | .nul | .undef | .bool | .boolLit _ => true
  | _ => false

def primitiveTy (G : NormalGraph ι) (P : ι → Bool) (S : List ι) : Prop :=
  ∀ i ∈ S, P i = false ∧ G.plain i = true ∧ ∀ c ∈ G i, isPrim c = true

theorem prim_sem (X Y : α → Fam) (P Q : α → ArgFam) {c : Clause α} (hc : isPrim c = true)
    (n : Nat) (W : WorldT n) (v : Val) : semWithArgs X P c n W v ↔ semWithArgs Y Q c n W v := by
  cases c <;> simp [isPrim] at hc ⊢ <;> rfl

theorem prim_semList (X Y : α → Fam) (P Q : α → ArgFam) {L : List (Clause α)}
    (hL : ∀ c ∈ L, isPrim c = true) (n : Nat) (W : WorldT n) (v : Val) :
    semList X P L n W v ↔ semList Y Q L n W v := by
  simp only [semList, setSem]
  constructor
  · rintro ⟨c, hc, hv⟩
    exact ⟨c, hc, (prim_sem X Y P Q (hL c hc) n W v).mp hv⟩
  · rintro ⟨c, hc, hv⟩
    exact ⟨c, hc, (prim_sem X Y P Q (hL c hc) n W v).mpr hv⟩

theorem primitive_meaningP {G : NormalGraph ι} {P η} {S : List ι}
    (hS : primitiveTy G P S) (n : Nat) (W : WorldT n) (v : Val) :
    meaningP G P η S n W v ↔ meaning G S n W v := by
  simp only [meaningP, meaning, setSem]
  constructor
  · rintro ⟨i, hi, hv⟩
    refine ⟨i, hi, ?_⟩
    have hP := (hS i hi).1
    have hC := (hS i hi).2.2
    have := (unfold_nonparam hP n W v).mp hv
    have hnorm := (unfold_normal G i (hS i hi).2.1 n W v).mpr
      ((prim_semList (meaningP G P η) (meaning G) _ _ hC n W v).mp this)
    exact hnorm
  · rintro ⟨i, hi, hv⟩
    refine ⟨i, hi, ?_⟩
    have hP := (hS i hi).1
    have hC := (hS i hi).2.2
    have := (unfold_normal G i (hS i hi).2.1 n W v).mp hv
    exact (unfold_nonparam hP n W v).mpr
      ((prim_semList (meaningP G P η) (meaning G) _ _ hC n W v).mpr this)

inductive SubP (G : NormalGraph ι) (P : ι → Bool) (Δ : List (ι × List ι)) :
    List ι → List ι → Prop where
  | hyp : (p, U) ∈ Δ → P p = true → SubP G P Δ [p] U
  | ground : primitiveTy G P S → primitiveTy G P T → Sub G S T → SubP G P Δ S T
  | subset : (∀ i ∈ S, i ∈ T) → SubP G P Δ S T
  | trans : SubP G P Δ S U → SubP G P Δ U T → SubP G P Δ S T

def Satisfies (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam)
    (Δ : List (ι × List ι)) : Prop :=
  ∀ p U, (p, U) ∈ Δ → P p = true → FamLe (η p) (meaningP G P η U)

theorem SubP.sound {G : NormalGraph ι} {P η Δ} {S T : List ι}
    (h : SubP G P Δ S T) (hsat : Satisfies G P η Δ) :
    FamLe (meaningP G P η S) (meaningP G P η T) := by
  induction h with
  | hyp hΔ hp =>
    intro n W v hv
    have hη := (meaningP_param hp n W v).mp hv
    exact hsat _ _ hΔ hp n W v hη
  | ground hS hT hg =>
    intro n W v hv
    exact (primitive_meaningP hT n W v).mpr
      (Sub.sound hg n W v ((primitive_meaningP hS n W v).mp hv))
  | subset h =>
    intro n W v ⟨i, hi, hv⟩
    exact ⟨i, h i hi, hv⟩
  | trans _ _ ih ih' =>
    intro n W v hv
    exact ih' n W v (ih n W v hv)

theorem sub_safeP {G : NormalGraph ι} {P η Δ} {A B : List ι} {n W h t}
    (hs : SubP G P Δ A B) (hsat : Satisfies G P η Δ)
    (ht : Safe (meaningP G P η A) n W h t) :
    Safe (meaningP G P η B) n W h t :=
  Safe_mono n (fun m _ => SubP.sound hs hsat m) W h t ht

theorem truLit_safeP {G : NormalGraph ι} {P η} {A Γ n W h ρ}
    (hr : Represents G A (.boolLit true)) (hA : ∀ i ∈ A, P i = false)
    (_he : EnvOkP G P η Γ ρ n W) :
    Safe (meaningP G P η A) n W h (instantiate 0 ρ .tru) := by
  simp only [instantiate]
  exact value_safe _ _ _ _ _ rfl ((represents_semP hr hA n W _).mpr rfl)

theorem letE_safeP {G : NormalGraph ι} {P η} {Γ A B a b n W h ρ}
    (hC : ClosedAssign P η)
    (iha : ∀ n W h ρ, EnvOkP G P η Γ ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η A) n W h (instantiate 0 ρ a))
    (ihb : ∀ n W h ρ, EnvOkP G P η (A :: Γ) ρ n W → WorldAdm W → HeapOk n W h →
      Safe (meaningP G P η B) n W h (instantiate 0 ρ b))
    (he : EnvOkP G P η Γ ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP G P η B) n W h (instantiate 0 ρ (.letE a b)) := by
  simp only [instantiate]
  apply bind (fun a => .letE a (instantiate 1 ρ b)) Step.letC n W h _ hw hh
    (iha n W h ρ he hw hh)
  intro j hj U hx hu heap av hok hav ha'
  cases j with
  | zero => trivial
  | succ k =>
    apply let_rule _ _ hav k U heap hu hok
    rw [instantiate_beta ρ he.1]
    have he' := ((he.transfer hC (k + 1) hj U hx).push_value hC ha').transfer hC
      k (Nat.le_succ k) (trunc k (Nat.le_succ k) U) (WExt_refl _)
    exact ihb k _ heap (push av ρ) he' (WorldAdm_trunc _ hu) (HeapOk_trunc k U heap hok)

/-- Source `function bind<T>(x: T): T { const y: T = x; return y }`. -/
theorem bind_generic {η : Nat → Fam} (hC : ClosedAssign idP η)
    (n : Nat) (W : WorldT n) (h : Heap) (ρ : Env)
    (he : EnvOkP idG idP η [[1]] ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP idG idP η [1]) n W h
      (instantiate 0 ρ (.letE (.var 0) (.var 0))) :=
  letE_safeP hC
    (fun _n _W _h _ρ he hw hh => var_safeP hC rfl he hw hh)
    (fun _n _W _h _ρ he hw hh => var_safeP hC rfl he hw hh)
    he hw hh

/-- `T extends boolean`: label 3 is `T`, labels 1 and 2 are `true` and `false`. -/
def boundG : NormalGraph Nat := .ofRows fun
  | 1 => [.boolLit true]
  | 2 => [.boolLit false]
  | _ => []

def boundP : Nat → Bool := fun i => i == 3
def boundΔ : List (Nat × List Nat) := [(3, [1, 2])]

theorem T_le_boolean : SubP boundG boundP boundΔ [3] [1, 2] :=
  .hyp (List.mem_singleton.mpr rfl) rfl

/-- Source `function asBoolean<T extends boolean>(x: T): boolean { return x }`.
The bound is `T ≤ boolean`; returning `x` at `boolean` is transport along
`SubP`, not `true ≤ T`. -/
theorem asBoolean_generic {η : Nat → Fam} (hC : ClosedAssign boundP η)
    (hsat : Satisfies boundG boundP η boundΔ)
    (n : Nat) (W : WorldT n) (h : Heap) (ρ : Env)
    (he : EnvOkP boundG boundP η [[3]] ρ n W) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaningP boundG boundP η [1, 2]) n W h (instantiate 0 ρ (.var 0)) :=
  sub_safeP T_le_boolean hsat (var_safeP hC rfl he hw hh)

theorem true_le_boolean : SubP boundG boundP boundΔ [1] [1, 2] :=
  .subset fun i hi => by
    have : i = 1 := List.mem_singleton.mp hi
    subst this
    exact List.mem_cons.mpr (Or.inl rfl)

theorem bound_prim_true : primitiveTy boundG boundP [1] := by
  intro i hi
  have : i = 1 := List.mem_singleton.mp hi
  subst this
  exact ⟨rfl, rfl, fun c hc => by simp [boundG] at hc; subst c; rfl⟩

theorem bound_prim_bool : primitiveTy boundG boundP [1, 2] := by
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · exact ⟨rfl, rfl, fun c hc => by simp [boundG] at hc; subst c; rfl⟩
  · have : i = 2 := List.mem_singleton.mp hi
    subst this
    exact ⟨rfl, rfl, fun c hc => by simp [boundG] at hc; subst c; rfl⟩

theorem falseT_satisfies :
    Satisfies boundG boundP (update (fun _ => nulT) 3 falseT) boundΔ := by
  intro p U hpΔ hp
  have : p = 3 := by simp [boundP] at hp; exact hp
  subst this
  have hU : U = [1, 2] := by simp [boundΔ] at hpΔ; cases hpΔ; rfl
  subst hU
  intro n W v hv
  have hv' : v = .fls := by simpa [update, falseT] using hv
  subst hv'
  refine (primitive_meaningP bound_prim_bool n W .fls).mpr ?_
  refine ⟨2, by simp, ?_⟩
  rw [unfold_normal _ _ rfl]
  simp [boundG, semList, setSem, semWithArgs]

#print axioms param_denote
#print axioms instantiate_param
#print axioms instantiate_ref
#print axioms extends_boolean_not_true
#print axioms identity_arrow
#print axioms no_params
#print axioms var_safeP
#print axioms funE_safeP
#print axioms id_generic
#print axioms bind_generic
#print axioms fst_generic
#print axioms id_at_boolean
#print axioms app_safeP
#print axioms alloc_safeP
#print axioms read_safeP
#print axioms write_safeP
#print axioms id_call_true
#print axioms SubP.sound
#print axioms letE_safeP
#print axioms T_le_boolean
#print axioms asBoolean_generic
#print axioms ifBool_safeP
#print axioms unionVar_safeP
#print axioms makeCallable_safeP
#print axioms callCallable_safeP
end Verification.Model.TypeParams
