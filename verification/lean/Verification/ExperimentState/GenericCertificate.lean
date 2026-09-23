import Verification.ExperimentState.DirectObligation
import Verification.ExperimentState.ProgramTyping

/-! # Semantic certificates for rigid source bodies

The source checker may propose one of these proofs, but this module validates
the proof independently and connects every accepted constructor to `Safe`.
The proof language is deliberately extensible: later source forms add a
constructor and its semantic case rather than another acceptance path.
-/
namespace Verification.ExperimentState.GenericCertificate
open ProgramTyping PositiveGraphs PositiveRules Tower
open DirectObligation

/-- The semantic requirements on every interpretation of a rigid name. -/
def ClosedAssign (eta : String -> Fam) : Prop :=
  forall name, Adm (eta name) /\ ValOnly (eta name) /\
    forall n W v, eta name n W v -> Scoped 0 v

/-- Runtime slots distinguish immutable values from private mutable locations.
`cell A` records the location's fixed contract, never its current contents. It
is internal to certificates, not a second source type representation. -/
inductive Slot where
  | value (type : Ty)
  | cell (contract : Ty)
  /-- A raw actual for a defaulted parameter. Only initialization may read it. -/
  | argument (contract : Ty)
  deriving Repr, BEq

def Slot.denote (G : NormalGraph Nat) (eta : String → Fam) : Slot → Fam
  | .value A => A.denote G eta
  | .cell A => bagT [(valueField, A.denote G eta)]
  | .argument A => unionT (A.denote G eta) undefT

/-- A runtime environment realizes the slot contracts in the certificate. -/
def EnvOk (G : NormalGraph Nat) (eta : String -> Fam)
    (Gamma : List Slot) (rho : Env) (n : Nat) (W : WorldT n) : Prop :=
  (forall i, Scoped 0 (rho i)) /\
    forall i (A : Slot), Gamma[i]? = some A -> A.denote G eta n W (rho i)

theorem Ty.denote_adm {G : NormalGraph Nat} {eta} (hC : ClosedAssign eta) :
    forall A : Ty, Adm (A.denote G eta)
  | .rigid name => (hC name).1
  | .ground labels => meaning_adm G labels
  | .top => ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | .arrow _ _ _ => callsT_adm _
  | .array _ => recT_adm _
  | .variadic .. => restsT_adm _

theorem Ty.denote_value {G : NormalGraph Nat} {eta} (hC : ClosedAssign eta)
    {A : Ty} {n W v} (h : A.denote G eta n W v) :
    isVal v = true /\ Scoped 0 v := by
  cases A with
  | rigid name => exact ⟨(hC name).2.1 n W v h, (hC name).2.2 n W v h⟩
  | ground labels => exact ProgramTyping.meaning_value h
  | top => exact h
  | variadic _ _ _ _ | arrow _ params result =>
    exact ⟨h.1.val, h.1.scoped⟩
  | array element =>
    obtain ⟨fields, rfl, _⟩ := h
    exact ⟨rfl, trivial⟩

theorem Slot.denote_adm {G : NormalGraph Nat} {eta} (hC : ClosedAssign eta) :
    ∀ A : Slot, Adm (A.denote G eta)
  | .value A => Ty.denote_adm hC A
  | .cell _ => bagT_adm _
  | .argument A => unionT_adm _ _ (Ty.denote_adm hC A)
      ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

/-- An invocation input is a value or an argument awaiting a default.
Storage identities cannot be passed off as source value parameters. -/
inductive Input where
  | value (type : Ty)
  | defaulted (type : Ty)
  deriving Repr, BEq

def Input.slot : Input → Slot
  | .value A => .value A
  | .defaulted A => .argument A

def Input.denote (G : NormalGraph Nat) (eta : String → Fam) (p : Input) : Fam :=
  p.slot.denote G eta

theorem Input.denote_value {G : NormalGraph Nat} {eta} (hC : ClosedAssign eta)
    {p : Input} {n W v} (h : p.denote G eta n W v) :
    isVal v = true ∧ Scoped 0 v := by
  cases p with
  | value A => exact Ty.denote_value hC h
  | defaulted A =>
    rcases h with h | h
    · exact Ty.denote_value hC h
    · change v = .undef at h
      subst v
      exact ⟨rfl, trivial⟩

theorem EnvOk.transfer {G : NormalGraph Nat} {eta Gamma rho n W}
    (hC : ClosedAssign eta) (he : EnvOk G eta Gamma rho n W)
    (j : Nat) (hj : j <= n) (U : WorldT j) (hx : WExt (trunc j hj W) U) :
    EnvOk G eta Gamma rho j U :=
  ⟨he.1, fun i A hi =>
    (Slot.denote_adm hC A).mono j _ U hx _
      ((Slot.denote_adm hC A).down_le n j hj W _ (he.2 i A hi))⟩

theorem EnvOk.push_value {G : NormalGraph Nat} {eta Gamma rho n W A a}
    (hC : ClosedAssign eta) (he : EnvOk G eta Gamma rho n W)
    (ha : A.denote G eta n W a) :
    EnvOk G eta (.value A :: Gamma) (push a rho) n W := by
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | zero => exact (Ty.denote_value hC ha).2
    | succ i => exact he.1 i
  · intro i B hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst B
      exact ha
    | succ i => exact he.2 i B hi

theorem EnvOk.prependInputs {G : NormalGraph Nat} {eta Gamma rho n W args} {As : List Input}
    (hC : ClosedAssign eta) (he : EnvOk G eta Gamma rho n W)
    (ha : ArgsT (As.map (Input.denote G eta)) n W args) :
    EnvOk G eta (As.map Input.slot ++ Gamma) (prependArgs args rho) n W := by
  induction As generalizing args with
  | nil => cases args <;> simp_all [ArgsT, prependArgs]
  | cons A As ih =>
    cases args with
    | nil => exact False.elim ha
    | cons a args =>
      have he' := ih ha.2
      refine ⟨?_, ?_⟩
      · intro i
        cases i with
        | zero => exact (Input.denote_value hC ha.1).2
        | succ i => exact he'.1 i
      · intro i B hi
        cases i with
        | zero =>
          simp only [List.map_cons, List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at hi
          subst B
          exact ha.1
        | succ i => exact he'.2 i B hi

/-- The same body rule serves nested monomorphic closures and quantified
introduction. Parameters precede the receiver, then the captures, which retain
their runtime values. -/
theorem invocation_of_inputs {G : NormalGraph Nat} {eta Gamma term n W rho}
    {receiver : Ty} {inputs : List Input} {result : Ty}
    (hC : ClosedAssign eta) (he : EnvOk G eta Gamma rho n W)
    (safe : ∀ j U heap env,
      EnvOk G eta (.value receiver :: inputs.map Input.slot ++ Gamma) env j U →
      WorldAdm U → HeapOk j U heap →
      Safe (result.denote G eta) j U heap (instantiate 0 env term)) :
    InvocationSpec inputs.length
      [(receiver.denote G eta, inputs.map (Input.denote G eta), result.denote G eta)]
      n W (instantiate (inputs.length + 1) rho term) := by
  refine ⟨instantiate_scoped rho he.1 term (inputs.length + 1), ?_⟩
  intro p hp j hj U hx hu heap hh r hr args ha
  have hp' : p = (receiver.denote G eta, inputs.map (Input.denote G eta), result.denote G eta) :=
    List.mem_singleton.mp hp
  subst p
  have hlength : args.length = inputs.length := by
    simpa only [List.length_map] using ArgsT_length ha
  have hall : ArgsT ((Input.value receiver :: inputs).map (Input.denote G eta)) j U
      (r :: args) := ⟨hr, ha⟩
  have he' := (he.transfer hC j (Nat.le_of_lt hj) U hx).prependInputs hC hall
  have hscoped : ∀ (As : List Input) args, ArgsT (As.map (Input.denote G eta)) j U args →
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
        · exact (Input.denote_value hC ha.1).2
        · exact ih args ha.2 v hv
  unfold CallArguments.bindParameters
  rw [← hlength, CallArguments.parameters_exact]
  have hl : args.length + 1 = 0 + (r :: args).length := by simp
  rw [hl, instantiate_args rho he.1 (hscoped _ _ hall)]
  exact safe j U heap _ (by simpa [List.append_assoc, Input.slot] using he') hu hh

theorem invocation_of_body {G : NormalGraph Nat} {eta Gamma term n W rho}
    {receiver : Ty} {inputs : List Ty} {result : Ty}
    (hC : ClosedAssign eta) (he : EnvOk G eta Gamma rho n W)
    (safe : ∀ j U heap env,
      EnvOk G eta (.value receiver :: inputs.map Slot.value ++ Gamma) env j U →
      WorldAdm U → HeapOk j U heap →
      Safe (result.denote G eta) j U heap (instantiate 0 env term)) :
    InvocationSpec inputs.length
      [(receiver.denote G eta, inputs.map (Ty.denote G eta), result.denote G eta)]
      n W (instantiate (inputs.length + 1) rho term) := by
  simpa only [List.map_map, List.length_map, Function.comp_def, Input.slot, Input.denote,
    Slot.denote] using invocation_of_inputs (inputs := inputs.map Input.value)
      (receiver := receiver) (result := result) (term := term) hC he (by
        simpa only [List.map_map, Function.comp_def, Input.slot] using safe)

/-- The graph's first four rows are the primitives, as `SourceTypes.initial`
lays them out. A literal's direct type names one of them, so its safety
needs this of the graph; every source table has it. -/
def Primitives (G : NormalGraph Nat) : Prop :=
  G 0 = [.nul] ∧ G 1 = [.boolLit true] ∧ G 2 = [.boolLit false] ∧ G 3 = [.undef]

theorem Primitives.represents_nul {G : NormalGraph Nat} (hG : Primitives G) :
    Represents G [0] .nul := by
  simp [Represents, PositiveRules.expand, hG.1]
theorem Primitives.represents_tru {G : NormalGraph Nat} (hG : Primitives G) :
    Represents G [1] (.boolLit true) := by
  simp [Represents, PositiveRules.expand, hG.2.1]
theorem Primitives.represents_fls {G : NormalGraph Nat} (hG : Primitives G) :
    Represents G [2] (.boolLit false) := by
  simp [Represents, PositiveRules.expand, hG.2.2.1]
theorem Primitives.represents_undef {G : NormalGraph Nat} (hG : Primitives G) :
    Represents G [3] .undef := by
  simp [Represents, PositiveRules.expand, hG.2.2.2]

/-- Producer-independent proof terms for direct source typing. Widening and
call compatibility use subtyping; their Boolean premises are covered by
`DirectObligation.Ty.leUnder_sound`. A primitive literal is its own proof. -/
inductive Proof where
  | var (index : Nat)
  | read (index : Nat)
  | lit (v : Claim.Val)
  | widen (expected : Ty) (body : Proof)
  | letE (init body : Proof)
  /-- Initialize a parameter from its raw argument or a universally checked default.
  The raw slot may additionally contain undefined; initialization binds a new value. -/
  | defaultE (index : Nat) (init : Proof)
  /-- A closure at `(receiver, inputs) => result`: the body sees the receiver,
  then the inputs, then the captures. -/
  | lambda (receiver : Ty) (inputs : List Ty) (body : Proof)
  | call (callee : Proof) (args : List Proof)
  deriving Repr, BEq

/-- Validation reconstructs both the calculus term and its direct type. -/
def Proof.check (parameters : List Parameter) (Gamma : List Slot) :
    Proof -> Option (Tm × Ty)
  | .var index => match Gamma[index]? with
      | some (.value A) => some (.var index, A)
      | some (.cell _) | some (.argument _) | none => none
  | .read index => match Gamma[index]? with
      | some (.cell A) => some (.read (.var index), A)
      | some (.value _) | some (.argument _) | none => none
  | .lit .vnull => some (.nul, .ground [0])
  | .lit .vundef => some (.undef, .ground [3])
  | .lit (.vbool true) => some (.tru, .ground [1])
  | .lit (.vbool false) => some (.fls, .ground [2])
  | .lit _ => none

  | .defaultE index init => do
      let some (.argument B) := Gamma[index]? | none
      let (term, actual) ← init.check parameters Gamma
      if actual.leUnder parameters B then
        some (.ite (.test .isUndef (.var index)) term (.var index), B)
      else none
  | .lambda receiver inputs body =>
      match body.check parameters (.value receiver :: (inputs.map Slot.value ++ Gamma)) with
      | some (term, result) =>
        some (.make (.closure inputs.length term) .nul, .arrow receiver inputs result)
      | none => none
  -- A plain call passes `undefined`: the callee's receiver must admit it.
  | .call callee args => do
      let (fn, .arrow rc inputs result) ← callee.check parameters Gamma | none
      let actuals ← args.mapM (fun arg => arg.check parameters Gamma)
      if (Ty.arrow rc inputs result).leUnder parameters
          (.arrow (.ground [3]) (actuals.map Prod.snd) result) then
        some (.call fn (actuals.map Prod.fst), result)
      else none
  | .widen expected body => match body.check parameters Gamma with
      | some (term, actual) =>
        if actual.leUnder parameters expected then some (term, expected) else none
      | none => none
  | .letE init body => match init.check parameters Gamma with
      | some (a, A) => match body.check parameters (.value A :: Gamma) with
          | some (b, B) => some (.letE a b, B)
          | none => none
      | none => none

private theorem var_safe {G : NormalGraph Nat} {eta Gamma i A n W heap rho}
    (hC : ClosedAssign eta) (hi : Gamma[i]? = some (.value A))
    (he : EnvOk G eta Gamma rho n W) :
    Safe (A.denote G eta) n W heap (instantiate 0 rho (.var i)) := by
  simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  exact value_safe _ _ _ _ _ (Ty.denote_value hC (he.2 _ _ hi)).1 (he.2 _ _ hi)

private theorem let_safe {G : NormalGraph Nat} {eta} {Gamma : List Slot} {A B : Ty}
    {a b n W heap rho}
    (hC : ClosedAssign eta)
    (iha : forall n W heap rho, EnvOk G eta Gamma rho n W -> WorldAdm W -> HeapOk n W heap ->
      Safe (A.denote G eta) n W heap (instantiate 0 rho a))
    (ihb : forall n W heap rho, EnvOk G eta (.value A :: Gamma) rho n W -> WorldAdm W -> HeapOk n W heap ->
      Safe (B.denote G eta) n W heap (instantiate 0 rho b))
    (he : EnvOk G eta Gamma rho n W) (hw : WorldAdm W) (hh : HeapOk n W heap) :
    Safe (B.denote G eta) n W heap (instantiate 0 rho (.letE a b)) := by
  simp only [instantiate]
  apply bind (fun a => .letE a (instantiate 1 rho b)) Step.letC n W heap _ hw hh
    (iha n W heap rho he hw hh)
  intro j hj U hx hu heap' av hok hav ha
  cases j with
  | zero => trivial
  | succ k =>
    apply let_rule _ _ hav k U heap' hu hok
    rw [instantiate_beta rho he.1]
    have he' := ((he.transfer hC (k + 1) hj U hx).push_value hC ha).transfer hC
      k (Nat.le_succ k) (trunc k (Nat.le_succ k) U) (WExt_refl _)
    exact ihb k _ heap' (push av rho) he' (WorldAdm_trunc _ hu)
      (HeapOk_trunc k U heap' hok)

private theorem default_safe {G : NormalGraph Nat} {eta Gamma index B init n W heap rho}
    (hC : ClosedAssign eta)
    (hi : Gamma[index]? = some (.argument B))
    (safe : ∀ n W heap rho, EnvOk G eta Gamma rho n W → WorldAdm W → HeapOk n W heap →
      Safe (B.denote G eta) n W heap (instantiate 0 rho init))
    (he : EnvOk G eta Gamma rho n W) (hw : WorldAdm W) (hh : HeapOk n W heap) :
    Safe (B.denote G eta) n W heap
      (instantiate 0 rho (.ite (.test .isUndef (.var index)) init (.var index))) := by
  have hv := he.2 _ _ hi
  have hvval := (Input.denote_value (p := .defaulted B) hC hv).1
  simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  cases n with
  | zero => trivial
  | succ n =>
    cases n with
    | zero =>
      exact Or.inr ⟨trunc 0 (by omega) W, heap, _, WExt_refl _, WorldAdm_trunc _ hw,
        .iteC (.testV hvval), HeapOk_trunc 0 W heap hh, trivial⟩
    | succ k =>
      apply ite_test_rule .isUndef (rho index) hvval _ _ k W heap hw hh
      · intro _
        exact safe k _ heap rho (he.transfer hC k (by omega) _ (WExt_refl _))
          (WorldAdm_trunc _ hw) (by
            simpa only [trunc_trunc] using HeapOk_trunc k _ heap (HeapOk_trunc (k+1) W heap hh))
      · intro hnot
        have hvalue : B.denote G eta k (trunc k (by omega) W) (rho index) := by
          rcases hv with hb | hu
          · exact (Ty.denote_adm hC B).down_le _ k (by omega) W _ hb
          · change rho index = .undef at hu
            rw [hu] at hnot
            simp [tagHolds] at hnot
        exact value_safe _ _ _ _ _ hvval hvalue

private theorem checked_argument {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; contradiction
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some v =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons, hx, ht] at h
      | some vs =>
        simp [List.mapM_cons, hx, ht] at h
        subst ys
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x, by simp, hx⟩
        · obtain ⟨a, ha, hf⟩ := ih ht hy
          exact ⟨a, by simp [ha], hf⟩

/-- Successful validation is a semantic certificate for every admissible
interpretation satisfying the declared bounds. -/
theorem Proof.check_safe {G : NormalGraph Nat} {parameters} {Gamma : List Slot}
    {proof : Proof} {term : Tm} {A : Ty}
    (hc : proof.check parameters Gamma = some (term, A)) {eta}
    (hC : ClosedAssign eta) (hs : DirectObligation.Satisfies G eta parameters)
    (hG : Primitives G) :
    forall n W heap rho, EnvOk G eta Gamma rho n W -> WorldAdm W -> HeapOk n W heap ->
      Safe (A.denote G eta) n W heap (instantiate 0 rho term) := by
  cases hproof : proof with
  | lit v =>
    simp only [hproof] at hc
    cases v with
    | vnull =>
      simp only [Proof.check, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      intro n W heap rho _ _ _
      exact value_safe _ _ _ _ _ rfl ((represents_sem hG.represents_nul n W _).mpr rfl)
    | vundef =>
      simp only [Proof.check, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      intro n W heap rho _ _ _
      exact value_safe _ _ _ _ _ rfl ((represents_sem hG.represents_undef n W _).mpr rfl)
    | vbool b =>
      cases b with
      | true =>
        simp only [Proof.check, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        intro n W heap rho _ _ _
        exact value_safe _ _ _ _ _ rfl ((represents_sem hG.represents_tru n W _).mpr rfl)
      | false =>
        simp only [Proof.check, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        intro n W heap rho _ _ _
        exact value_safe _ _ _ _ _ rfl ((represents_sem hG.represents_fls n W _).mpr rfl)
    | vnum _ => simp [Proof.check] at hc
    | vstr _ => simp [Proof.check] at hc
  | var index =>
    simp only [hproof] at hc
    cases hi : Gamma[index]? with
    | none => simp [Proof.check, hi] at hc
    | some slot =>
      cases slot with
      | cell A' | argument A' => simp [Proof.check, hi] at hc
      | value A' =>
        simp only [Proof.check, hi, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        intro n W heap rho he _ _
        exact var_safe hC hi he
  | read index =>
    simp only [hproof] at hc
    cases hi : Gamma[index]? with
    | none => simp [Proof.check, hi] at hc
    | some slot =>
      cases slot with
      | value A' | argument A' => simp [Proof.check, hi] at hc
      | cell A' =>
        simp only [Proof.check, hi, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        intro n W heap rho he hw hh
        simp only [Tm.read, instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
        exact bag_read (fun _ _ _ hv => (Ty.denote_value hC hv).1)
          (List.mem_singleton_self _) (he.2 _ _ hi) hw hh
  | widen expected body =>
    simp only [hproof] at hc
    cases hp : body.check parameters Gamma with
    | none => simp [Proof.check, hp] at hc
    | some pair =>
      obtain ⟨t, actual⟩ := pair
      by_cases hle : actual.leUnder parameters expected = true
      · simp only [Proof.check, hp, hle, if_true, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        intro n W heap rho he hw hh
        exact Safe_mono n (fun k _ => Ty.leUnder_sound hs hle k) W heap _
          (Proof.check_safe (proof := body) hp hC hs hG n W heap rho he hw hh)
      · simp [Proof.check, hp, hle] at hc
  | letE init body =>
    simp only [hproof] at hc
    cases hpInit : init.check parameters Gamma with
    | none => simp [Proof.check, hpInit] at hc
    | some pair =>
      obtain ⟨a, TA⟩ := pair
      cases hpBody : body.check parameters (.value TA :: Gamma) with
      | none => simp [Proof.check, hpInit, hpBody] at hc
      | some pair =>
        obtain ⟨b, TB⟩ := pair
        simp only [Proof.check, hpInit, hpBody, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        intro n W heap rho he hw hh
        exact let_safe hC (Proof.check_safe (proof := init) hpInit hC hs hG)
          (Proof.check_safe (proof := body) hpBody hC hs hG) he hw hh
  | defaultE index init =>
    simp only [hproof] at hc
    cases hi : Gamma[index]? with
    | none => simp [Proof.check, hi] at hc
    | some slot =>
      cases slot with
      | cell _ | value _ => simp [Proof.check, hi] at hc
      | argument B =>
        cases hp : init.check parameters Gamma with
        | none => simp [Proof.check, hi, hp] at hc
        | some pair =>
          obtain ⟨t, actual⟩ := pair
          simp only [Proof.check, hi] at hc
          rw [hp] at hc
          change (if actual.leUnder parameters B = true
            then some (Tm.ite (.test .isUndef (.var index)) t (.var index), B)
            else none) = some (term, _) at hc
          split at hc
          · next hle =>
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
            intro n W heap rho he hw hh
            apply default_safe hC hi _ he hw hh
            intro n W heap rho he hw hh
            exact Safe_mono n (fun k _ => Ty.leUnder_sound hs hle k) W heap _
              (Proof.check_safe hp hC hs hG n W heap rho he hw hh)
          · contradiction
  | lambda receiver inputs body =>
    simp only [hproof] at hc
    cases hp : body.check parameters (.value receiver :: (inputs.map Slot.value ++ Gamma)) with
    | none => simp [Proof.check, hp] at hc
    | some pair =>
      obtain ⟨b, B⟩ := pair
      simp only [Proof.check, hp, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      intro n W heap rho he hw hh
      simp only [instantiate, Nat.zero_add]
      have code := invocation_of_body (receiver := receiver) hC he
        (Proof.check_safe (proof := body) hp hC hs hG)
      have hs := make_callable_rule nulT_adm inputs.length n W heap _ .nul code rfl hw hh rfl
      apply Safe_mono n _ W heap _ hs
      intro j hj U v hv
      simpa only [Ty.denote, Ty.denoteList_eq_map] using hv.2
  | call callee args =>
    simp only [hproof] at hc
    cases hf : callee.check parameters Gamma with
    | none => simp [Proof.check, hf] at hc
    | some pair =>
      obtain ⟨f, F⟩ := pair
      cases F with
      | rigid name | array _ | variadic _ _ _ _ | top => simp [Proof.check, hf] at hc
      | ground labels => simp [Proof.check, hf] at hc
      | arrow rc inputs result =>
        cases ha : args.mapM (fun arg => arg.check parameters Gamma) with
        | none => simp [Proof.check, hf, ha] at hc
        | some actuals =>
          by_cases ht : (Ty.arrow rc inputs result).leUnder parameters
              (.arrow (.ground [3]) (actuals.map Prod.snd) result) = true
          · simp [Proof.check, hf, ha, ht] at hc
            obtain ⟨rfl, rfl⟩ := hc
            intro n W heap rho he hw hh
            simp only [instantiate, instantiateArgs_eq_map, List.map_map, Function.comp_def]
            have call := call_safe (Rc := (Ty.ground [3]).denote G eta)
              (B := result.denote G eta) (f := instantiate 0 rho f) (r := .undef)
              (actuals.map fun p => (p.2.denote G eta, instantiate 0 rho p.1))
              (Ty.denote_adm hC _) (fun _ _ _ hv => (Ty.denote_value hC hv).1)
              (by
                intro p hp
                obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
                exact Ty.denote_adm hC q.2)
              (by
                intro p hp
                obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
                exact fun _ _ _ hv => (Ty.denote_value hC hv).1)
              hw hh
            apply (by simpa only [List.map_map, Function.comp_def] using call)
            · have safe := Safe_mono n (fun j _ => Ty.leUnder_sound hs ht j)
                W heap _ (Proof.check_safe (proof := callee) hf hC hs hG n W heap rho he hw hh)
              simpa only [Ty.denote, Ty.denoteList_eq_map, List.map_map,
                Function.comp_def] using safe
            · intro j hj U hx hu heap' hh'
              exact value_safe _ _ _ _ _ rfl
                ((represents_sem hG.represents_undef j U _).mpr rfl)
            · intro p hp
              obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
              obtain ⟨arg, harg, hcArg⟩ := checked_argument ha hq
              intro j hj U hx hu heap' hh'
              exact Proof.check_safe (proof := arg) hcArg hC hs hG j U heap' rho
                (he.transfer hC j hj U hx) hu hh'
          · simp [Proof.check, hf, ha, ht] at hc
termination_by sizeOf proof
decreasing_by
  all_goals simp_all
  all_goals try omega
  all_goals have hsize := List.sizeOf_lt_of_mem harg
  all_goals omega

/-- A complete direct-body certificate. The result is stored separately so
the acceptance boundary checks the reconstructed result against the declared
contract using the proved subtype relation. -/
structure Certificate where
  parameters : List Parameter
  inputs : List Slot
  result : Ty
  proof : Proof
  deriving Repr, BEq

def Certificate.check (c : Certificate) : Option Tm :=
  match c.proof.check c.parameters c.inputs with
  | some (term, result) =>
    if result.leUnder c.parameters c.result then some term else none
  | none => none

/-- The semantic contract represented by a direct-body certificate. -/
def Certificate.Safe (G : NormalGraph Nat) (c : Certificate) : Prop :=
  exists term, c.check = some term /\
    forall eta, ClosedAssign eta -> DirectObligation.Satisfies G eta c.parameters ->
      forall n W heap rho, EnvOk G eta c.inputs rho n W -> WorldAdm W -> HeapOk n W heap ->
        Verification.ExperimentState.Safe (c.result.denote G eta) n W heap
          (instantiate 0 rho term)

theorem Certificate.check_safe {G : NormalGraph Nat} (hG : Primitives G) {c : Certificate} {term}
    (hc : c.check = some term) : c.Safe G := by
  unfold Certificate.check at hc
  cases hp : c.proof.check c.parameters c.inputs with
  | none =>
    rw [hp] at hc
    contradiction
  | some pair =>
    rw [hp] at hc
    obtain ⟨body, result⟩ := pair
    by_cases hr : result.leUnder c.parameters c.result = true
    · change (if result.leUnder c.parameters c.result then some body else none) = some term at hc
      rw [hr] at hc
      cases hc
      refine ⟨term, ?_, ?_⟩
      · simp [Certificate.check, hp, hr]
      · intro eta hC hs n W heap rho he hw hh
        exact Safe_mono n (fun k _ => Ty.leUnder_sound hs hr k) W heap _
          (c.proof.check_safe hp hC hs hG n W heap rho he hw hh)
    · have hf : result.leUnder c.parameters c.result = false := eq_false_of_ne_true hr
      change (if result.leUnder c.parameters c.result then some body else none) = some term at hc
      rw [hf] at hc
      contradiction

#print axioms Proof.check_safe
#print axioms Certificate.check_safe

/-- Collect arbitrary values satisfying one rigid element contract into fresh,
invariant array storage. No instantiation is chosen by this rule. -/
theorem array_collect_safe {G : NormalGraph Nat} {eta} (hC : ClosedAssign eta)
    (E : Ty) {n : Nat} {W : WorldT n} {h : Heap} {extra : List Tm}
    (hw : WorldAdm W) (hh : HeapOk n W h)
    (he : ∀ e ∈ extra, E.denote G eta n W e) :
    Safe ((Ty.array E).denote G eta) n W h (CallArguments.restArray extra) := by
  let S := listT ⟨[], [], some (E.denote G eta), false⟩
  apply bind_list [(S, .arrLit extra)] (by simp [S, listT_adm])
    (fun args => .makeAt .absent [CallArguments.arrayStoreField] args)
    (fun hs => CallArguments.Step.makeArgs hs) hw hh
  · intro p hp j hj U hx hu heap hok
    simp only [List.mem_singleton] at hp
    subst p
    have he' : ∀ e ∈ extra, E.denote G eta j U e := fun e hm =>
      (Ty.denote_adm hC E).mono j _ U hx e
        ((Ty.denote_adm hC E).down_le n j hj W e (he e hm))
    apply arr_alloc_rule (As := List.replicate extra.length (E.denote G eta))
      (by intro A hA; rw [List.eq_of_mem_replicate hA]; exact Ty.denote_adm hC E)
      j U heap extra (by simp) (fun v hv => (Ty.denote_value hC (he' v hv)).1) hu hok
      (by
        intro p hp
        rw [List.eq_of_mem_replicate (List.of_mem_zip hp).1]
        exact he' p.2 (List.of_mem_zip hp).2)
    intro k hk V hy hl
    have ht := listT_alloc (T := ⟨[], [], some (E.denote G eta), false⟩)
      (As := List.replicate extra.length (E.denote G eta))
      (by simp) (by simp) (by
        intro i A hA
        obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hA
        simp [positionFam]) hl
    simpa [S] using ht
  · intro j hj U hx hu heap args hok hargs
    have hlen := ArgsT_length hargs
    apply make_fields_rule (As := [S]) (by simp [S, listT_adm]) j U heap .absent
      [CallArguments.arrayStoreField] args (by simp) (by simpa using hlen.symm)
      (by simpa using hlen.symm)
      (ArgsT_values (by
        intro A hA
        change A ∈ [S] at hA
        rw [List.mem_singleton] at hA
        subst A
        intro k V v hv
        obtain ⟨ls, rfl, _⟩ := hv
        rfl) hargs) hu hok (ArgsT_zip hargs)
    intro k hk V hy hrec
    exact hrec

/-- The universal body premise becomes a variadic code contract by allocating
slot zero and binding the fixed arguments after it. Captures keep their one
environment across every interpretation of the quantified element type. -/
theorem rest_invocation_of_inputs {G : NormalGraph Nat} {eta Gamma term n W rho}
    {receiver : Ty} {inputs : List Input} {element result : Ty}
    (hC : ClosedAssign eta) (he : EnvOk G eta Gamma rho n W)
    (safe : ∀ j U heap env,
      EnvOk G eta (.value (.array element) :: .value receiver :: inputs.map Input.slot ++ Gamma)
        env j U →
      WorldAdm U → HeapOk j U heap →
      Safe (result.denote G eta) j U heap (instantiate 0 env term)) :
    RestCalls.RestSpec inputs.length (receiver.denote G eta) (inputs.map (Input.denote G eta))
      (element.denote G eta) (result.denote G eta) n W
      (instantiate (inputs.length + 2) rho term) := by
  apply RestCalls.restSpec_of_body (instantiate_scoped rho he.1 term (inputs.length + 2))
    (by simp) (Ty.denote_adm hC receiver) (by
      intro A hA
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hA
      exact Slot.denote_adm hC p.slot)
    (Ty.denote_adm hC (.array element))
    (fun _ _ _ _ hw hh hx => array_collect_safe hC element hw hh hx)
  intro j hj U hx hu heap hh r hr args a ha harr _
  have hall : ArgsT ((Input.value receiver :: inputs).map (Input.denote G eta)) j U
      (r :: args) := ⟨hr, ha⟩
  have he' := (he.transfer hC j (Nat.le_of_lt hj) U hx).prependInputs hC hall
  have argsScoped : ∀ (ps : List Input) args, ArgsT (ps.map (Input.denote G eta)) j U args →
      ∀ a ∈ args, Scoped 0 a := by
    intro ps
    induction ps with
    | nil => intro args h; cases args <;> simp_all [ArgsT]
    | cons p ps ih =>
      intro args h
      cases args with
      | nil => exact False.elim h
      | cons a args =>
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact (Input.denote_value hC h.1).2
        · exact ih args h.2 v hv
  have hsc := argsScoped _ _ hall
  have hl : args.length = inputs.length := by simpa using ArgsT_length ha
  have hbeta := instantiate_beta _ (prependArgs_scoped hsc he.1) a term 0
  rw [Nat.zero_add] at hbeta
  rw [show inputs.length + 2 = 1 + (r :: args).length by simp; omega,
    instantiate_args rho he.1 hsc term 1, hbeta]
  exact safe j U heap _ (by simpa [List.append_assoc, Input.slot] using he'.push_value hC harr)
    hu hh

/-- A closure checks its parameters before its captures. The captured runtime
environment is held fixed across all interpretations of the quantified names. -/
structure ClosureCertificate where
  parameters : List Parameter
  inputs : List Input
  captures : List Slot
  result : Ty
  proof : Proof
  rest : Option Ty := none
  /-- The receiver the code binds before its parameters; a closure indifferent
  to it states top. -/
  receiver : Ty := .top
  deriving Repr, BEq

def ClosureCertificate.body (c : ClosureCertificate) : Certificate :=
  ⟨c.parameters, (match c.rest with
    | none => .value c.receiver :: c.inputs.map Input.slot ++ c.captures
    | some E => .value (.array E) :: .value c.receiver :: c.inputs.map Input.slot ++ c.captures),
    c.result, c.proof⟩

def ClosureCertificate.check (c : ClosureCertificate) : Option Tm := c.body.check

/-- Universal code safety in one captured environment and world. This is the
invocation premise of scheme introduction, not a list of observed instances. -/
def ClosureCertificate.Safe (G : NormalGraph Nat) (c : ClosureCertificate) : Prop :=
  ∃ term, c.check = some term ∧
    ∀ n W rho,
      (∀ eta, ClosedAssign eta → DirectObligation.Satisfies G eta c.parameters →
        EnvOk G eta c.captures rho n W) →
      ∀ eta, ClosedAssign eta → DirectObligation.Satisfies G eta c.parameters →
        match c.rest with
        | none => InvocationSpec c.inputs.length
            [(c.receiver.denote G eta, c.inputs.map (Input.denote G eta), c.result.denote G eta)]
            n W (instantiate (c.inputs.length + 1) rho term)
        | some E => RestCalls.RestSpec c.inputs.length (c.receiver.denote G eta)
            (c.inputs.map (Input.denote G eta))
            (E.denote G eta) (c.result.denote G eta) n W
            (instantiate (c.inputs.length + 2) rho term)

theorem ClosureCertificate.check_safe {G : NormalGraph Nat} (hG : Primitives G)
    {c : ClosureCertificate} {term} (hc : c.check = some term) : c.Safe G := by
  refine ⟨term, hc, ?_⟩
  intro n W rho henv eta hC hs
  have he := henv eta hC hs
  obtain ⟨body, hb, safe⟩ := Certificate.check_safe (G := G) hG hc
  have eq : body = term := Option.some.inj (hb.symm.trans hc)
  subst body
  cases hr : c.rest with
  | none => exact invocation_of_inputs hC he (by simpa [ClosureCertificate.body, hr] using safe eta hC hs)
  | some E =>
    exact rest_invocation_of_inputs hC he
      (by simpa [ClosureCertificate.body, hr] using safe eta hC hs)

#print axioms invocation_of_inputs
#print axioms invocation_of_body
#print axioms ClosureCertificate.check_safe
end Verification.ExperimentState.GenericCertificate
