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

/-- A runtime environment realizes the direct types in the certificate. -/
def EnvOk (G : NormalGraph Nat) (eta : String -> Fam)
    (Gamma : List Ty) (rho : Env) (n : Nat) (W : WorldT n) : Prop :=
  (forall i, Scoped 0 (rho i)) /\
    forall i (A : Ty), Gamma[i]? = some A -> Ty.denote G eta A n W (rho i)

theorem Ty.denote_adm {G : NormalGraph Nat} {eta} (hC : ClosedAssign eta) :
    forall A : Ty, Adm (A.denote G eta)
  | .rigid name => (hC name).1
  | .ground labels => meaning_adm G labels
  | .arrow _ _ => callsT_adm _

theorem Ty.denote_value {G : NormalGraph Nat} {eta} (hC : ClosedAssign eta)
    {A : Ty} {n W v} (h : A.denote G eta n W v) :
    isVal v = true /\ Scoped 0 v := by
  cases A with
  | rigid name => exact ⟨(hC name).2.1 n W v h, (hC name).2.2 n W v h⟩
  | ground labels => exact ProgramTyping.meaning_value h
  | arrow params result =>
    exact ⟨(callsT_callable h).val, (callsT_callable h).scoped⟩

theorem EnvOk.transfer {G : NormalGraph Nat} {eta Gamma rho n W}
    (hC : ClosedAssign eta) (he : EnvOk G eta Gamma rho n W)
    (j : Nat) (hj : j <= n) (U : WorldT j) (hx : WExt (trunc j hj W) U) :
    EnvOk G eta Gamma rho j U :=
  ⟨he.1, fun i A hi =>
    (Ty.denote_adm hC A).mono j _ U hx _
      ((Ty.denote_adm hC A).down_le n j hj W _ (he.2 i A hi))⟩

theorem EnvOk.push_value {G : NormalGraph Nat} {eta Gamma rho n W A a}
    (hC : ClosedAssign eta) (he : EnvOk G eta Gamma rho n W)
    (ha : A.denote G eta n W a) :
    EnvOk G eta (A :: Gamma) (push a rho) n W := by
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

/-- Producer-independent proof terms for direct source typing. `widen` is the
only place subtyping enters; its Boolean premise is covered by
`DirectObligation.Ty.leUnder_sound`. -/
inductive Proof where
  | var (index : Nat)
  | widen (expected : Ty) (body : Proof)
  | letE (init body : Proof)
  deriving Repr, BEq

/-- Validation reconstructs both the calculus term and its direct type. -/
def Proof.check (parameters : List Parameter) (Gamma : List Ty) :
    Proof -> Option (Tm × Ty)
  | .var index => match Gamma[index]? with
      | some A => some (.var index, A)
      | none => none
  | .widen expected body => match body.check parameters Gamma with
      | some (term, actual) =>
        if actual.leUnder parameters expected then some (term, expected) else none
      | none => none
  | .letE init body => match init.check parameters Gamma with
      | some (a, A) => match body.check parameters (A :: Gamma) with
          | some (b, B) => some (.letE a b, B)
          | none => none
      | none => none

private theorem var_safe {G : NormalGraph Nat} {eta Gamma i A n W heap rho}
    (hC : ClosedAssign eta) (hi : Gamma[i]? = some A)
    (he : EnvOk G eta Gamma rho n W) :
    Safe (A.denote G eta) n W heap (instantiate 0 rho (.var i)) := by
  simp only [instantiate, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  exact value_safe _ _ _ _ _ (Ty.denote_value hC (he.2 _ _ hi)).1 (he.2 _ _ hi)

private theorem let_safe {G : NormalGraph Nat} {eta} {Gamma : List Ty} {A B : Ty}
    {a b n W heap rho}
    (hC : ClosedAssign eta)
    (iha : forall n W heap rho, EnvOk G eta Gamma rho n W -> WorldAdm W -> HeapOk n W heap ->
      Safe (A.denote G eta) n W heap (instantiate 0 rho a))
    (ihb : forall n W heap rho, EnvOk G eta (A :: Gamma) rho n W -> WorldAdm W -> HeapOk n W heap ->
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

/-- Successful validation is a semantic certificate for every admissible
interpretation satisfying the declared bounds. -/
theorem Proof.check_safe {G : NormalGraph Nat} {parameters} {Gamma : List Ty}
    {proof : Proof} {term : Tm} {A : Ty}
    (hc : proof.check parameters Gamma = some (term, A)) {eta}
    (hC : ClosedAssign eta) (hs : DirectObligation.Satisfies G eta parameters) :
    forall n W heap rho, EnvOk G eta Gamma rho n W -> WorldAdm W -> HeapOk n W heap ->
      Safe (A.denote G eta) n W heap (instantiate 0 rho term) := by
  induction proof generalizing Gamma term A with
  | var index =>
    cases hi : Gamma[index]? with
    | none => simp [Proof.check, hi] at hc
    | some A' =>
      simp only [Proof.check, hi, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      intro n W heap rho he _ _
      exact var_safe hC hi he
  | widen expected body ih =>
    cases hp : body.check parameters Gamma with
    | none => simp [Proof.check, hp] at hc
    | some pair =>
      obtain ⟨t, actual⟩ := pair
      by_cases hle : actual.leUnder parameters expected = true
      · simp only [Proof.check, hp, hle, if_true, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        intro n W heap rho he hw hh
        exact Safe_mono n (fun k _ => Ty.leUnder_sound hs hle k) W heap _
          (ih hp n W heap rho he hw hh)
      · simp [Proof.check, hp, hle] at hc
  | letE init body ihInit ihBody =>
    cases hpInit : init.check parameters Gamma with
    | none => simp [Proof.check, hpInit] at hc
    | some pair =>
      obtain ⟨a, TA⟩ := pair
      cases hpBody : body.check parameters (TA :: Gamma) with
      | none => simp [Proof.check, hpInit, hpBody] at hc
      | some pair =>
        obtain ⟨b, TB⟩ := pair
        simp only [Proof.check, hpInit, hpBody, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        intro n W heap rho he hw hh
        exact let_safe hC (ihInit hpInit) (ihBody hpBody) he hw hh

/-- A complete direct-body certificate. The result is stored separately so
the acceptance boundary can demand that proof checking reconstruct exactly
the declared contract. -/
structure Certificate where
  parameters : List Parameter
  inputs : List Ty
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

theorem Certificate.check_safe {G : NormalGraph Nat} {c : Certificate} {term}
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
          (c.proof.check_safe hp hC hs n W heap rho he hw hh)
    · have hf : result.leUnder c.parameters c.result = false := eq_false_of_ne_true hr
      change (if result.leUnder c.parameters c.result then some body else none) = some term at hc
      rw [hf] at hc
      contradiction

#print axioms Proof.check_safe
#print axioms Certificate.check_safe
end Verification.ExperimentState.GenericCertificate
