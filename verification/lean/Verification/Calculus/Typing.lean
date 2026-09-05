import Verification.Calculus.Narrowing

namespace Verification
namespace Core

/-! ## Typing

The rules are syntax-directed, with subsumption folded into each one rather
than standing as a separate rule: one constructor per expression form, so a
derivation inverts in a single step, and `HasTy_sub` recovers subsumption as
an admissible rule.

The `const` rule ignores its annotation. Which type an annotation permits for
the binding is a question for a checker; all soundness needs is that the
binding's type contains the initialiser's value. -/

mutual

inductive HasTy : Prog → TEnv → Exp → Ty → Prop where
  | var : tenvGet Γ x = some t0 → sub t0 t = true → HasTy p Γ (.var x) t
  | lit : sub (ofAtom (atomOfVal w)) t = true → HasTy p Γ (.lit w) t
  | not : HasTy p Γ e bool_ → sub bool_ t = true → HasTy p Γ (.not e) t
  | eq : HasTy p Γ l tl → HasTy p Γ r tr → sub bool_ t = true → HasTy p Γ (.eq l r) t
  | ne : HasTy p Γ l tl → HasTy p Γ r tr → sub bool_ t = true → HasTy p Γ (.ne l r) t
  | tyof : HasTy p Γ e te → sub (tagsOf te) t = true → HasTy p Γ (.tyof e) t
  | and : HasTy p Γ l bool_ → HasTy p (narrow Γ l true) r bool_ → sub bool_ t = true →
      HasTy p Γ (.and l r) t
  | or : HasTy p Γ l bool_ → HasTy p (narrow Γ l false) r bool_ → sub bool_ t = true →
      HasTy p Γ (.or l r) t
  | call : lookupFun p f = some fn → HasTyArgs p Γ args fn.params → sub fn.ret t = true →
      HasTy p Γ (.call f args) t

inductive HasTyArgs : Prog → TEnv → List Exp → List (String × Ty) → Prop where
  | nil : HasTyArgs p Γ [] []
  | cons : HasTy p Γ a t → HasTyArgs p Γ as ps → HasTyArgs p Γ (a :: as) ((x, t) :: ps)

end

/-- A block is well-typed when every path through it returns a value in `tr`.
There is deliberately no rule for the empty block: falling off the end is not
a way to leave a function, and that is the whole content of "every branch
must return". An `if` types its branch followed by whatever came after, so a
branch that returns never has to account for the rest. -/
inductive BlockOk : Prog → TEnv → Ty → List Stm → Prop where
  | ret : HasTy p Γ e tr → BlockOk p Γ tr (.ret e :: rest)
  | cst : HasTy p Γ init d → BlockOk p (tenvSet Γ x d) tr rest →
      BlockOk p Γ tr (.cst x annot init :: rest)
  | ite : HasTy p Γ c bool_ →
      BlockOk p (narrow Γ c true) tr (thn ++ rest) →
      BlockOk p (narrow Γ c false) tr (els ++ rest) →
      BlockOk p Γ tr (.ite c thn els :: rest)

def FnOk (p : Prog) (fn : Fn) : Prop := BlockOk p fn.params fn.ret fn.body

/-- Every function of the program checks against its own declared signature.
A call is therefore never given a rule of its own: `ProgOk` is the hypothesis
`sound` discharges for the whole program at once. -/
def ProgOk (p : Prog) : Prop := ∀ fn ∈ p, FnOk p fn

/-! ## Arguments and parameter binding -/

theorem MemAll_length {vs : List Val} {ps : List (String × Ty)} (h : MemAll vs ps) :
    vs.length = ps.length := by
  induction vs generalizing ps with
  | nil => cases ps with
    | nil => rfl
    | cons q qs => simp [MemAll] at h
  | cons v vs ih => cases ps with
    | nil => simp [MemAll] at h
    | cons q qs =>
      obtain ⟨x, t⟩ := q
      simp only [MemAll] at h
      simp [ih h.2]

theorem agree_cons {ρ Γ x v t} (h : agree ρ Γ) (hm : mem v t) :
    agree (venvSet ρ x v) (tenvSet Γ x t) := by
  intro y ty hy
  by_cases hxy : x = y
  · subst hxy
    simp [tenvSet, tenvGet] at hy
    subst hy
    exact ⟨v, by simp [venvSet, venvGet], hm⟩
  · have hne : (x == y) = false := by simp [hxy]
    simp [tenvSet, tenvGet, hne] at hy
    obtain ⟨v', hv', hm'⟩ := h y ty hy
    refine ⟨v', ?_, hm'⟩
    simp [venvSet, venvGet, hne, hv']

theorem agree_bindParams {vs : List Val} {ps : List (String × Ty)} (h : MemAll vs ps) :
    agree (bindParams ps vs) ps := by
  induction vs generalizing ps with
  | nil =>
    cases ps with
    | nil => intro y ty hy; simp [tenvGet] at hy
    | cons q qs => simp [MemAll] at h
  | cons v vs ih =>
    cases ps with
    | nil => simp [MemAll] at h
    | cons q qs =>
      obtain ⟨x, t⟩ := q
      simp only [MemAll] at h
      intro y ty hy
      by_cases hxy : x = y
      · subst hxy
        simp [tenvGet] at hy
        subst hy
        exact ⟨v, by simp [bindParams, venvGet], h.1⟩
      · have hne : (x == y) = false := by simp [hxy]
        simp [tenvGet, hne] at hy
        obtain ⟨v', hv', hm'⟩ := ih h.2 y ty hy
        refine ⟨v', ?_, hm'⟩
        simp [bindParams, venvGet, hne, hv']

/-! ## Soundness

Preservation and progress together, by induction on the fuel. Every recursive
call in the evaluator is at one less fuel, so the induction hypothesis covers
callees as well as sub-expressions -- which is exactly why a call to another
function needs no assumption of its own. -/

theorem sound {p : Prog} (hp : ProgOk p) (n : Nat) :
    (∀ ρ Γ e t, agree ρ Γ → HasTy p Γ e t →
        evalE p n ρ e ≠ .stuck ∧ ∀ v, evalE p n ρ e = .ok v → mem v t)
  ∧ (∀ ρ Γ as ps, agree ρ Γ → HasTyArgs p Γ as ps →
        evalArgs p n ρ as ≠ .stuck ∧ ∀ vs, evalArgs p n ρ as = .ok vs → MemAll vs ps)
  ∧ (∀ ρ Γ b tr, agree ρ Γ → BlockOk p Γ tr b →
        execB p n ρ b ≠ .stuck ∧ ∀ v, execB p n ρ b = .ok v → mem v tr) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intro ρ Γ a b _ _ <;> simp [evalE, evalArgs, execB]
  | succ n ih =>
    obtain ⟨ihE, ihA, ihB⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    -- expressions
    · intro ρ Γ e t hG hty
      cases e with
      | var x =>
        cases hty with
        | var ht hsub =>
          obtain ⟨v, hv, hm⟩ := hG _ _ ht
          simp only [evalE, hv]
          exact ⟨by simp, fun v' hv' => by cases hv'; exact sub_sound hsub hm⟩
      | lit w =>
        cases hty with
        | lit hsub =>
          simp only [evalE]
          exact ⟨by simp, fun v' hv' => by cases hv'; exact sub_sound hsub (mem_atomOfVal _)⟩
      | not e1 =>
        cases hty with
        | not he hsub =>
          obtain ⟨hns, hpres⟩ := ihE ρ Γ e1 bool_ hG he
          cases hev : evalE p n ρ e1 with
          | ok v =>
            obtain ⟨b, rfl⟩ := mem_bool_inv (hpres v hev)
            simp only [evalE, hev]
            exact ⟨by simp, fun v' hv' => by cases hv'; exact sub_sound hsub mem_bool⟩
          | stuck => exact absurd hev hns
          | timeout => simp [evalE, hev]
      | eq l r =>
        cases hty with
        | eq hl hr hsub =>
          obtain ⟨hns1, _⟩ := ihE ρ Γ l _ hG hl
          obtain ⟨hns2, _⟩ := ihE ρ Γ r _ hG hr
          cases hev1 : evalE p n ρ l with
          | ok a =>
            cases hev2 : evalE p n ρ r with
            | ok c =>
              simp only [evalE, hev1, hev2]
              exact ⟨by simp, fun v' hv' => by cases hv'; exact sub_sound hsub mem_bool⟩
            | stuck => exact absurd hev2 hns2
            | timeout => simp [evalE, hev1, hev2]
          | stuck => exact absurd hev1 hns1
          | timeout => simp [evalE, hev1]
      | ne l r =>
        cases hty with
        | ne hl hr hsub =>
          obtain ⟨hns1, _⟩ := ihE ρ Γ l _ hG hl
          obtain ⟨hns2, _⟩ := ihE ρ Γ r _ hG hr
          cases hev1 : evalE p n ρ l with
          | ok a =>
            cases hev2 : evalE p n ρ r with
            | ok c =>
              simp only [evalE, hev1, hev2]
              exact ⟨by simp, fun v' hv' => by cases hv'; exact sub_sound hsub mem_bool⟩
            | stuck => exact absurd hev2 hns2
            | timeout => simp [evalE, hev1, hev2]
          | stuck => exact absurd hev1 hns1
          | timeout => simp [evalE, hev1]
      | tyof e1 =>
        cases hty with
        | tyof he hsub =>
          obtain ⟨hns, hpres⟩ := ihE ρ Γ e1 _ hG he
          cases hev : evalE p n ρ e1 with
          | ok v =>
            simp only [evalE, hev]
            exact ⟨by simp, fun v' hv' => by
              cases hv'; exact sub_sound hsub (mem_tagsOf (hpres v hev))⟩
          | stuck => exact absurd hev hns
          | timeout => simp [evalE, hev]
      | and l r =>
        cases hty with
        | and hl hr hsub =>
          obtain ⟨hns1, hp1⟩ := ihE ρ Γ l bool_ hG hl
          cases hev1 : evalE p n ρ l with
          | ok a =>
            obtain ⟨b1, rfl⟩ := mem_bool_inv (hp1 a hev1)
            cases b1
            · simp only [evalE, hev1]
              exact ⟨by simp, fun v' hv' => by cases hv'; exact sub_sound hsub mem_bool⟩
            · have hG2 : agree ρ (narrow Γ l true) := narrow_sound p n ρ Γ l true hG hev1
              obtain ⟨hns2, hp2⟩ := ihE ρ (narrow Γ l true) r bool_ hG2 hr
              cases hev2 : evalE p n ρ r with
              | ok c =>
                obtain ⟨b2, rfl⟩ := mem_bool_inv (hp2 c hev2)
                simp only [evalE, hev1, hev2]
                exact ⟨by simp, fun v' hv' => by cases hv'; exact sub_sound hsub mem_bool⟩
              | stuck => exact absurd hev2 hns2
              | timeout => simp [evalE, hev1, hev2]
          | stuck => exact absurd hev1 hns1
          | timeout => simp [evalE, hev1]
      | or l r =>
        cases hty with
        | or hl hr hsub =>
          obtain ⟨hns1, hp1⟩ := ihE ρ Γ l bool_ hG hl
          cases hev1 : evalE p n ρ l with
          | ok a =>
            obtain ⟨b1, rfl⟩ := mem_bool_inv (hp1 a hev1)
            cases b1
            · have hG2 : agree ρ (narrow Γ l false) := narrow_sound p n ρ Γ l false hG hev1
              obtain ⟨hns2, hp2⟩ := ihE ρ (narrow Γ l false) r bool_ hG2 hr
              cases hev2 : evalE p n ρ r with
              | ok c =>
                obtain ⟨b2, rfl⟩ := mem_bool_inv (hp2 c hev2)
                simp only [evalE, hev1, hev2]
                exact ⟨by simp, fun v' hv' => by cases hv'; exact sub_sound hsub mem_bool⟩
              | stuck => exact absurd hev2 hns2
              | timeout => simp [evalE, hev1, hev2]
            · simp only [evalE, hev1]
              exact ⟨by simp, fun v' hv' => by cases hv'; exact sub_sound hsub mem_bool⟩
          | stuck => exact absurd hev1 hns1
          | timeout => simp [evalE, hev1]
      | call f args =>
        cases hty with
        | call hlk hargs hsub =>
          rename_i fn
          obtain ⟨hnsA, hpA⟩ := ihA ρ Γ args fn.params hG hargs
          cases heva : evalArgs p n ρ args with
          | ok vs =>
            have hma : MemAll vs fn.params := hpA vs heva
            have hlen : (vs.length == fn.params.length) = true := by
              simp [MemAll_length hma]
            have hfn : fn ∈ p := List.mem_of_find?_eq_some hlk
            obtain ⟨hnsB, hpB⟩ := ihB (bindParams fn.params vs) fn.params fn.body fn.ret
              (agree_bindParams hma) (hp fn hfn)
            simp only [evalE, hlk, heva, hlen, if_true]
            exact ⟨hnsB, fun v hv => sub_sound hsub (hpB v hv)⟩
          | stuck => exact absurd heva hnsA
          | timeout => simp [evalE, hlk, heva]
    -- argument lists
    · intro ρ Γ as ps hG hargs
      cases as with
      | nil => cases hargs with | nil => simp [evalArgs, MemAll]
      | cons a as' =>
        cases hargs with
        | cons hta htas =>
          obtain ⟨hns1, hp1⟩ := ihE ρ Γ a _ hG hta
          obtain ⟨hns2, hp2⟩ := ihA ρ Γ as' _ hG htas
          cases hev1 : evalE p n ρ a with
          | ok v =>
            cases hev2 : evalArgs p n ρ as' with
            | ok vs =>
              simp only [evalArgs, hev1, hev2]
              refine ⟨by simp, ?_⟩
              intro vs' hvs'
              cases hvs'
              simp only [MemAll]
              exact ⟨hp1 v hev1, hp2 vs hev2⟩
            | stuck => exact absurd hev2 hns2
            | timeout => simp [evalArgs, hev1, hev2]
          | stuck => exact absurd hev1 hns1
          | timeout => simp [evalArgs, hev1]
    -- blocks
    · intro ρ Γ b tr hG hb
      cases b with
      | nil => cases hb
      | cons s rest =>
        cases s with
        | ret e =>
          cases hb with
          | ret hte =>
            simp only [execB]
            exact ihE ρ Γ e tr hG hte
        | cst x annot init =>
          cases hb with
          | cst hinit hrest =>
            rename_i d
            obtain ⟨hns1, hp1⟩ := ihE ρ Γ init d hG hinit
            cases hev : evalE p n ρ init with
            | ok v =>
              obtain ⟨hns2, hp2⟩ := ihB (venvSet ρ x v) (tenvSet Γ x d) rest tr
                (agree_cons hG (hp1 v hev)) hrest
              simp only [execB, hev]
              exact ⟨hns2, hp2⟩
            | stuck => exact absurd hev hns1
            | timeout => simp [execB, hev]
        | ite c thn els =>
          cases hb with
          | ite hc hthn hels =>
            obtain ⟨hns1, hp1⟩ := ihE ρ Γ c bool_ hG hc
            cases hev : evalE p n ρ c with
            | ok v =>
              obtain ⟨bb, rfl⟩ := mem_bool_inv (hp1 v hev)
              cases bb
              · obtain ⟨hns2, hp2⟩ := ihB ρ (narrow Γ c false) (els ++ rest) tr
                  (narrow_sound p n ρ Γ c false hG hev) hels
                simp only [execB, hev]
                exact ⟨hns2, hp2⟩
              · obtain ⟨hns2, hp2⟩ := ihB ρ (narrow Γ c true) (thn ++ rest) tr
                  (narrow_sound p n ρ Γ c true hG hev) hthn
                simp only [execB, hev]
                exact ⟨hns2, hp2⟩
            | stuck => exact absurd hev hns1
            | timeout => simp [execB, hev]

/-! ## What the theorem says

Calling a function of a well-typed program with arguments that inhabit its
parameter types cannot go wrong, and if it produces a value at all then that
value inhabits the declared return type. -/

theorem call_never_stuck {p : Prog} (hp : ProgOk p) {fn : Fn} (hfn : fn ∈ p)
    {vs : List Val} (hma : MemAll vs fn.params) (n : Nat) :
    execB p n (bindParams fn.params vs) fn.body ≠ .stuck :=
  ((sound hp n).2.2 _ _ _ _ (agree_bindParams hma) (hp fn hfn)).1

theorem call_returns_in_type {p : Prog} (hp : ProgOk p) {fn : Fn} (hfn : fn ∈ p)
    {vs : List Val} (hma : MemAll vs fn.params) (n : Nat) {v : Val}
    (h : execB p n (bindParams fn.params vs) fn.body = .ok v) : mem v fn.ret :=
  ((sound hp n).2.2 _ _ _ _ (agree_bindParams hma) (hp fn hfn)).2 v h

/-- Subsumption, admissible. Because every rule carries its own `sub` side
condition, weakening is a single case split composed with `sub_trans` -- no
induction on the derivation, which is what keeps inversion one step deep. -/
theorem HasTy_sub {p Γ e t t'} (h : HasTy p Γ e t) (hs : sub t t' = true) :
    HasTy p Γ e t' := by
  cases h with
  | var ht hsub => exact .var ht (sub_trans hsub hs)
  | lit hsub => exact .lit (sub_trans hsub hs)
  | not he hsub => exact .not he (sub_trans hsub hs)
  | eq hl hr hsub => exact .eq hl hr (sub_trans hsub hs)
  | ne hl hr hsub => exact .ne hl hr (sub_trans hsub hs)
  | tyof he hsub => exact .tyof he (sub_trans hsub hs)
  | and hl hr hsub => exact .and hl hr (sub_trans hsub hs)
  | or hl hr hsub => exact .or hl hr (sub_trans hsub hs)
  | call hlk hargs hsub => exact .call hlk hargs (sub_trans hsub hs)

/-- A well-typed block stays well-typed with anything appended: it returns
before it gets there. This is what lets `checkBlock` demand that a branch
return and then discharge the `thn ++ rest` obligation of `BlockOk.ite` from
the branch alone, without walking the concatenation. -/
theorem BlockOk_append {p Γ tr b1} (h : BlockOk p Γ tr b1) (b2 : List Stm) :
    BlockOk p Γ tr (b1 ++ b2) := by
  induction h with
  | ret hte => exact .ret hte
  | cst hinit _ ih => exact .cst hinit ih
  | ite hc _ _ iht ihe =>
    refine .ite hc ?_ ?_
    · rw [List.append_assoc] at iht; exact iht
    · rw [List.append_assoc] at ihe; exact ihe

end Core
end Verification
