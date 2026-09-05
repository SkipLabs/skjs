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

/-! ## Graph typing

Every checked node has an established entry environment, recorded in `I`.
An edge carries the environment its source derived and must justify the
environment its target was given -- which is what makes a join checkable
without a least upper bound on types: both predecessors of a merge
independently imply the merge's environment.

`Covers` is semantic implication between environments, so forgetting a fact
is sound and inventing a required binding is not. -/

def Covers (G H : TEnv) : Prop := ∀ ρ, agree ρ G → agree ρ H

/-- The way `Covers` is established in practice: every binding the target
requires is supplied by the source at a type it contains. `tenvGet` takes the
first match, so this respects shadowing on both sides. -/
theorem Covers_of_sub {G H : TEnv}
    (h : ∀ x t, tenvGet H x = some t → ∃ s, tenvGet G x = some s ∧ sub s t = true) :
    Covers G H := by
  intro ρ hG x t ht
  obtain ⟨s, hs, hsub⟩ := h x t ht
  obtain ⟨v, hv, hm⟩ := hG x s hs
  exact ⟨v, hv, sub_sound hsub hm⟩

/-- An edge from a state described by `G`. `none` is control leaving the graph
without returning, which no edge can justify: that is where "a function may
not fall off the end" now lives, stated once rather than once per branch. -/
def Edge (f : Fn) (I : List TEnv) (G : TEnv) : Option Nat → Prop
  | none => False
  | some pc => ∃ H, I[pc]? = some H ∧ Covers G H

inductive NodeOk (p : Prog) (f : Fn) (I : List TEnv) (G : TEnv) : Node → Prop where
  | ret : HasTy p G e f.ret → NodeOk p f I G (.ret e)
  | set : HasTy p G e t → Edge f I (tenvSet G x t) next →
      NodeOk p f I G (.set x e next)
  | branch : HasTy p G c bool_ →
      Edge f I (narrow G c true) yes → Edge f I (narrow G c false) no →
      NodeOk p f I G (.branch c yes no)

/-- `I` establishes an entry environment for every node it covers, the
function's entry edge is justified from the parameters, and every covered
node checks against its environment. -/
structure FnOk (p : Prog) (f : Fn) (I : List TEnv) : Prop where
  entry : Edge f I f.params (some 0)
  present : ∀ (pc : Nat) G, I[pc]? = some G → ∃ node, f.code[pc]? = some node
  nodes : ∀ (pc : Nat) G node, I[pc]? = some G → f.code[pc]? = some node →
    NodeOk p f I G node

/-- Every function of the program checks against its own declared signature,
under some environment assignment. A call is therefore never given a rule of
its own: `ProgOk` is the hypothesis `sound` discharges for the whole program
at once. -/
def ProgOk (p : Prog) : Prop := ∀ f ∈ p, ∃ I, FnOk p f I

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
  ∧ (∀ f I pc G ρ, FnOk p f I → I[pc]? = some G → agree ρ G →
        run p n f pc ρ ≠ .stuck ∧ ∀ v, run p n f pc ρ = .ok v → mem v f.ret) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro ρ Γ a b _ _; simp [evalE]
    · intro ρ Γ a b _ _; simp [evalArgs]
    · intro f I pc G ρ _ _ _; simp [run]
  | succ n ih =>
    obtain ⟨ihE, ihA, ihR⟩ := ih
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
            obtain ⟨I, hI⟩ := hp fn hfn
            obtain ⟨H, hH, hcov⟩ := hI.entry
            obtain ⟨hnsB, hpB⟩ := ihR fn I 0 H (bindParams fn.params vs) hI hH
              (hcov _ (agree_bindParams hma))
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
    -- graph nodes
    · intro f I pc G ρ hI hpc hG
      obtain ⟨node, hnode⟩ := hI.present pc G hpc
      have hok : NodeOk p f I G node := hI.nodes pc G node hpc hnode
      cases hok with
      | ret hte =>
        rename_i e
        simp only [run, hnode]
        exact ihE ρ G e f.ret hG hte
      | set hinit hedge =>
        rename_i e t x next
        obtain ⟨hns1, hp1⟩ := ihE ρ G e t hG hinit
        cases hev : evalE p n ρ e with
        | ok v =>
          cases next with
          | none => exact absurd hedge (by simp [Edge])
          | some k =>
            obtain ⟨H, hH, hcov⟩ := hedge
            obtain ⟨hns2, hp2⟩ := ihR f I k H (venvSet ρ x v) hI hH
              (hcov _ (agree_cons hG (hp1 v hev)))
            simp only [run, hnode, hev]
            exact ⟨hns2, hp2⟩
        | stuck => exact absurd hev hns1
        | timeout => simp [run, hnode, hev]
      | branch hc hyes hno =>
        rename_i c yes no
        obtain ⟨hns1, hp1⟩ := ihE ρ G c bool_ hG hc
        cases hev : evalE p n ρ c with
        | ok v =>
          obtain ⟨bb, rfl⟩ := mem_bool_inv (hp1 v hev)
          cases bb
          · cases no with
            | none => exact absurd hno (by simp [Edge])
            | some k =>
              obtain ⟨H, hH, hcov⟩ := hno
              obtain ⟨hns2, hp2⟩ := ihR f I k H ρ hI hH
                (hcov _ (narrow_sound p n ρ G c false hG hev))
              simp only [run, hnode, hev]
              exact ⟨hns2, hp2⟩
          · cases yes with
            | none => exact absurd hyes (by simp [Edge])
            | some k =>
              obtain ⟨H, hH, hcov⟩ := hyes
              obtain ⟨hns2, hp2⟩ := ihR f I k H ρ hI hH
                (hcov _ (narrow_sound p n ρ G c true hG hev))
              simp only [run, hnode, hev]
              exact ⟨hns2, hp2⟩
        | stuck => exact absurd hev hns1
        | timeout => simp [run, hnode, hev]

/-! ## What the theorem says

Calling a function of a well-typed program with arguments that inhabit its
parameter types cannot go wrong, and if it produces a value at all then that
value inhabits the declared return type. -/

private theorem entry_agrees {p : Prog} (hp : ProgOk p) {fn : Fn} (hfn : fn ∈ p)
    {vs : List Val} (hma : MemAll vs fn.params) :
    ∃ I H, FnOk p fn I ∧ I[0]? = some H ∧ agree (bindParams fn.params vs) H := by
  obtain ⟨I, hI⟩ := hp fn hfn
  obtain ⟨H, hH, hcov⟩ := hI.entry
  exact ⟨I, H, hI, hH, hcov _ (agree_bindParams hma)⟩

theorem call_never_stuck {p : Prog} (hp : ProgOk p) {fn : Fn} (hfn : fn ∈ p)
    {vs : List Val} (hma : MemAll vs fn.params) (n : Nat) :
    run p n fn 0 (bindParams fn.params vs) ≠ .stuck := by
  obtain ⟨I, H, hI, hH, hag⟩ := entry_agrees hp hfn hma
  exact ((sound hp n).2.2 fn I 0 H _ hI hH hag).1

theorem call_returns_in_type {p : Prog} (hp : ProgOk p) {fn : Fn} (hfn : fn ∈ p)
    {vs : List Val} (hma : MemAll vs fn.params) (n : Nat) {v : Val}
    (h : run p n fn 0 (bindParams fn.params vs) = .ok v) : mem v fn.ret := by
  obtain ⟨I, H, hI, hH, hag⟩ := entry_agrees hp hfn hma
  exact ((sound hp n).2.2 fn I 0 H _ hI hH hag).2 v h

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

end Core
end Verification
