import Verification.Calculus.TypeOperations
import Verification.Calculus.Programs

namespace Verification
namespace Core

abbrev TEnv := List (String × Ty)

def tenvGet : TEnv → String → Option Ty
  | [], _ => none
  | (y, t) :: rest, x => if y == x then some t else tenvGet rest x

def tenvSet (Γ : TEnv) (x : String) (t : Ty) : TEnv := (x, t) :: Γ

/-! ## `typeof` as a type

`tagTyOf k` is the type of the values whose tag is `k`, and `mem_tagTyOf`
says so in both directions. Both matter: the forward one justifies `meet` on
the edge where a `typeof` test holds, the backward one justifies `diff` on the
edge where it fails. -/

def tagTyOf (k : String) : Ty :=
  match k with
  | "number" => ofAtom .num
  | "string" => ofAtom .str
  | "boolean" => ofAtom .bool
  | "undefined" => ofAtom .undef
  | "object" => ofAtom .null
  | _ => never

theorem mem_tagTyOf {v : Val} {k : String} : mem v (tagTyOf k) ↔ typeofVal v = k := by
  unfold tagTyOf
  split <;> subst_vars <;> cases v <;>
    simp_all [mem_ofAtom_iff, inhabits, typeofVal, not_mem_never]
  all_goals (intro h; subst h; simp_all)

/-! ## The tag of a type

`tagsOf t` is the set of strings `typeof` can yield for a value of `t`. It is
what gives `typeof e` a type sharper than `string`: for `string | number` it
is `"string" | "number"`, not every string. -/

def tagOfAtom : Atom → Atom
  | .null => .strLit "object"
  | .undef => .strLit "undefined"
  | .num | .numLit _ => .strLit "number"
  | .str | .strLit _ => .strLit "string"
  | .bool | .boolLit _ => .strLit "boolean"

/-- The five tags any value can carry. -/
def allTags : Ty :=
  { top := false
    atoms := [.strLit "undefined", .strLit "object", .strLit "number",
              .strLit "string", .strLit "boolean"] }

def tagsOf (t : Ty) : Ty :=
  if t.top then allTags else { top := false, atoms := t.atoms.map tagOfAtom }

theorem mem_allTags (v : Val) : mem (.vstr (typeofVal v)) allTags := by
  cases v <;> exact Or.inr (by simp [allTags, typeofVal, inhabits])

theorem mem_tagsOf {v : Val} {t : Ty} (h : mem v t) :
    mem (.vstr (typeofVal v)) (tagsOf t) := by
  unfold tagsOf
  split
  · exact mem_allTags v
  · next htop =>
    rcases h with h | ⟨a, ha, hva⟩
    · simp_all
    · refine Or.inr ⟨tagOfAtom a, List.mem_map_of_mem ha, ?_⟩
      cases a <;> cases v <;> simp_all [inhabits, typeofVal, tagOfAtom]

/-! ## Truthiness as a type -/

def atomTruthy : Atom → Option Atom
  | .null | .undef => none
  | .num => some .num
  | .str => some .str
  | .bool => some (.boolLit true)
  | .numLit b => if b == zeroBits then none else some (.numLit b)
  | .strLit s => if s == "" then none else some (.strLit s)
  | .boolLit b => if b then some (.boolLit b) else none

def atomFalsy : Atom → Option Atom
  | .null => some .null
  | .undef => some .undef
  | .num => some .num
  | .str => some (.strLit "")
  | .bool => some (.boolLit false)
  | .numLit b => if b == zeroBits then some (.numLit b) else none
  | .strLit s => if s == "" then some (.strLit s) else none
  | .boolLit b => if b then none else some (.boolLit b)

def truthyPart (t : Ty) : Ty :=
  if t.top then t else { top := false, atoms := t.atoms.filterMap atomTruthy }

def falsyPart (t : Ty) : Ty :=
  if t.top then t else { top := false, atoms := t.atoms.filterMap atomFalsy }

theorem atomTruthy_sound {v : Val} {a : Atom} (hv : inhabits v a = true) (ht : truthy v = true) :
    ∃ c, atomTruthy a = some c ∧ inhabits v c = true := by
  cases a <;> cases v <;> simp_all [inhabits, truthy, atomTruthy]

theorem atomFalsy_sound {v : Val} {a : Atom} (hv : inhabits v a = true) (ht : truthy v = false) :
    ∃ c, atomFalsy a = some c ∧ inhabits v c = true := by
  cases a <;> cases v <;> simp_all [inhabits, truthy, atomFalsy]

theorem mem_truthyPart {v : Val} {t : Ty} (h : mem v t) (ht : truthy v = true) :
    mem v (truthyPart t) := by
  unfold truthyPart
  split
  · exact h
  · next htop =>
    rcases h with h | ⟨a, ha, hva⟩
    · simp_all
    · obtain ⟨c, hc, hvc⟩ := atomTruthy_sound hva ht
      exact Or.inr ⟨c, List.mem_filterMap.mpr ⟨a, ha, hc⟩, hvc⟩

theorem mem_falsyPart {v : Val} {t : Ty} (h : mem v t) (ht : truthy v = false) :
    mem v (falsyPart t) := by
  unfold falsyPart
  split
  · exact h
  · next htop =>
    rcases h with h | ⟨a, ha, hva⟩
    · simp_all
    · obtain ⟨c, hc, hvc⟩ := atomFalsy_sound hva ht
      exact Or.inr ⟨c, List.mem_filterMap.mpr ⟨a, ha, hc⟩, hvc⟩

/-! ## Agreement

`agree ρ Γ` is the invariant the whole proof turns on: every type the
environment records really does contain the value the variable holds. -/

def agree (ρ : VEnv) (Γ : TEnv) : Prop :=
  ∀ x t, tenvGet Γ x = some t → ∃ v, venvGet ρ x = some v ∧ mem v t

theorem agree_set {ρ Γ x u t} (h : agree ρ Γ) (hu : venvGet ρ x = some u) (hm : mem u t) :
    agree ρ (tenvSet Γ x t) := by
  intro y ty hy
  by_cases hxy : x = y
  · subst hxy
    simp [tenvSet, tenvGet] at hy
    subst hy
    exact ⟨u, hu, hm⟩
  · have hne : (x == y) = false := by simp [hxy]
    simp [tenvSet, tenvGet, hne] at hy
    exact h y ty hy

def narrowWith (Γ : TEnv) (x : String) (f : Ty → Ty) : TEnv :=
  match tenvGet Γ x with
  | some t => tenvSet Γ x (f t)
  | none => Γ

theorem agree_narrowWith {ρ Γ x u f} (h : agree ρ Γ) (hu : venvGet ρ x = some u)
    (hf : ∀ t, mem u t → mem u (f t)) : agree ρ (narrowWith Γ x f) := by
  unfold narrowWith
  split
  · next t ht =>
    obtain ⟨v, hv, hm⟩ := h x t ht
    rw [hu] at hv
    cases hv
    exact agree_set h hu (hf t hm)
  · exact h

/-! ## Narrowing

`narrow Γ e b` is the environment that holds on the edge where `e` evaluates
to `b`. Returning `Γ` unchanged is always sound, so an incomplete rule set
costs precision, never soundness. -/

def narrowEq (Γ : TEnv) (l r : Exp) (target : Bool) : TEnv :=
  match l, r with
  | .tyof (.var x), .lit (.vstr k) =>
      narrowWith Γ x (fun t => if target then meet t (tagTyOf k) else diff t (tagTyOf k))
  | .lit (.vstr k), .tyof (.var x) =>
      narrowWith Γ x (fun t => if target then meet t (tagTyOf k) else diff t (tagTyOf k))
  | .var x, .lit w =>
      narrowWith Γ x
        (fun t => if target then meet t (ofAtom (atomOfVal w)) else diff t (ofAtom (atomOfVal w)))
  | .lit w, .var x =>
      narrowWith Γ x
        (fun t => if target then meet t (ofAtom (atomOfVal w)) else diff t (ofAtom (atomOfVal w)))
  | .var x, .var y =>
      if target then
        match tenvGet Γ x, tenvGet Γ y with
        | some tx, some ty => tenvSet (tenvSet Γ x (meet tx ty)) y (meet tx ty)
        | _, _ => Γ
      else Γ
  | _, _ => Γ

def narrow (Γ : TEnv) (e : Exp) (target : Bool) : TEnv :=
  match e with
  | .not inner => narrow Γ inner (!target)
  | .eq l r => narrowEq Γ l r target
  | .ne l r => narrowEq Γ l r (!target)
  -- Only one edge of each connective is informative; the other is a join,
  -- and the lattice has no joins.
  | .and l r => if target then narrow (narrow Γ l true) r true else Γ
  | .or l r => if target then Γ else narrow (narrow Γ l false) r false
  | .var x => narrowWith Γ x (fun t => if target then truthyPart t else falsyPart t)
  | _ => Γ

/-! ## Inverting the evaluator -/

theorem evalE_var_inv {p n ρ x u} (h : evalE p n ρ (.var x) = .ok u) :
    venvGet ρ x = some u := by
  cases n with
  | zero => simp [evalE] at h
  | succ n =>
    simp only [evalE] at h
    split at h
    · next v hv => cases h; exact hv
    · simp at h

theorem evalE_lit_inv {p n ρ} {w u : Val} (h : evalE p n ρ (.lit w) = .ok u) : u = w := by
  cases n with
  | zero => simp [evalE] at h
  | succ n => simp only [evalE] at h; cases h; rfl

theorem evalE_tyof_inv {p n ρ e u} (h : evalE p n ρ (.tyof e) = .ok u) :
    ∃ m w, n = m + 1 ∧ evalE p m ρ e = .ok w ∧ u = .vstr (typeofVal w) := by
  cases n with
  | zero => simp [evalE] at h
  | succ m =>
    simp only [evalE] at h
    split at h
    · next w hw => cases h; exact ⟨m, w, rfl, hw, rfl⟩
    · simp at h
    · simp at h

theorem evalE_eq_inv {p n ρ l r u} (h : evalE p n ρ (.eq l r) = .ok u) :
    ∃ m a b, n = m + 1 ∧ evalE p m ρ l = .ok a ∧ evalE p m ρ r = .ok b ∧ u = .vbool (a == b) := by
  cases n with
  | zero => simp [evalE] at h
  | succ m =>
    simp only [evalE] at h
    split at h
    · next a ha =>
      split at h
      · next b hb => cases h; exact ⟨m, a, b, rfl, ha, hb, rfl⟩
      · simp at h
      · simp at h
    · simp at h
    · simp at h

theorem evalE_ne_inv {p n ρ l r u} (h : evalE p n ρ (.ne l r) = .ok u) :
    ∃ m a b, n = m + 1 ∧ evalE p m ρ l = .ok a ∧ evalE p m ρ r = .ok b ∧
      u = .vbool (!(a == b)) := by
  cases n with
  | zero => simp [evalE] at h
  | succ m =>
    simp only [evalE] at h
    split at h
    · next a ha =>
      split at h
      · next b hb => cases h; exact ⟨m, a, b, rfl, ha, hb, rfl⟩
      · simp at h
      · simp at h
    · simp at h
    · simp at h

/-! ## Narrowing is sound

The one place where the runtime facts about `===`, `typeof` and truthiness
have to be cashed in. Each case pairs an evaluation outcome with the lattice
lemma that justifies the type it licenses: `meet_sound` on an edge that
confirms a value, `diff_sound` on an edge that excludes one. -/

theorem narrowEq_sound {p n ρ Γ l r} {u w : Val} {target : Bool}
    (hG : agree ρ Γ)
    (hl : evalE p n ρ l = .ok u) (hr : evalE p n ρ r = .ok w)
    (heq : (u == w) = target) :
    agree ρ (narrowEq Γ l r target) := by
  unfold narrowEq
  split
  -- `typeof x === k`
  case h_1 =>
    rename_i x k
    obtain ⟨m, z, rfl, hz, rfl⟩ := evalE_tyof_inv hl
    have hzx : venvGet ρ x = some z := evalE_var_inv hz
    have hwk : w = .vstr k := evalE_lit_inv hr
    subst hwk
    cases target
    · refine agree_narrowWith hG hzx ?_
      intro t ht
      show mem z (diff t (tagTyOf k))
      refine diff_sound ht ?_
      intro hmem
      have hk : typeofVal z = k := mem_tagTyOf.mp hmem
      simp [hk] at heq
    · refine agree_narrowWith hG hzx ?_
      intro t ht
      show mem z (meet t (tagTyOf k))
      refine meet_sound ht (mem_tagTyOf.mpr ?_)
      simpa using heq
  -- `k === typeof x`
  case h_2 =>
    rename_i k x
    obtain ⟨m, z, rfl, hz, rfl⟩ := evalE_tyof_inv hr
    have hzx : venvGet ρ x = some z := evalE_var_inv hz
    have huk : u = .vstr k := evalE_lit_inv hl
    subst huk
    cases target
    · refine agree_narrowWith hG hzx ?_
      intro t ht
      show mem z (diff t (tagTyOf k))
      refine diff_sound ht ?_
      intro hmem
      have hk : typeofVal z = k := mem_tagTyOf.mp hmem
      simp [hk] at heq
    · refine agree_narrowWith hG hzx ?_
      intro t ht
      show mem z (meet t (tagTyOf k))
      refine meet_sound ht (mem_tagTyOf.mpr ?_)
      have := heq
      simp at this
      exact this.symm
  -- `x === c`
  case h_3 =>
    rename_i x c
    have hux : venvGet ρ x = some u := evalE_var_inv hl
    have hwc : w = c := evalE_lit_inv hr
    subst hwc
    cases target
    · refine agree_narrowWith hG hux ?_
      intro t ht
      show mem u (diff t (ofAtom (atomOfVal w)))
      refine diff_sound ht ?_
      intro hmem
      have : u = w := atomOfVal_exact (mem_ofAtom_iff.mp hmem)
      simp [this] at heq
    · refine agree_narrowWith hG hux ?_
      intro t ht
      show mem u (meet t (ofAtom (atomOfVal w)))
      have huw : u = w := by simpa using heq
      subst huw
      exact meet_sound ht (mem_atomOfVal u)
  -- `c === x`
  case h_4 =>
    rename_i c x
    have hwx : venvGet ρ x = some w := evalE_var_inv hr
    have huc : u = c := evalE_lit_inv hl
    subst huc
    cases target
    · refine agree_narrowWith hG hwx ?_
      intro t ht
      show mem w (diff t (ofAtom (atomOfVal u)))
      refine diff_sound ht ?_
      intro hmem
      have : w = u := atomOfVal_exact (mem_ofAtom_iff.mp hmem)
      simp [this] at heq
    · refine agree_narrowWith hG hwx ?_
      intro t ht
      show mem w (meet t (ofAtom (atomOfVal u)))
      have huw : u = w := by simpa using heq
      subst huw
      exact meet_sound ht (mem_atomOfVal u)
  -- `x === y`
  case h_5 =>
    rename_i x y
    have hux : venvGet ρ x = some u := evalE_var_inv hl
    have hwy : venvGet ρ y = some w := evalE_var_inv hr
    cases target
    · show agree ρ Γ
      exact hG
    · have huw : u = w := by simpa using heq
      subst huw
      show agree ρ (match tenvGet Γ x, tenvGet Γ y with
        | some tx, some ty => tenvSet (tenvSet Γ x (meet tx ty)) y (meet tx ty)
        | _, _ => Γ)
      split
      · rename_i tx ty htx hty
        obtain ⟨v1, hv1, hm1⟩ := hG x tx htx
        obtain ⟨v2, hv2, hm2⟩ := hG y ty hty
        rw [hux] at hv1; cases hv1
        rw [hwy] at hv2; cases hv2
        have hm : mem u (meet tx ty) := meet_sound hm1 hm2
        exact agree_set (agree_set hG hux hm) hwy hm
      · exact hG
  case h_6 => exact hG

theorem narrow_sound (p : Prog) :
    ∀ (n : Nat) (ρ : VEnv) (Γ : TEnv) (e : Exp) (b : Bool),
      agree ρ Γ → evalE p n ρ e = .ok (.vbool b) → agree ρ (narrow Γ e b) := by
  intro n
  induction n with
  | zero => intro ρ Γ e b _ h; simp [evalE] at h
  | succ n ih =>
    intro ρ Γ e b hG h
    cases e with
    | var x =>
      have hux : venvGet ρ x = some (.vbool b) := evalE_var_inv h
      refine agree_narrowWith hG hux ?_
      intro t ht
      cases b
      · show mem (Val.vbool false) (falsyPart t)
        exact mem_falsyPart ht rfl
      · show mem (Val.vbool true) (truthyPart t)
        exact mem_truthyPart ht rfl
    | lit v => exact hG
    | not inner =>
      show agree ρ (narrow Γ inner (!b))
      simp only [evalE] at h
      split at h
      · rename_i b' hb'
        have : (!b') = b := by simpa using h
        subst this
        simpa using ih ρ Γ inner b' hG hb'
      · simp at h
      · simp at h
      · simp at h
    | eq l r =>
      obtain ⟨m, a, c, hmn, ha, hc, hu⟩ := evalE_eq_inv h
      have hb : b = (a == c) := by simpa using hu
      exact narrowEq_sound hG ha hc hb.symm
    | ne l r =>
      obtain ⟨m, a, c, hmn, ha, hc, hu⟩ := evalE_ne_inv h
      have hb : b = (!(a == c)) := by simpa using hu
      have hac : (a == c) = (!b) := by rw [hb]; simp
      exact narrowEq_sound hG ha hc hac
    | tyof e => exact hG
    | and l r =>
      cases b
      · show agree ρ Γ
        exact hG
      · show agree ρ (narrow (narrow Γ l true) r true)
        simp only [evalE] at h
        split at h
        · simp at h
        · rename_i hlt
          split at h
          · rename_i b2 hb2
            have hb : b2 = true := by simpa using h
            subst hb
            exact ih ρ (narrow Γ l true) r true (ih ρ Γ l true hG hlt) hb2
          · simp at h
          · simp at h
          · simp at h
        · simp at h
        · simp at h
        · simp at h
    | or l r =>
      cases b
      · show agree ρ (narrow (narrow Γ l false) r false)
        simp only [evalE] at h
        split at h
        · simp at h
        · rename_i hlf
          split at h
          · rename_i b2 hb2
            have hb : b2 = false := by simpa using h
            subst hb
            exact ih ρ (narrow Γ l false) r false (ih ρ Γ l false hG hlf) hb2
          · simp at h
          · simp at h
          · simp at h
        · simp at h
        · simp at h
        · simp at h
      · show agree ρ Γ
        exact hG
    | call f args => exact hG

end Core
end Verification
