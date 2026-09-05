import Verification.Calculus.Types

namespace Verification
namespace Core

def never : Ty := { top := false, atoms := [] }
def unknown : Ty := { top := true, atoms := [] }
def ofAtom (a : Atom) : Ty := { top := false, atoms := [a] }

/-- The union of some atoms: `ofAtoms [.str, .num]` is `string | number`.

This is a constructor, not an operation. The calculus has `meet` and `diff`
but deliberately no join (see `narrow`), because narrowing only ever removes
possibilities. Unions therefore only ever enter from outside, decoded from the
`{top, atoms}` JSON, and nothing here needs to build one at runtime -- so this
exists for stating types by hand rather than for computing with. -/
def ofAtoms (as : List Atom) : Ty := { top := false, atoms := as }

theorem mem_ofAtom {v : Val} {a : Atom} (h : inhabits v a = true) : mem v (ofAtom a) := by
  exact Or.inr ⟨a, List.mem_singleton.mpr rfl, h⟩

/-! ### Atom containment -/

/-- `atomSub a b` : every value of `a` is a value of `b`. -/
def atomSub : Atom → Atom → Bool
  | .null, .null => true
  | .undef, .undef => true
  | .num, .num => true
  | .str, .str => true
  | .bool, .bool => true
  | .numLit _, .num => true
  | .strLit _, .str => true
  | .boolLit _, .bool => true
  | .numLit a, .numLit b => a == b
  | .strLit a, .strLit b => a == b
  | .boolLit a, .boolLit b => a == b
  | _, _ => false

theorem atomSub_sound {a b : Atom} (hab : atomSub a b = true) {v : Val}
    (hv : inhabits v a = true) : inhabits v b = true := by
  cases a <;> cases b <;> cases v <;> simp_all [atomSub, inhabits]

/-! ### Subtyping -/

/-- `sub t₁ t₂` : a sound, incomplete test for `⟦t₁⟧ ⊆ ⟦t₂⟧`. -/
def sub (t1 t2 : Ty) : Bool :=
  if t2.top then true
  else if t1.top then false
  else t1.atoms.all (fun a => t2.atoms.any (fun b => atomSub a b))

theorem sub_sound {t1 t2 : Ty} (h : sub t1 t2 = true) {v : Val}
    (hv : mem v t1) : mem v t2 := by
  cases h2 : t2.top with
  | true => exact Or.inl h2
  | false =>
    cases h1 : t1.top with
    | true => simp [sub, h1, h2] at h
    | false =>
      rcases hv with htop | ⟨a, ha, hva⟩
      · simp [h1] at htop
      · simp [sub, h1, h2] at h
        obtain ⟨b, hb, hab⟩ := h a ha
        exact Or.inr ⟨b, hb, atomSub_sound hab hva⟩

theorem atomSub_refl (a : Atom) : atomSub a a = true := by
  cases a <;> simp [atomSub]

theorem atomSub_trans {a b c : Atom} (hab : atomSub a b = true) (hbc : atomSub b c = true) :
    atomSub a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [atomSub]

/-- `sub` is a preorder. Transitivity is what lets subsumption be folded into
each typing rule rather than standing as a rule of its own. -/
theorem sub_refl (t : Ty) : sub t t = true := by
  unfold sub
  split
  · rfl
  · simp only [List.all_eq_true, List.any_eq_true]
    intro a ha
    exact ⟨a, ha, atomSub_refl a⟩

theorem sub_trans {t1 t2 t3 : Ty} (h12 : sub t1 t2 = true) (h23 : sub t2 t3 = true) :
    sub t1 t3 = true := by
  by_cases h3 : t3.top = true
  · simp [sub, h3]
  · simp only [Bool.not_eq_true] at h3
    simp only [sub, h3, Bool.false_eq_true, if_false] at h23 ⊢
    by_cases h2 : t2.top = true
    · simp [h2] at h23
    · simp only [Bool.not_eq_true] at h2
      simp only [h2, Bool.false_eq_true, if_false] at h23
      simp only [sub, h2, Bool.false_eq_true, if_false] at h12
      by_cases h1 : t1.top = true
      · simp [h1] at h12
      · simp only [Bool.not_eq_true] at h1
        simp only [h1, Bool.false_eq_true, if_false] at h12 ⊢
        simp only [List.all_eq_true, List.any_eq_true] at h12 h23 ⊢
        intro a ha
        obtain ⟨b, hb, hab⟩ := h12 a ha
        obtain ⟨c, hc, hbc⟩ := h23 b hb
        exact ⟨c, hc, atomSub_trans hab hbc⟩

/-- Type equality up to denotation, as far as `sub` can see it. -/
def equiv (t1 t2 : Ty) : Bool := sub t1 t2 && sub t2 t1

/-! ### Meet -/

/-- The atoms of `a ⊓ b`. Sound because whenever a value inhabits both `a` and
`b`, one of the two atoms is contained in the other. -/
def atomMeet (a b : Atom) : List Atom :=
  if atomSub a b then [a] else if atomSub b a then [b] else []

theorem atomMeet_sound {a b : Atom} {v : Val}
    (ha : inhabits v a = true) (hb : inhabits v b = true) :
    ∃ c ∈ atomMeet a b, inhabits v c = true := by
  by_cases hab : atomSub a b = true
  · exact ⟨a, by simp [atomMeet, hab], ha⟩
  · by_cases hba : atomSub b a = true
    · exact ⟨b, by simp [atomMeet, hab, hba], hb⟩
    · exfalso
      cases a <;> cases b <;> cases v <;> simp_all [atomSub, inhabits]

/-- `meet t₁ t₂` contains `⟦t₁⟧ ∩ ⟦t₂⟧`. -/
def meet (t1 t2 : Ty) : Ty :=
  if t1.top then t2
  else if t2.top then t1
  else { top := false,
         atoms := t1.atoms.flatMap (fun a => t2.atoms.flatMap (fun b => atomMeet a b)) }

theorem meet_sound {t1 t2 : Ty} {v : Val} (h1 : mem v t1) (h2 : mem v t2) :
    mem v (meet t1 t2) := by
  cases ht1 : t1.top with
  | true => simpa [meet, ht1] using h2
  | false =>
    cases ht2 : t2.top with
    | true => simpa [meet, ht1, ht2] using h1
    | false =>
      rcases h1 with htop | ⟨a, ha, hva⟩
      · simp [ht1] at htop
      rcases h2 with htop | ⟨b, hb, hvb⟩
      · simp [ht2] at htop
      obtain ⟨c, hc, hvc⟩ := atomMeet_sound hva hvb
      have hatoms : (meet t1 t2).atoms
          = t1.atoms.flatMap (fun a => t2.atoms.flatMap (fun b => atomMeet a b)) := by
        simp [meet, ht1, ht2]
      refine Or.inr ⟨c, ?_, hvc⟩
      rw [hatoms]
      simp only [List.mem_flatMap]
      exact ⟨a, ha, b, hb, hc⟩

/-! ### Difference -/

/-- Whether every value of the atom `a` lies in `t`. -/
def atomCovered (a : Atom) (t : Ty) : Bool :=
  t.top || t.atoms.any (fun b => atomSub a b)

/-- `diff t₁ t₂` contains `⟦t₁⟧ \ ⟦t₂⟧`. It drops exactly the atoms of `t₁`
that `t₂` covers entirely, so an atom only partly removed by `t₂` survives
whole. -/
def diff (t1 t2 : Ty) : Ty :=
  if t1.top then t1
  else { top := false, atoms := t1.atoms.filter (fun a => !atomCovered a t2) }

theorem diff_sound {t1 t2 : Ty} {v : Val} (h1 : mem v t1) (h2 : ¬ mem v t2) :
    mem v (diff t1 t2) := by
  cases ht1 : t1.top with
  | true => simpa [diff, ht1] using h1
  | false =>
    rcases h1 with htop | ⟨a, ha, hva⟩
    · simp [ht1] at htop
    have hcov : atomCovered a t2 = false := by
      cases hc : atomCovered a t2 with
      | false => rfl
      | true =>
        exfalso
        simp only [atomCovered, Bool.or_eq_true, List.any_eq_true] at hc
        rcases hc with htop2 | ⟨b, hb, hab⟩
        · exact h2 (Or.inl htop2)
        · exact h2 (Or.inr ⟨b, hb, atomSub_sound hab hva⟩)
    have hatoms : (diff t1 t2).atoms = t1.atoms.filter (fun a => !atomCovered a t2) := by
      simp [diff, ht1]
    refine Or.inr ⟨a, ?_, hva⟩
    rw [hatoms]
    exact List.mem_filter.mpr ⟨ha, by simp [hcov]⟩

/-- The atom denoting exactly `v`, and nothing else. Every literal has one,
so no literal's type is ever an over-approximation. -/
def atomOfVal : Val → Atom
  | .vnull => .null
  | .vundef => .undef
  | .vnum b => .numLit b
  | .vstr s => .strLit s
  | .vbool b => .boolLit b

def bool_ : Ty := ofAtom .bool
def string_ : Ty := ofAtom .str

/-! ## Small facts about the denotation -/

theorem mem_ofAtom_iff {v : Val} {a : Atom} : mem v (ofAtom a) ↔ inhabits v a = true := by
  constructor
  · rintro (h | ⟨b, hb, hvb⟩)
    · simp [ofAtom] at h
    · simp [ofAtom] at hb; subst hb; exact hvb
  · intro h; exact Or.inr ⟨a, by simp [ofAtom], h⟩

theorem not_mem_never {v : Val} : ¬ mem v never := by
  rintro (h | ⟨a, ha, _⟩) <;> simp [never] at *

theorem mem_bool {b : Bool} : mem (.vbool b) bool_ :=
  mem_ofAtom_iff.mpr (by simp [inhabits])

theorem mem_bool_inv {v : Val} (h : mem v bool_) : ∃ b, v = .vbool b := by
  have := mem_ofAtom_iff.mp h
  cases v <;> simp [inhabits] at this
  exact ⟨_, rfl⟩

theorem inhabits_atomOfVal (v : Val) : inhabits v (atomOfVal v) = true := by
  cases v <;> simp [atomOfVal, inhabits]

theorem mem_atomOfVal (v : Val) : mem v (ofAtom (atomOfVal v)) :=
  mem_ofAtom_iff.mpr (inhabits_atomOfVal v)

theorem atomOfVal_exact {u w : Val} (h : inhabits u (atomOfVal w) = true) : u = w := by
  cases u <;> cases w <;> simp_all [atomOfVal, inhabits]

end Core
end Verification
