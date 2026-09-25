import Verification.Model.Semantics.Calculus

/-!
# Binding discipline

`Scoped d t` says that the free de Bruijn indices of `t` are below `d`.
Unlike `isVal`, it rules out callable code containing free variables. Substitution
in the machine is valid for closed arguments; the lemmas here state that
precondition explicitly.
-/
namespace Verification.Model

mutual
def Scoped (d : Nat) : Tm → Prop
  | .var i => i < d
  | .objAt _ .absent => True
  | .objAt _ (.closure n b _) => Scoped (d + n + 1) b
  | .makeAt (.closure n b _) _ args => Scoped (d + n + 1) b ∧ ScopedArgs d args
  | .objAt _ (.variadic n b) => Scoped (d + n + 2) b
  | .makeAt (.variadic n b) _ args => Scoped (d + n + 2) b ∧ ScopedArgs d args
  | .objAt _ (.bound t r pre) => Scoped d t ∧ Scoped d r ∧ ScopedArgs d pre
  | .makeAt (.bound t r pre) _ args =>
      Scoped d t ∧ Scoped d r ∧ ScopedArgs d pre ∧ ScopedArgs d args
  | .makeAt .absent _ args => ScopedArgs d args
  | .letE a b => Scoped d a ∧ Scoped (d + 1) b
  | .invoke f r args => Scoped d f ∧ Scoped d r ∧ ScopedArgs d args
  | .construct f args => Scoped d f ∧ ScopedArgs d args
  | .readAt _ a | .test _ a => Scoped d a
  | .writeAt _ a b | .arith _ a b | .elemAt a b | .indexAt a b =>
      Scoped d a ∧ Scoped d b
  | .ite c a b | .setElem c a b => Scoped d c ∧ Scoped d a ∧ Scoped d b
  | .arrLit args => ScopedArgs d args
  | .lenOf a => Scoped d a
  | .spread a => Scoped d a
  | .throw a => Scoped d a
  | .merge _ a b => Scoped d a ∧ Scoped d b
  -- Graph code's node expressions are scoped by its own environment, which
  -- invocation supplies whole; only the captures are scoped here.
  | .objAt _ (.graph _ _ _ _ caps) => ScopedArgs d caps
  | .makeAt (.graph _ _ _ _ caps) _ args => ScopedArgs d caps ∧ ScopedArgs d args
  | .goto _ _ _ L x => ScopedArgs d L ∧ Scoped d x
  | .frame _ _ t L x _ _ => Scoped d t ∧ ScopedArgs d L ∧ Scoped d x
  | _ => True

def ScopedArgs (d : Nat) : List Tm → Prop
  | [] => True
  | a :: args => Scoped d a ∧ ScopedArgs d args
end

@[simp] theorem scopedArgs_iff (d : Nat) (args : List Tm) :
    ScopedArgs d args ↔ ∀ a ∈ args, Scoped d a := by
  induction args <;> simp_all [ScopedArgs]

@[simp] theorem scoped_app (d : Nat) (f a : Tm) :
    Scoped d (.app f a) ↔ Scoped d f ∧ Scoped d a := by simp [Scoped]

theorem Scoped.mono {t : Tm} {d e : Nat} (h : Scoped d t) (hde : d ≤ e) :
    Scoped e t := by
  induction t using Tm.induct generalizing d e <;> simp only [Scoped, scopedArgs_iff] at *
  case var i => omega
  case objClosure l n b k ih => exact ih h (by omega)
  case invoke f r args ihf ihr iha =>
    exact ⟨ihf h.1 hde, ihr h.2.1 hde, fun a ha => iha a ha (h.2.2 a ha) hde⟩
  case construct f args ihf iha =>
    exact ⟨ihf h.1 hde, fun a ha => iha a ha (h.2 a ha) hde⟩
  case letE a b iha ihb => exact ⟨iha h.1 hde, ihb h.2 (by omega)⟩
  case attach n f k ns args ihf ihargs =>
    exact ⟨ihf h.1 (by omega), fun a ha => ihargs a ha (h.2 a ha) hde⟩
  case objVariadic l n b ih => exact ih h (by omega)
  case makeVariadic n f ns args ihf ihargs =>
    exact ⟨ihf h.1 (by omega), fun a ha => ihargs a ha (h.2 a ha) hde⟩
  case objBound fs t r pre iht ihr ihp =>
    exact ⟨iht h.1 hde, ihr h.2.1 hde, fun a ha => ihp a ha (h.2.2 a ha) hde⟩
  case makeBound t r pre ns args iht ihr ihp ihargs =>
    exact ⟨iht h.1 hde, ihr h.2.1 hde, fun a ha => ihp a ha (h.2.2.1 a ha) hde,
      fun a ha => ihargs a ha (h.2.2.2 a ha) hde⟩
  case write f a b iha ihb => exact ⟨iha h.1 hde, ihb h.2 hde⟩
  case arith op a b iha ihb => exact ⟨iha h.1 hde, ihb h.2 hde⟩
  case ite c a b ihc iha ihb => exact ⟨ihc h.1 hde, iha h.2.1 hde, ihb h.2.2 hde⟩
  case alloc ns args ihargs => exact fun a ha => ihargs a ha (h a ha) hde
  case arrLit args ihargs => exact fun a ha => ihargs a ha (h a ha) hde
  case elemAt a b iha ihb => exact ⟨iha h.1 hde, ihb h.2 hde⟩
  case index a b iha ihb => exact ⟨iha h.1 hde, ihb h.2 hde⟩
  case setElem a b c iha ihb ihc => exact ⟨iha h.1 hde, ihb h.2.1 hde, ihc h.2.2 hde⟩
  case lenOf a ih => exact ih h hde
  case spread a ih => exact ih h hde
  case throw a ih => exact ih h hde
  case merge dr a b iha ihb => exact ⟨iha h.1 hde, ihb h.2 hde⟩
  case read f a ih => exact ih h hde
  case test k a ih => exact ih h hde
  case objGraph fs n E K st caps _ ihc => exact fun a ha => ihc a ha (h a ha) hde
  case makeGraph n E K st caps ns args _ ihc iha =>
    exact ⟨fun a ha => ihc a ha (h.1 a ha) hde, fun a ha => iha a ha (h.2 a ha) hde⟩
  case goto E K l L x _ ihL ihx => exact ⟨fun a ha => ihL a ha (h.1 a ha) hde, ihx h.2 hde⟩
  case frame E K t L x k hd _ iht ihL ihx =>
    exact ⟨iht h.1 hde, fun a ha => ihL a ha (h.2.1 a ha) hde, ihx h.2.2 hde⟩
  all_goals trivial

theorem subst_above {t : Tm} {d j : Nat} (h : Scoped d t) (hj : d ≤ j) (a : Tm) :
    subst j a t = t := by
  induction t using Tm.induct generalizing d j <;> simp only [Scoped, scopedArgs_iff, subst, substArgs_eq_map] at *
  case var i => simp [show i ≠ j by omega, show ¬j < i by omega]
  case objClosure l n b k ih => rw [ih h (by omega)]
  case invoke f r args ihf ihr iha =>
    rw [ihf h.1 hj, ihr h.2.1 hj]
    congr 1
    simpa using (List.map_congr_left (g := id) (fun a ha => iha a ha (h.2.2 a ha) hj))
  case construct f args ihf iha =>
    rw [ihf h.1 hj]
    congr 1
    simpa using (List.map_congr_left (g := id) (fun a ha => iha a ha (h.2 a ha) hj))
  case letE x b ihx ihb => rw [ihx h.1 hj, ihb h.2 (by omega)]
  case attach n f k ns args ihf ihargs =>
    have hmap : args.map (subst j a) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (h.2 x hx) hj))
    rw [ihf h.1 (by omega), hmap]
  case objVariadic l n b ih => rw [ih h (by omega)]
  case makeVariadic n f ns args ihf ihargs =>
    have hmap : args.map (subst j a) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (h.2 x hx) hj))
    rw [ihf h.1 (by omega), hmap]
  case objBound fs t r pre iht ihr ihp =>
    have hmap : pre.map (subst j a) = pre := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihp x hx (h.2.2 x hx) hj))
    rw [iht h.1 hj, ihr h.2.1 hj, hmap]
  case makeBound t r pre ns args iht ihr ihp ihargs =>
    have hpre : pre.map (subst j a) = pre := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihp x hx (h.2.2.1 x hx) hj))
    have hmap : args.map (subst j a) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (h.2.2.2 x hx) hj))
    rw [iht h.1 hj, ihr h.2.1 hj, hpre, hmap]
  case write f b c ihb ihc => rw [ihb h.1 hj, ihc h.2 hj]
  case arith op b c ihb ihc => rw [ihb h.1 hj, ihc h.2 hj]
  case ite c b e ihc ihb ihe => rw [ihc h.1 hj, ihb h.2.1 hj, ihe h.2.2 hj]
  case alloc ns args ihargs =>
    have hmap : args.map (subst j a) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (h x hx) hj))
    rw [hmap]
  case arrLit args ihargs =>
    have hmap : args.map (subst j a) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (h x hx) hj))
    rw [hmap]
  case elemAt b c ihb ihc => rw [ihb h.1 hj, ihc h.2 hj]
  case setElem b c e ihb ihc ihe => rw [ihb h.1 hj, ihc h.2.1 hj, ihe h.2.2 hj]
  case lenOf b ih => rw [ih h hj]
  case spread b ih => rw [ih h hj]
  case throw b ih => rw [ih h hj]
  case merge dr b c ihb ihc => rw [ihb h.1 hj, ihc h.2 hj]
  case read f b ih => rw [ih h hj]
  case index b key ihb ihkey => rw [ihb h.1 hj, ihkey h.2 hj]
  case test k b ih => rw [ih h hj]
  case objGraph fs n E K st caps _ ihc =>
    have hmap : caps.map (subst j a) = caps := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihc x hx (h x hx) hj))
    rw [hmap]
  case makeGraph n E K st caps ns args _ ihc iha =>
    have hc : caps.map (subst j a) = caps := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihc x hx (h.1 x hx) hj))
    have hmap : args.map (subst j a) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => iha x hx (h.2 x hx) hj))
    rw [hc, hmap]
  case goto E K l L x _ ihL ihx =>
    have hL : L.map (subst j a) = L := by
      simpa using (List.map_congr_left (g := id) (fun y hy => ihL y hy (h.1 y hy) hj))
    rw [hL, ihx h.2 hj]
  case frame E K t L x k hd _ iht ihL ihx =>
    have hL : L.map (subst j a) = L := by
      simpa using (List.map_congr_left (g := id) (fun y hy => ihL y hy (h.2.1 y hy) hj))
    rw [iht h.1 hj, hL, ihx h.2.2 hj]
  all_goals rfl

theorem Scoped.closed {t : Tm} (h : Scoped 0 t) : Closed t :=
  fun j a => subst_above h (Nat.zero_le j) a

theorem subst_scoped {t a : Tm} {d j : Nat} (ht : Scoped (d + 1) t)
    (ha : Scoped 0 a) (hj : j ≤ d) : Scoped d (subst j a t) := by
  induction t using Tm.induct generalizing d j <;> simp only [Scoped, scopedArgs_iff, subst, substArgs_eq_map] at *
  case var i =>
    split
    · exact ha.mono (Nat.zero_le d)
    · rename_i hn
      have hne : i ≠ j := by simpa using hn
      split <;> simp only [Scoped, scopedArgs_iff] <;> omega
  case objClosure l n b k ih => exact ih (by simpa [Nat.add_right_comm] using ht) (by omega)
  case invoke f r args ihf ihr iha =>
    refine ⟨ihf ht.1 hj, ihr ht.2.1 hj, ?_⟩
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact iha a ha (ht.2.2 a ha) hj
  case construct f args ihf iha =>
    refine ⟨ihf ht.1 hj, ?_⟩
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact iha a ha (ht.2 a ha) hj
  case letE x b ihx ihb => exact ⟨ihx ht.1 hj, ihb ht.2 (by omega)⟩
  case attach n f k ns args ihf ihargs =>
    refine ⟨ihf (by simpa [Nat.add_right_comm] using ht.1) (by omega), ?_⟩
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihargs x hx (ht.2 x hx) hj
  case objVariadic l n b ih =>
    exact ih (d := d + n + 2) (by rw [show d + n + 2 + 1 = d + 1 + n + 2 by omega]; exact ht)
      (by omega)
  case makeVariadic n f ns args ihf ihargs =>
    refine ⟨ihf (d := d + n + 2) (by rw [show d + n + 2 + 1 = d + 1 + n + 2 by omega]; exact ht.1)
      (by omega), ?_⟩
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihargs x hx (ht.2 x hx) hj
  case objBound fs t r pre iht ihr ihp =>
    refine ⟨iht ht.1 hj, ihr ht.2.1 hj, ?_⟩
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihp x hx (ht.2.2 x hx) hj
  case makeBound t r pre ns args iht ihr ihp ihargs =>
    refine ⟨iht ht.1 hj, ihr ht.2.1 hj, ?_, ?_⟩
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact ihp x hx (ht.2.2.1 x hx) hj
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact ihargs x hx (ht.2.2.2 x hx) hj
  case write f b c ihb ihc => exact ⟨ihb ht.1 hj, ihc ht.2 hj⟩
  case arith op b c ihb ihc => exact ⟨ihb ht.1 hj, ihc ht.2 hj⟩
  case ite c b e ihc ihb ihe => exact ⟨ihc ht.1 hj, ihb ht.2.1 hj, ihe ht.2.2 hj⟩
  case alloc ns args ihargs =>
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihargs x hx (ht x hx) hj
  case arrLit args ihargs =>
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihargs x hx (ht x hx) hj
  case elemAt b c ihb ihc => exact ⟨ihb ht.1 hj, ihc ht.2 hj⟩
  case index b c ihb ihc => exact ⟨ihb ht.1 hj, ihc ht.2 hj⟩
  case setElem b c e ihb ihc ihe => exact ⟨ihb ht.1 hj, ihc ht.2.1 hj, ihe ht.2.2 hj⟩
  case lenOf b ih => exact ih ht hj
  case spread b ih => exact ih ht hj
  case throw b ih => exact ih ht hj
  case merge dr b c ihb ihc => exact ⟨ihb ht.1 hj, ihc ht.2 hj⟩
  case read f b ih => exact ih ht hj
  case test k b ih => exact ih ht hj
  case objGraph fs n E K st caps _ ihc =>
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihc x hx (ht x hx) hj
  case makeGraph n E K st caps ns args _ ihc iha =>
    refine ⟨?_, ?_⟩
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact ihc x hx (ht.1 x hx) hj
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact iha x hx (ht.2 x hx) hj
  case goto E K l L x _ ihL ihx =>
    refine ⟨?_, ihx ht.2 hj⟩
    intro v hv
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    exact ihL y hy (ht.1 y hy) hj
  case frame E K t L x k hd _ iht ihL ihx =>
    refine ⟨iht ht.1 hj, ?_, ihx ht.2.2 hj⟩
    intro v hv
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    exact ihL y hy (ht.2.1 y hy) hj
  all_goals trivial


theorem instantiate_scoped (ρ : Env) (hρ : ∀ i, Scoped 0 (ρ i)) (t : Tm) (d : Nat) :
    Scoped d (instantiate d ρ t) := by
  induction t using Tm.induct generalizing d <;> simp only [instantiate, instantiateArgs_eq_map, Scoped, scopedArgs_iff] at *
  case var i => split <;> first | assumption | exact (hρ _).mono (Nat.zero_le d)
  case objClosure l n b k ih => exact ih _
  case invoke f r args ihf ihr iha =>
    refine ⟨ihf _, ihr _, ?_⟩
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact iha a ha d
  case construct f args ihf iha =>
    refine ⟨ihf _, ?_⟩
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact iha a ha d
  case letE a b iha ihb => exact ⟨iha _, ihb _⟩
  case attach n f k ns args ihf ihargs =>
    refine ⟨ihf _, ?_⟩
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihargs x hx d
  case objVariadic l n b ih => exact ih _
  case makeVariadic n f ns args ihf ihargs =>
    refine ⟨ihf _, ?_⟩
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihargs x hx d
  case objBound fs t r pre iht ihr ihp =>
    refine ⟨iht _, ihr _, ?_⟩
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihp x hx d
  case makeBound t r pre ns args iht ihr ihp ihargs =>
    refine ⟨iht _, ihr _, ?_, ?_⟩
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact ihp x hx d
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact ihargs x hx d
  case write f a b iha ihb => exact ⟨iha _, ihb _⟩
  case arith op a b iha ihb => exact ⟨iha _, ihb _⟩
  case ite c a b ihc iha ihb => exact ⟨ihc _, iha _, ihb _⟩
  case alloc ns args ihargs =>
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihargs x hx d
  case arrLit args ihargs =>
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihargs x hx d
  case elemAt a b iha ihb => exact ⟨iha _, ihb _⟩
  case index a b iha ihb => exact ⟨iha _, ihb _⟩
  case setElem a b c iha ihb ihc => exact ⟨iha _, ihb _, ihc _⟩
  case lenOf a ih => exact ih _
  case spread a ih => exact ih _
  case throw a ih => exact ih _
  case merge dr a b iha ihb => exact ⟨iha _, ihb _⟩
  case read f a ih => exact ih d
  case test k a ih => exact ih d
  case objGraph fs n E K st caps _ ihc =>
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
    exact ihc x hx d
  case makeGraph n E K st caps ns args _ ihc iha =>
    refine ⟨?_, ?_⟩
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact ihc x hx d
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact iha x hx d
  case goto E K l L x _ ihL ihx =>
    refine ⟨?_, ihx d⟩
    intro v hv
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    exact ihL y hy d
  case frame E K t L x k hd _ iht ihL ihx =>
    refine ⟨iht d, ?_, ihx d⟩
    intro v hv
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hv
    exact ihL y hy d
  all_goals trivial

/-- Closing a lambda and applying it agrees with extending its environment. -/
theorem instantiate_beta (ρ : Env) (hρ : ∀ i, Scoped 0 (ρ i)) (a t : Tm) (d : Nat) :
    subst d a (instantiate (d + 1) ρ t) = instantiate d (push a ρ) t := by
  induction t using Tm.induct generalizing d <;> simp only [instantiate, instantiateArgs_eq_map, subst, substArgs_eq_map] at *
  case var i =>
    by_cases h : i < d
    · simp [show i < d + 1 by omega, h, subst, show i ≠ d by omega, show ¬d < i by omega]
    · by_cases he : i = d
      · subst i; simp [subst, push]
      · have hi : ¬ i < d + 1 := by omega
        have heq : i - d = (i - (d + 1)) + 1 := by omega
        simp only [if_neg hi, if_neg h, heq, push]
        exact (hρ _).closed d a
  case objClosure l n b k ih => rw [show d + 1 + n + 1 = d + n + 1 + 1 by omega, ih]
  case invoke f r args ihf ihr iha =>
    rw [ihf, ihr, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact iha a ha d
  case construct f args ihf iha =>
    rw [ihf, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact iha a ha d
  case letE a b iha ihb => rw [iha, ihb]
  case attach n f k ns args ihf ihargs =>
    rw [show d + 1 + n + 1 = d + n + 1 + 1 by omega, ihf, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact ihargs x hx d
  case objVariadic l n b ih => rw [show d + 1 + n + 2 = d + n + 2 + 1 by omega, ih]
  case makeVariadic n f ns args ihf ihargs =>
    rw [show d + 1 + n + 2 = d + n + 2 + 1 by omega, ihf, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact ihargs x hx d
  case objBound fs t r pre iht ihr ihp =>
    have hmap : List.map (subst d a ∘ instantiate (d + 1) ρ) pre =
        List.map (instantiate d (push a ρ)) pre :=
      List.map_congr_left (fun x hx => ihp x hx d)
    rw [iht, ihr, List.map_map, hmap]
  case makeBound t r pre ns args iht ihr ihp ihargs =>
    have hpre : List.map (subst d a ∘ instantiate (d + 1) ρ) pre =
        List.map (instantiate d (push a ρ)) pre :=
      List.map_congr_left (fun x hx => ihp x hx d)
    have hmap : List.map (subst d a ∘ instantiate (d + 1) ρ) args =
        List.map (instantiate d (push a ρ)) args :=
      List.map_congr_left (fun x hx => ihargs x hx d)
    rw [iht, ihr, List.map_map, List.map_map, hpre, hmap]
  case write f b c ihb ihc => rw [ihb, ihc]
  case arith op b c ihb ihc => rw [ihb, ihc]
  case ite c b e ihc ihb ihe => rw [ihc, ihb, ihe]
  case alloc ns args ihargs =>
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact ihargs x hx d
  case arrLit args ihargs =>
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact ihargs x hx d
  case elemAt b c ihb ihc => rw [ihb, ihc]
  case setElem b c e ihb ihc ihe => rw [ihb, ihc, ihe]
  case lenOf b ih => rw [ih]
  case spread b ih => rw [ih]
  case throw b ih => rw [ih]
  case merge dr b c ihb ihc => rw [ihb, ihc]
  case read f b ih => rw [ih]
  case index b key ihb ihkey => rw [ihb, ihkey]
  case test k b ih => rw [ih]
  case objGraph fs n E K st caps _ ihc =>
    rw [List.map_map]
    congr 2
    exact List.map_congr_left (fun x hx => ihc x hx d)
  case makeGraph n E K st caps ns args _ ihc iha =>
    have hc : List.map (subst d a ∘ instantiate (d + 1) ρ) caps =
        List.map (instantiate d (push a ρ)) caps :=
      List.map_congr_left (fun x hx => ihc x hx d)
    have hmap : List.map (subst d a ∘ instantiate (d + 1) ρ) args =
        List.map (instantiate d (push a ρ)) args :=
      List.map_congr_left (fun x hx => iha x hx d)
    rw [List.map_map, List.map_map, hc, hmap]
  case goto E K l L x _ ihL ihx =>
    rw [List.map_map, ihx]
    congr 1
    exact List.map_congr_left (fun y hy => ihL y hy d)
  case frame E K t L x k hd _ iht ihL ihx =>
    rw [List.map_map, ihx, iht]
    congr 1
    exact List.map_congr_left (fun y hy => ihL y hy d)
  all_goals rfl

/-- Put parameters in declaration order before the captured environment.
Slot zero is the first parameter, not the last argument evaluated. -/
def prependArgs (args : List Tm) (ρ : Env) : Env := args.foldr push ρ

theorem prependArgs_scoped (hargs : ∀ a ∈ args, Scoped 0 a)
    (hρ : ∀ i, Scoped 0 (ρ i)) : ∀ i, Scoped 0 (prependArgs args ρ i) := by
  induction args with
  | nil => exact hρ
  | cons a args ih =>
    intro i
    cases i with
    | zero => exact hargs a (by simp)
    | succ i => exact ih (fun a ha => hargs a (by simp [ha])) i

/-- Closing captures and then binding any number of parameters agrees with a
single simultaneous substitution. The theorem includes nested closure bodies. -/
theorem instantiate_args (ρ : Env) (hρ : ∀ i, Scoped 0 (ρ i))
    (hargs : ∀ a ∈ args, Scoped 0 a) (t : Tm) (d : Nat) :
    bindArgs d args (instantiate (d + args.length) ρ t) =
      instantiate d (prependArgs args ρ) t := by
  induction args generalizing d with
  | nil => simp [bindArgs, prependArgs]
  | cons a args ih =>
    have hrest : ∀ a ∈ args, Scoped 0 a := fun a ha => hargs a (by simp [ha])
    have level : d + (a::args).length = (d + 1) + args.length := by simp; omega
    simp only [bindArgs, level]
    rw [ih hrest (d + 1)]
    exact instantiate_beta _ (prependArgs_scoped hrest hρ) a t d

theorem instantiate_above {t : Tm} {d : Nat} (ht : Scoped d t) (ρ : Env) :
    instantiate d ρ t = t := by
  induction t using Tm.induct generalizing d <;> simp only [Scoped, scopedArgs_iff, instantiate, instantiateArgs_eq_map] at *
  case var i => simp [ht]
  case objClosure l n b k ih => rw [ih ht]
  case invoke f r args ihf ihr iha =>
    rw [ihf ht.1, ihr ht.2.1]
    congr 1
    simpa using (List.map_congr_left (g := id) (fun a ha => iha a ha (ht.2.2 a ha)))
  case construct f args ihf iha =>
    rw [ihf ht.1]
    congr 1
    simpa using (List.map_congr_left (g := id) (fun a ha => iha a ha (ht.2 a ha)))
  case letE a b iha ihb => rw [iha ht.1, ihb ht.2]
  case attach n f k ns args ihf ihargs =>
    have hmap : args.map (instantiate d ρ) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (ht.2 x hx)))
    rw [ihf ht.1, hmap]
  case objVariadic l n b ih => rw [ih ht]
  case makeVariadic n f ns args ihf ihargs =>
    have hmap : args.map (instantiate d ρ) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (ht.2 x hx)))
    rw [ihf ht.1, hmap]
  case objBound fs t r pre iht ihr ihp =>
    have hmap : pre.map (instantiate d ρ) = pre := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihp x hx (ht.2.2 x hx)))
    rw [iht ht.1, ihr ht.2.1, hmap]
  case makeBound t r pre ns args iht ihr ihp ihargs =>
    have hpre : pre.map (instantiate d ρ) = pre := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihp x hx (ht.2.2.1 x hx)))
    have hmap : args.map (instantiate d ρ) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (ht.2.2.2 x hx)))
    rw [iht ht.1, ihr ht.2.1, hpre, hmap]
  case write f a b iha ihb => rw [iha ht.1, ihb ht.2]
  case arith op a b iha ihb => rw [iha ht.1, ihb ht.2]
  case ite c a b ihc iha ihb => rw [ihc ht.1, iha ht.2.1, ihb ht.2.2]
  case alloc ns args ihargs =>
    have hmap : args.map (instantiate d ρ) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (ht x hx)))
    rw [hmap]
  case arrLit args ihargs =>
    have hmap : args.map (instantiate d ρ) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihargs x hx (ht x hx)))
    rw [hmap]
  case elemAt a b iha ihb => rw [iha ht.1, ihb ht.2]
  case index a b iha ihb => rw [iha ht.1, ihb ht.2]
  case setElem a b c iha ihb ihc => rw [iha ht.1, ihb ht.2.1, ihc ht.2.2]
  case lenOf a ih => rw [ih ht]
  case spread a ih => rw [ih ht]
  case throw a ih => rw [ih ht]
  case merge dr a b iha ihb => rw [iha ht.1, ihb ht.2]
  case read f a ih => rw [ih ht]
  case test k a ih => rw [ih ht]
  case objGraph fs n E K st caps _ ihc =>
    have hmap : caps.map (instantiate d ρ) = caps := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihc x hx (ht x hx)))
    rw [hmap]
  case makeGraph n E K st caps ns args _ ihc iha =>
    have hc : caps.map (instantiate d ρ) = caps := by
      simpa using (List.map_congr_left (g := id) (fun x hx => ihc x hx (ht.1 x hx)))
    have hmap : args.map (instantiate d ρ) = args := by
      simpa using (List.map_congr_left (g := id) (fun x hx => iha x hx (ht.2 x hx)))
    rw [hc, hmap]
  case goto E K l L x _ ihL ihx =>
    have hL : L.map (instantiate d ρ) = L := by
      simpa using (List.map_congr_left (g := id) (fun y hy => ihL y hy (ht.1 y hy)))
    rw [hL, ihx ht.2]
  case frame E K t L x k hd _ iht ihL ihx =>
    have hL : L.map (instantiate d ρ) = L := by
      simpa using (List.map_congr_left (g := id) (fun y hy => ihL y hy (ht.2.1 y hy)))
    rw [iht ht.1, hL, ihx ht.2.2]
  all_goals rfl

/-- Binding closed arguments closes exactly their parameter slots, leaving the
specified enclosing binders. Captures were already closed by the descriptor. -/
theorem bindArgs_scoped (ht : Scoped (d + args.length) t)
    (hargs : ∀ a ∈ args, Scoped 0 a) : Scoped d (bindArgs d args t) := by
  let ρ : Env := fun _ => .nul
  have hρ : ∀ i, Scoped 0 (ρ i) := fun _ => trivial
  rw [← instantiate_above ht ρ, instantiate_args ρ hρ hargs]
  exact instantiate_scoped _ (prependArgs_scoped hargs hρ) t d

#print axioms instantiate_args
#print axioms bindArgs_scoped

end Verification.Model
