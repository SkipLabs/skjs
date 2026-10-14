import Verification.Semantics.Safety

namespace Verification.OperationResults

/-- A concrete configuration of the existing calculus and its world. -/
structure Config where
  level : Nat
  world : WorldT level
  heap : Heap
  term : Tm

/-- A computation step with exactly the world obligations used by Safe. -/
inductive Edge : Config → Config → Prop where
  | step {n W U h h' t t'} :
      WExt (trunc n (Nat.le_succ n) W) U → WorldAdm U →
      Step h t h' t' → HeapOk n U h' →
      Edge ⟨n+1, W, h, t⟩ ⟨n, U, h', t'⟩

inductive Path : Config → Config → Prop where
  | refl : Path c c
  | snoc : Path c d → Edge d e → Path c e

/-- A second world-annotated execution has the same concrete steps. Its
result world need not coincide with the world chosen by the safety proof. -/
theorem Path.safe_exists {c d : Config} (path : Path c d) (B : Fam) :
    ∀ V : WorldT c.level, Safe Ξ B c.level V c.heap c.term →
      ∃ U : WorldT d.level, Safe Ξ B d.level U d.heap d.term := by
  induction path with
  | refl => intro V h; exact ⟨V, h⟩
  | snoc path edge ih =>
    intro V hs
    obtain ⟨V', hs'⟩ := ih V hs
    cases edge with
    | step he ha step hok =>
      rcases hs' with (⟨hv, _⟩ | thrown) | ⟨U, h', t', hx, hu, st, hh, rest⟩
      · exact False.elim (value_no_step hv step)
      · exact False.elim (thrown.no_step step)
      · obtain ⟨rfl, rfl⟩ := Step_det step st
        exact ⟨U, rest⟩

/-- Outcomes include the actual result world. Each is witnessed by a finite
execution from an input in A with budget left to observe the result. At
budget zero Safe imposes no result obligation, so it supplies no outcome. -/
def Outcomes (op : Val → Tm) (A : Fam) : Fam := fun n W v =>
  (0 < n ∧ isVal v = true ∧ Scoped 0 v) ∧ ∃ k, ∃ U : WorldT k, ∃ h x h',
    WorldAdm U ∧ HeapOk k U h ∧ A k U x ∧
    Path ⟨k, U, h, op x⟩ ⟨n, W, h', v⟩

/-- The least admissible family containing a given family. -/
def closure (A : Fam) : Fam := fun n W v =>
  ∀ B : Fam, Adm B → FamLe A B → B n W v

theorem closure_contains (A : Fam) : FamLe A (closure A) :=
  fun n W v ha _ _ hab => hab n W v ha

theorem closure_le {A B} (hb : Adm B) (hab : FamLe A B) :
    FamLe (closure A) B := fun _ _ _ h => h B hb hab

theorem closure_adm (A : Fam) : Adm (closure A) := by
  constructor
  · intro n W v h B hb hab
    exact hb.down n W v (h B hb hab)
  · intro n W U he v h B hb hab
    exact hb.mono n W U he v (h B hb hab)

theorem closure_mono {A B} (hab : FamLe A B) :
    FamLe (closure A) (closure B) := by
  intro n W v h C hc hbc
  exact h C hc (fun k U u hu => hbc k U u (hab k U u hu))

def values : Fam := fun _ _ v => isVal v = true ∧ Scoped 0 v

theorem values_adm : Adm values := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

/-- Canonical result family: execution outcomes, closed under the existing
semantic type's approximation and world-extension requirements. -/
def result (op : Val → Tm) (A : Fam) : Fam := closure (Outcomes op A)

theorem result_adm (op : Val → Tm) (A : Fam) : Adm (result op A) :=
  closure_adm _

/-- Reuse the SAME world witnesses as an existing safety proof. No
intersection of independently chosen safety derivations is used. -/
theorem safe_result_from {op A} {k} {U : WorldT k} {h x}
    (hu : WorldAdm U) (hh : HeapOk k U h) (hx : A k U x) :
    ∀ n (W : WorldT n) heap t,
      Path ⟨k, U, h, op x⟩ ⟨n, W, heap, t⟩ →
      Safe Ξ values n W heap t → Safe Ξ (result op A) n W heap t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W heap t path hs
    rcases hs with (⟨hv, hclosed⟩ | thrown) | ⟨V, heap', t', he, ha, step, hok, rest⟩
    · exact .inl (.inl ⟨hv, closure_contains _ _ _ _
        ⟨⟨Nat.zero_lt_succ _, hclosed⟩, k, U, h, x, heap, hu, hh, hx, path⟩⟩)
    · exact .inl (.inr thrown)
    · exact .inr ⟨V, heap', t', he, ha, step, hok,
        ih V heap' t' (.snoc path (.step he ha step hok)) rest⟩

theorem safe_result {op A n W heap x}
    (hw : WorldAdm W) (hh : HeapOk n W heap) (hx : A n W x)
    (hs : Safe Ξ values n W heap (op x)) :
    Safe Ξ (result op A) n W heap (op x) :=
  safe_result_from hw hh hx n W heap (op x) .refl hs

theorem result_valid (op : Val → Tm) (A : Fam) : (Adm (result op A) ∧ ∀ n W v, result op A n W v → isVal v = true ∧ Scoped 0 v) :=
  ⟨result_adm op A, closure_le values_adm (fun _ _ _ h => h.1.2)⟩

#print axioms result_valid
#print axioms result_adm
#print axioms safe_result

/-- Lifetime membership of an existing value survives every world step. -/
theorem Path.preserves {c d : Config} (path : Path c d) {B : Fam}
    (hb : Adm B) (v : Val) (hv : B c.level c.world v) :
    B d.level d.world v := by
  induction path with
  | refl => exact hv
  | snoc path edge ih =>
    cases edge with
    | step he _ _ _ => exact hb.mono _ _ _ he v (hb.down _ _ v ih)

theorem outcomes_mono {op A B} (hab : FamLe A B) :
    FamLe (Outcomes op A) (Outcomes op B) := by
  rintro n W v ⟨hv, k, U, h, x, h', hu, hh, hx, path⟩
  exact ⟨hv, k, U, h, x, h', hu, hh, hab k U x hx, path⟩

theorem result_mono {op A B} (hab : FamLe A B) :
    FamLe (result op A) (result op B) := closure_mono (outcomes_mono hab)

theorem result_union (op : Val → Tm) (A B : Fam) :
    result op (unionT A B) = unionT (result op A) (result op B) := by
  funext n W v; apply propext; constructor
  · apply closure_le (unionT_adm _ _ (result_adm op A) (result_adm op B))
    rintro j U u ⟨hv, k, V, h, x, h', hw, hh, hx, path⟩
    rcases hx with hx | hx
    · exact Or.inl (closure_contains _ _ _ _ ⟨hv, k, V, h, x, h', hw, hh, hx, path⟩)
    · exact Or.inr (closure_contains _ _ _ _ ⟨hv, k, V, h, x, h', hw, hh, hx, path⟩)
  · intro h
    rcases h with ha | hb
    · exact result_mono (fun _ _ _ h => Or.inl h) n W v ha
    · exact result_mono (fun _ _ _ h => Or.inr h) n W v hb

def empty : Fam := fun _ _ _ => False

/-- Await is interpreted by invoking the modeled external await intrinsic.
The intrinsic is fixed by the environment, independently of type arguments. -/
def awaited (intrinsic : Val) (A : Fam) : Fam :=
  result (fun x => .invoke intrinsic .undef [x]) A

#print axioms result_union

/-- A safety result that is independent of the choice of world also bounds
all operational outcomes. Heap-sensitive results require a stronger premise. -/
theorem result_le_of_safe {op A B}
    (hb : Adm B)
    (independent : ∀ n (U V : WorldT n) v, B n U v → B n V v)
    (safe : ∀ n (W : WorldT n) heap x, WorldAdm W → HeapOk n W heap →
      A n W x → Safe Ξ B n W heap (op x)) :
    FamLe (result op A) B := by
  apply closure_le hb
  rintro n W v ⟨⟨hn, hv, _⟩, k, U, h, x, h', hu, hh, hx, path⟩
  obtain ⟨V, hs⟩ := path.safe_exists B U (safe k U h x hu hh hx)
  cases n with
  | zero => omega
  | succ n =>
    rcases hs with (⟨_, hB⟩ | thrown) | ⟨_, _, _, _, _, step, _, _⟩
    · exact independent _ V W v hB
    · exact False.elim (val_not_thrown hv thrown)
    · exact False.elim (value_no_step hv step)

#print axioms result_le_of_safe

end Verification.OperationResults
