import Verification.ExperimentState.PositiveGraphs

/-! Declarative subtyping for positive recursive graphs. Rules have only finite
syntactic premises; semantic soundness is a separate theorem. -/
namespace Verification.ExperimentState.PositiveRules
open PositiveNormalization PositiveGraphs ReferenceConjunctions Tower

abbrev Table (ι : Type) := List (List ι × List ι)
abbrev Rel (table : Table ι) (a b : List ι) : Prop := (a, b) ∈ table

abbrev Ops (ι : Type) := List (List ι × List ι)
def expand (G : NormalGraph ι) (S : List ι) : List (Clause (List ι)) := S.flatMap G

/-- Decompose one clause into an exactly equivalent finite union. `bool` is the
only clause of this language whose inhabitants are a finite set, so it is the
only one that decomposes: every Boolean value is `true` or `false`. Everything
else is already its own decomposition. -/
def splitClause : Clause α → List (Clause α)
  | .bool => [.boolLit true, .boolLit false]
  | c => [c]

/-- The clauses a covering obligation must discharge on its left. Splitting the
source, rather than searching the target for a matching pair, keeps `Covers`
clause-to-clause while letting one source clause be covered by several target
clauses. -/
def sourceClauses (G : NormalGraph ι) (S : List ι) : List (Clause (List ι)) :=
  (expand G S).flatMap splitClause

def meaning (G : NormalGraph ι) (S : List ι) : Fam := setSem (normalDenote G) S

/-- A conservative compatibility check: two union labels can share a value
only if some pair of their clauses has the same outer shape. -/
def compatible (G : NormalGraph ι) (i k : ι) : Bool :=
  (G i).any fun a => (G k).any fun b => shape a == shape b

theorem normal_congr (G : NormalGraph ι) : LayerCongr (normalLayer G) := by
  intro X Y n h i W v
  constructor <;> rintro ⟨c, hc, hv⟩ <;> refine ⟨c, hc, ?_⟩
  · exact (sem_congr _ _ n (fun a => setSem_congr n h a) c W v).mp hv
  · exact (sem_congr _ _ n (fun a => setSem_congr n h a) c W v).mpr hv

theorem unfold_normal (G : NormalGraph ι) (i : ι) (n W v) :
    normalDenote G i n W v ↔ semList (meaning G) (G i) n W v :=
  Tower.denote_unfold (normal_congr G) i n W v

theorem expand_sem (G : NormalGraph ι) (S : List ι) (n W v) :
    meaning G S n W v ↔ semList (meaning G) (expand G S) n W v := by
  constructor
  · rintro ⟨i, hi, hv⟩
    obtain ⟨c, hc, hv⟩ := (unfold_normal G i n W v).mp hv
    exact ⟨c, List.mem_flatMap.mpr ⟨i, hi, hc⟩, hv⟩
  · rintro ⟨c, hc, hv⟩
    obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
    exact ⟨i, hi, (unfold_normal G i n W v).mpr ⟨c, hc, hv⟩⟩

/-- The split is meaning preserving, in the same style as `meet_sound` and
`normalize_sound`: the union of the parts denotes exactly the original clause. -/
theorem splitClause_sem (X : α → Fam) (c : Clause α) (n W v) :
    semList X (splitClause c) n W v ↔ sem X c n W v := by
  cases c
  all_goals simp [splitClause, semList, setSem, sem, boolT]

theorem source_sem (G : NormalGraph ι) (S : List ι) (n W v) :
    meaning G S n W v ↔ semList (meaning G) (sourceClauses G S) n W v := by
  rw [expand_sem G S n W v]
  constructor
  · rintro ⟨c, hc, hv⟩
    obtain ⟨d, hd, hvd⟩ := (splitClause_sem (meaning G) c n W v).mpr hv
    exact ⟨d, List.mem_flatMap.mpr ⟨c, hc, hd⟩, hvd⟩
  · rintro ⟨d, hd, hv⟩
    obtain ⟨c, hc, hd⟩ := List.mem_flatMap.mp hd
    exact ⟨c, hc, (splitClause_sem (meaning G) c n W v).mp ⟨d, hd, hv⟩⟩

theorem compatible_sound {G : NormalGraph ι} {i k : ι} {n W U v}
    (hi : normalDenote G i n W v) (hk : normalDenote G k n U v) :
    compatible G i k = true := by
  obtain ⟨a, ha, hva⟩ := (unfold_normal G i n W v).mp hi
  obtain ⟨b, hb, hvb⟩ := (unfold_normal G k n U v).mp hk
  simp only [compatible, List.any_eq_true, beq_iff_eq]
  exact ⟨a, ha, b, hb, (sem_shape hva).symm.trans (sem_shape hvb)⟩

def FamLeAt (G : NormalGraph ι) (a b : List ι) (n : Nat) : Prop :=
  ∀ (W : WorldT n) (v : Val), meaning G a n W v → meaning G b n W v

inductive Arrow (G : NormalGraph ι) (R : List ι → List ι → Prop)
    (L : Ops ι) : List ι → List ι → Prop where
  | empty : Arrow G R L [] d
  | source : p ∈ L → R c p.1 → (p.2 = [] ∨ R p.2 d) → Arrow G R L c d
  | union : Arrow G R L a d → Arrow G R L b d → Arrow G R L (a ++ b) d
  | combine : Arrow G R L c b → Arrow G R L c b' →
      (∀ i ∈ b, ∀ k ∈ b', compatible G i k = true → R [i] d) → Arrow G R L c d

/-- Splitting a domain into clauses is derivable by finite union composition. -/
theorem Arrow.split {G : NormalGraph ι} {R L c d}
    (h : ∀ i ∈ c, Arrow G R L [i] d) : Arrow G R L c d := by
  induction c with
  | nil => exact .empty
  | cons i tail ih =>
    exact .union (h i (by simp)) (ih (fun k hk => h k (by simp [hk])))

theorem Arrow.sound {G : NormalGraph ι} {R L c d} (hc : Arrow G R L c d) (n : Nat)
    (hr : ∀ j, j < n → ∀ a b, R a b → FamLeAt G a b j)
    (W : WorldT n) (v : Val)
    (hv : arrowsT (L.map fun p => (meaning G p.1, meaning G p.2)) n W v) :
    arrowT (meaning G c) (meaning G d) n W v := by
  induction hc with
  | empty =>
    refine ⟨hv.1, ?_⟩
    rintro j hj U hx hu h hh x ⟨i, hi, _⟩
    simp at hi
  | source hm hd hc =>
    refine ⟨hv.1, ?_⟩
    intro j hj U hx hu h hh x ha
    have hs := hv.2 _ (List.mem_map_of_mem hm) j hj U hx hu h hh x
      (hr j hj _ _ hd U x ha)
    apply Safe_mono j _ U h _ hs
    intro r hb V u hu
    rcases hc with he | he
    · obtain ⟨i, hi, _⟩ := hu
      simp [he] at hi
    · exact hr r (by omega) _ _ he V u hu
  | union _ _ hl hh =>
    refine ⟨hv.1, ?_⟩
    rintro j hj U hx hu h hok x ⟨i, hi, hxv⟩
    rcases List.mem_append.mp hi with hi | hi
    · exact hl.2 j hj U hx hu h hok x ⟨i, hi, hxv⟩
    · exact hh.2 j hj U hx hu h hok x ⟨i, hi, hxv⟩
  | combine _ _ hg hl hh =>
    refine ⟨hv.1, ?_⟩
    intro j hj U hx hu h hok x ha
    apply safe_cross_upto j _ U U h _ hok hok
      (hl.2 j hj U hx hu h hok x ha) (hh.2 j hj U hx hu h hok x ha)
    rintro r hb V V' heap h1 h2 u ⟨i, hi, hv1⟩ ⟨k, hk, hv2⟩
    exact hr r (by omega) _ _ (hg i hi k hk (compatible_sound hv1 hv2)) V u
      ⟨i, by simp, hv1⟩

def Covers (G : NormalGraph ι) (R : List ι → List ι → Prop) :
    Clause (List ι) → Clause (List ι) → Prop
  | .nul, .nul => True
  | .undef, .undef => True
  | .bool, .bool => True
  | .boolLit _, .bool => True
  | .boolLit a, .boolLit b => a = b
  | .refs a bs, .refs c ds => ∀ b ∈ c :: ds, ∃ x ∈ a :: bs, R x b ∧ R b x
  | .arrs L, .arrs M => ∀ p ∈ M, Arrow G R L p.1 p.2
  | _, _ => False

theorem Covers.sound {G : NormalGraph ι} {R a b} (hc : Covers G R a b) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j)
    (W : WorldT n) (v : Val) : sem (meaning G) a n W v → sem (meaning G) b n W v := by
  cases a <;> cases b <;> simp only [Covers] at hc
  all_goals try contradiction
  · exact id
  · exact id
  · rename_i a bs c ds
    intro hv
    have hall : ∀ x ∈ a :: bs, refT (meaning G x) n W v := by
      simpa [sem, refsT] using hv
    have hout : ∀ b ∈ c :: ds, refT (meaning G b) n W v := by
      intro b hb
      obtain ⟨x, hx, hxb, hbx⟩ := hc b hb
      apply (refT_contractive n (meaning G x) (meaning G b) ?_ W v).mp (hall x hx)
      intro j hj U u
      exact ⟨hr j hj x b hxb U u, hr j hj b x hbx U u⟩
    simpa [sem, refsT] using hout
  · intro hv
    refine ⟨hv.1, ?_⟩
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (Arrow.sound (hc q hq) n hr W v hv).2
  · rename_i b
    cases b <;> intro hv <;> cases hv
    · exact Or.inr rfl
    · exact Or.inl rfl
  · cases hc; exact id
  · exact id

/-- Each split part of each source clause must be covered by some single target
clause. A `bool` source is therefore discharged by the pair of Boolean singleton
clauses, or by a single `bool` clause, or by any target containing both. -/
def Valid (G : NormalGraph ι) (table : Table ι) : Prop :=
  ∀ p ∈ table, ∀ a ∈ sourceClauses G p.1, ∃ b ∈ expand G p.2, Covers G (Rel table) a b

def Core (G : NormalGraph ι) (S T : List ι) : Prop :=
  ∃ table, (S, T) ∈ table ∧ Valid G table

theorem Core.sound {G : NormalGraph ι} {S T} (hc : Core G S T) :
    FamLe (meaning G S) (meaning G T) := by
  obtain ⟨table, hm, hc⟩ := hc
  have hs : ∀ n a b, Rel table a b → FamLeAt G a b n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro A B hab W v hv
      obtain ⟨a, ha, hv⟩ := (source_sem G A n W v).mp hv
      obtain ⟨b, hb, hcover⟩ := hc (A, B) hab a ha
      exact (expand_sem G B n W v).mpr
        ⟨b, hb, Covers.sound hcover n (fun j hj => ih j hj) W v hv⟩
  exact fun n => hs n S T hm

/-- Structural rules compose completed proofs. They cannot bypass the guarded
coverage obligation for any row of a recursive table. -/
inductive Sub (G : NormalGraph ι) : List ι → List ι → Prop where
  | core : Core G S T → Sub G S T
  | subset : (∀ i ∈ S, i ∈ T) → Sub G S T
  | trans : Sub G S U → Sub G U T → Sub G S T

theorem Sub.sound {G : NormalGraph ι} {S T} (h : Sub G S T) :
    FamLe (meaning G S) (meaning G T) := by
  induction h with
  | core h => exact h.sound
  | subset h => rintro n W v ⟨i, hi, hv⟩; exact ⟨i, h i hi, hv⟩
  | trans _ _ ih ih' => exact fun n W v hv => ih' n W v (ih n W v hv)

theorem Sub.refl (G : NormalGraph ι) (S : List ι) : Sub G S S := .subset (fun _ h => h)

theorem Sub.congr {G : NormalGraph ι} {S S' T T' : List ι}
    (hs : ∀ i, i ∈ S ↔ i ∈ S') (ht : ∀ i, i ∈ T ↔ i ∈ T') :
    Sub G S T ↔ Sub G S' T' := by
  constructor
  · intro h
    exact .trans (.subset (fun i hi => (hs i).mpr hi))
      (.trans h (.subset (fun i hi => (ht i).mp hi)))
  · intro h
    exact .trans (.subset (fun i hi => (hs i).mp hi))
      (.trans h (.subset (fun i hi => (ht i).mpr hi)))

#print axioms Sub.sound
end Verification.ExperimentState.PositiveRules