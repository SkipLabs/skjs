import Verification.Model.Types.TypeAlgebra

/-! A nonempty conjunction of record contracts. Keeping the first operand
explicit prevents the empty conjunction from silently becoming top.

An operand is a finite map from field names to contracts, and each names only
the fields it constrains. Two operands therefore meet only where they name the
same field, which is what makes a conjunction of contracts on disjoint fields
the composed record rather than the empty type. -/
namespace Verification.Model.ReferenceConjunctions

/-- What one operand says: a contract per named field. -/
abbrev Fields := List (PropKey × Fam)

def refsT (A : Fields) (Bs : List Fields) : Fam := fun n W v =>
  recT A n W v ∧ ∀ B ∈ Bs, recT B n W v

theorem singleton (A : Fields) (n : Nat) (W : WorldT n) (v : Val) :
    refsT A [] n W v ↔ recT A n W v := by simp [refsT]

theorem cell (A : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    refsT [(valueField, A)] [] n W v ↔ refT A n W v := by simp [refsT, refT]

theorem merge (A C : Fields) (Bs Ds : List Fields) (n : Nat) (W : WorldT n) (v : Val) :
    refsT A (Bs ++ C :: Ds) n W v ↔ interT (refsT A Bs) (refsT C Ds) n W v := by
  simp only [refsT, List.mem_append, List.mem_cons,
    or_imp, forall_and, interT]
  simp only [forall_eq]
  constructor
  · rintro ⟨ha, hb, hc, hd⟩; exact ⟨⟨ha, hb⟩, hc, hd⟩
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩; exact ⟨ha, hb, hc, hd⟩

theorem adm (A : Fields) (Bs : List Fields) : Adm (refsT A Bs) := by
  constructor
  · intro n W v h
    exact ⟨(recT_adm A).down n W v h.1,
      fun B hb => (recT_adm B).down n W v (h.2 B hb)⟩
  · intro n W U hx v h
    exact ⟨(recT_adm A).mono n W U hx v h.1,
      fun B hb => (recT_adm B).mono n W U hx v (h.2 B hb)⟩

/-- The families a label map denotes, field by field. -/
def famsOf {ι : Type} (X : ι → Fam) (fs : List (PropKey × ι)) : Fields :=
  fs.map (fun p => (p.1, X p.2))

theorem mem_famsOf {ι : Type} {X : ι → Fam} {fs : List (PropKey × ι)} {f : PropKey} {A : Fam} :
    (f, A) ∈ famsOf X fs ↔ ∃ i, (f, i) ∈ fs ∧ A = X i := by
  simp only [famsOf, List.mem_map]
  constructor
  · rintro ⟨⟨g, i⟩, hp, he⟩
    cases he
    exact ⟨i, hp, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(f, i), hi, rfl⟩

theorem recT_congr_below {ι : Type} (X Y : ι → Fam) (a : List (PropKey × ι)) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    recT (famsOf X a) n W v ↔ recT (famsOf Y a) n W v := by
  constructor <;> rintro ⟨flds, rfl, hfs⟩ <;> refine ⟨flds, rfl, ?_⟩ <;>
      intro f T hm <;> obtain ⟨i, hi, rfl⟩ := mem_famsOf.mp hm
  · obtain ⟨l, c, hl, hw, hag⟩ := hfs f (X i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
    exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).trans (h i j hj W' u)⟩
  · obtain ⟨l, c, hl, hw, hag⟩ := hfs f (Y i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
    exact ⟨l, c, hl, hw, fun j hj W' u => (hag j hj W' u).trans (h i j hj W' u).symm⟩

theorem famsOf_append {ι : Type} (X : ι → Fam) (a b : List (PropKey × ι)) :
    famsOf X (a ++ b) = famsOf X a ++ famsOf X b := List.map_append ..

theorem view_congr_below {ι : Type} (X Y : ι → Fam) (a : List (PropKey × ι)) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    viewT (famsOf X a) n W v ↔ viewT (famsOf Y a) n W v := by
  constructor <;> intro hv f T hm <;> obtain ⟨i, hi, rfl⟩ := mem_famsOf.mp hm
  · obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ := hv f (X i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
    exact ⟨flds, l, c, rfl, hf, hl, fun j hj W' u hu => (h i j hj W' u).mp (hag j hj W' u hu)⟩
  · obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ := hv f (Y i) (mem_famsOf.mpr ⟨i, hi, rfl⟩)
    exact ⟨flds, l, c, rfl, hf, hl, fun j hj W' u hu => (h i j hj W' u).mpr (hag j hj W' u hu)⟩

theorem congr_below {ι : Type} (X Y : ι → Fam) (a : List (PropKey × ι))
    (bs : List (List (PropKey × ι))) (n : Nat)
    (h : ∀ i, Agree (X i) (Y i) n) (W : WorldT n) (v : Val) :
    refsT (famsOf X a) (bs.map (famsOf X)) n W v ↔
      refsT (famsOf Y a) (bs.map (famsOf Y)) n W v := by
  simp only [refsT, List.forall_mem_map]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨(recT_congr_below X Y a n h W v).mp ha,
      fun b hm => (recT_congr_below X Y b n h W v).mp (hb b hm)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨(recT_congr_below X Y a n h W v).mpr ha,
      fun b hm => (recT_congr_below X Y b n h W v).mpr (hb b hm)⟩

/-- All constraints on one field describe the same stored contract, so their
operands agree at the budgets at which that contract can be observed. Two
operands that name no field in common constrain different locations and are
not compared at all. -/
theorem operands_agree {A B : Fields} {Bs : List Fields} {n W v} {f : PropKey} {P Q : Fam}
    (h : refsT A Bs n W v) (hb : B ∈ Bs) (hp : (f, P) ∈ A) (hq : (f, Q) ∈ B) :
    Agree P Q n := by
  obtain ⟨flds, l, c, rfl, hf, hl, ha⟩ := recT_at hp h.1
  obtain ⟨flds', l', c', he, hf', hl', hc⟩ := recT_at hq (h.2 B hb)
  cases he
  cases Option.some.inj (hf.symm.trans hf')
  cases hl'.symm.trans hl
  intro j hj U u
  exact (ha j hj U u).symm.trans (hc j hj U u)

/-- Every operand constrains the same object, so a field any of them names is
a field of that object, with the contract that operand gives it. -/
theorem refsT_field {A : Fields} {Bs : List Fields} {n W v} {f : PropKey} {P : Fam}
    (h : refsT A Bs n W v) (hm : (f, P) ∈ A ∨ ∃ B ∈ Bs, (f, P) ∈ B) :
    ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr n),
      v = .objAt flds .absent ∧ flds.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < n) (W' : WorldT j) (u : Val), c j hj W' u ↔ P j W' u := by
  rcases hm with hm | ⟨B, hB, hm⟩
  · exact recT_at hm h.1
  · exact recT_at hm (h.2 B hB)

/-- A read of a named field satisfies every operand constraining that field,
at every available lower budget. -/
theorem read_all {A : Fields} {Bs : List Fields} {n W heap}
    {flds : List (PropKey × Nat)} {f : PropKey} {P : Fam} {l : Nat}
    (hok : HeapOk n W heap) (hr : refsT A Bs n W (.objAt flds .absent))
    (hp : (f, P) ∈ A) (hf : flds.lookup f = some l) :
    ∃ v, heap[l]? = some v ∧ ∀ j (hj : j < n),
      P j (trunc j (Nat.le_of_lt hj) W) v ∧
      ∀ B ∈ Bs, ∀ Q, (f, Q) ∈ B → Q j (trunc j (Nat.le_of_lt hj) W) v := by
  obtain ⟨flds', l', c, he, hf', hl, hc⟩ := recT_at hp hr.1
  cases he
  cases Option.some.inj (hf'.symm.trans hf)
  obtain ⟨v, hv, hm⟩ := read_sound n W heap l c hok hl
  refine ⟨v, hv, ?_⟩
  intro j hj
  have ha := (hc j hj _ v).mp (hm j hj)
  exact ⟨ha, fun B hb Q hq => (operands_agree hr hb hp hq j hj _ v).mp ha⟩

/-- Writing a value satisfying even one operand's constraint on the field
suffices: every operand constraining it agrees with the same invariant below
this budget. Aliased heap satisfaction survives, and no other field moves. -/
theorem write_first {A : Fields} {Bs : List Fields} {n W heap}
    {flds : List (PropKey × Nat)} {f : PropKey} {P : Fam} {l : Nat} {v : Val}
    (hok : HeapOk n W heap) (hr : refsT A Bs n W (.objAt flds .absent))
    (hp : (f, P) ∈ A) (hf : flds.lookup f = some l)
    (hv : ∀ j (hj : j < n), P j (trunc j (Nat.le_of_lt hj) W) v) :
    HeapOk n W (heap.set l v) := by
  obtain ⟨flds', l', c, he, hf', hl, hc⟩ := recT_at hp hr.1
  cases he
  cases Option.some.inj (hf'.symm.trans hf)
  exact write_sound n W heap l c v hok hl (fun j hj => (hc j hj _ v).mpr (hv j hj))

theorem duplicate (A : Fields) (n : Nat) (W : WorldT n) (v : Val) :
    refsT A [A] n W v ↔ recT A n W v := by simp [refsT]

/-- Both constraints on the cyclic reference are inhabited in a satisfying heap. -/
theorem cyclic_inhabited (n : Nat) :
    HeapOk n (ofList [res R]) [.obj 0 .absent] ∧
    refsT [(valueField, R)] [[(valueField, R)]] n (ofList [res R]) (.obj 0 .absent) :=
  ⟨cyclic_heap_ok n, (duplicate [(valueField, R)] n _ _).mpr
    ((R_unfold n _ _).mp (R_cyclic n))⟩

/-- Incompatible contracts must remain visible at zero; dropping the entire
conjunction as bottom would not preserve the current indexed interpretation. -/
theorem incompatible_at_zero :
    refsT [(valueField, nulT)] [[(valueField, boolT)]] 0 (ofList [res nulT])
      (.obj 0 .absent) := by
  have hr : ∀ A : Fam, refT A 0 (ofList [res nulT]) (.obj 0 .absent) := by
    intro A
    exact refT_cell (c := res nulT) (by simp [lookup]) (fun j hj => by omega)
  refine ⟨hr nulT, ?_⟩
  intro B hB
  simp only [List.mem_singleton] at hB
  subst hB
  exact hr boolT

theorem incompatible_positive {n : Nat} (hn : 0 < n) (W : WorldT n) (v : Val) :
    ¬ refsT [(valueField, nulT)] [[(valueField, boolT)]] n W v := by
  intro h
  have he := operands_agree (B := [(valueField, boolT)]) (f := valueField)
    (P := nulT) (Q := boolT) h (by simp) (by simp) (by simp) 0 hn (ofList []) .nul
  have hb := he.mp rfl
  simp [boolT] at hb

#print axioms read_all
#print axioms cyclic_inhabited
end Verification.Model.ReferenceConjunctions
