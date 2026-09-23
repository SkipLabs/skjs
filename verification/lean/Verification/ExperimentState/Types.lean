import Verification.ExperimentState.Worlds
/-!
# Semantic types

A type is a family of approximations indexed by a budget, judged against a world
of the same level. `Adm` says which families are types: downward closed with the
world truncated to match, and stable under the world growing.

A reference is built from a *semantic* element type and compares the stored
contract with it at strictly lower budget. Nothing syntactic is involved, so a
type parameter under a reference is interpreted rather than ignored --
`ref_param_universal` -- which is the failure that motivated worlds in the first
place.

Because a reference reads its element type only below the current budget it is a
**guard**, so `refT` is contractive and the guarded fixed point applies: the
tower `⊤, F ⊤, F (F ⊤), …` stabilises below its own height, its diagonal is
coherent, and that diagonal is a fixed point. This is Banach's theorem on a
space where distance is the first budget at which two families disagree, and it
needs no monotonicity -- which is how it survives recursion through negative
positions.

The fixed point is also *unique*: any family satisfying the equation is it. So a
recursive type is determined by its equation rather than merely solving it, and
two spellings of one recursion are the same type.
-/
namespace Verification
namespace ExperimentState

abbrev Fam := (k : Nat) → WorldT k → Val → Prop

/-- Every semantic type restricts to a contract at any level. The contract can
observe only strictly lower levels; higher-level information is unavailable. -/
def res {k : Nat} (T : Fam) : Ctr k := fun j _ W' v => T j W' v

/-- **A record, built from semantic field types.** An object is a finite map
from field names to locations, fixed at allocation; the contract stored at a
named field's location is compared with that field's family, at strictly lower
budget. Taking the field types semantically rather than syntactically is what
makes the clause depend on the environment interpreting it, so a type parameter
under a field is interpreted rather than ignored.

Fields the type does not name are unconstrained, so a record type is open, as
TypeScript's structural types are; every field it does name keeps its exact
contract, which is what makes that openness sound and each field invariant. -/
abbrev Fields := List (String × Fam)

def recT (fs : Fields) : Fam := fun k W v =>
  ∃ flds : List (String × Nat), v = .objAt flds .absent ∧
    ∀ (f : String) (T : Fam), (f, T) ∈ fs →
      ∃ (l : Nat) (c : Ctr k), flds.lookup f = some l ∧ lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u ↔ T j W' u

/-- **A reference**: the record with the single field a cell carries. Every
rule and proof written before fields were named speaks about this one. -/
def refT (T : Fam) : Fam := recT [(valueField, T)]

/-- One named field, as the cell development states it. -/
theorem recT_single {f : String} {A : Fam} {k} {W : WorldT k} {v} :
    recT [(f, A)] k W v ↔ ∃ (flds : List (String × Nat)) (l : Nat) (c : Ctr k),
      v = .objAt flds .absent ∧ flds.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u ↔ A j W' u := by
  constructor
  · rintro ⟨flds, rfl, h⟩
    obtain ⟨l, c, hl, hw, hag⟩ := h f A (by simp)
    exact ⟨flds, l, c, rfl, hl, hw, hag⟩
  · rintro ⟨flds, l, c, rfl, hl, hw, hag⟩
    refine ⟨flds, rfl, ?_⟩
    rintro f' T' hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ⟨l, c, hl, hw, hag⟩

/-- A pair in a zip comes from one position of both lists. -/
theorem mem_zip_index {α β : Type} {as : List α} {bs : List β} {a : α} {b : β}
    (h : (a, b) ∈ as.zip bs) :
    ∃ (i : Nat) (hi : i < as.length) (hj : i < bs.length), as[i] = a ∧ bs[i] = b := by
  induction as generalizing bs with
  | nil => simp at h
  | cons x as ih =>
    cases bs with
    | nil => simp at h
    | cons y bs =>
      rw [List.zip_cons_cons] at h
      rcases List.mem_cons.mp h with he | h'
      · cases he
        exact ⟨0, by simp, by simp, rfl, rfl⟩
      · obtain ⟨i, hi, hj, h1, h2⟩ := ih h'
        exact ⟨i + 1, by simpa using hi, by simpa using hj, h1, h2⟩

/-- **The record a fresh allocation satisfies.** Each named field stands for the
location its position was given, under the contract stated for it there. -/
theorem recT_alloc {n : Nat} {W : WorldT n} {ns : List String} {As : List Fam} {base : Nat}
    (hnd : ns.Nodup) (hlen : ns.length = As.length)
    (hl : ∀ (i : Nat) (hi : i < ns.length),
      lookup W (base + i) = some (res (As[i]'(hlen ▸ hi)))) :
    recT (ns.zip As) n W (.objAt (slots base ns) .absent) := by
  refine ⟨slots base ns, rfl, ?_⟩
  intro f T hm
  obtain ⟨i, hi, hj, rfl, rfl⟩ := mem_zip_index hm
  exact ⟨base + i, res (As[i]'hj), lookup_slots hnd hi, hl i hi, fun _ _ _ _ => Iff.rfl⟩

/-- What a record type says about one of its fields. -/
theorem recT_at {fs : List (String × Fam)} {f : String} {A : Fam} (hm : (f, A) ∈ fs)
    {k} {W : WorldT k} {v} (h : recT fs k W v) :
    ∃ (flds : List (String × Nat)) (l : Nat) (c : Ctr k),
      v = .objAt flds .absent ∧ flds.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u ↔ A j W' u := by
  obtain ⟨flds, rfl, hfs⟩ := h
  obtain ⟨l, c, hl, hw, hag⟩ := hfs f A hm
  exact ⟨flds, l, c, rfl, hl, hw, hag⟩

theorem refT_iff {A : Fam} {k} {W : WorldT k} {v} :
    refT A k W v ↔ ∃ (flds : List (String × Nat)) (l : Nat) (c : Ctr k),
      v = .objAt flds .absent ∧ flds.lookup valueField = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u ↔ A j W' u :=
  recT_single

/-- Building the cell at a known location, as the earlier development did. -/
theorem refT_cell {A : Fam} {k} {W : WorldT k} {l : Nat} {c : Ctr k}
    (hl : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u ↔ A j W' u) :
    refT A k W (.obj l .absent) :=
  refT_iff.mpr ⟨_, l, c, rfl, lookup_value l, hl, hag⟩

def nulT : Fam := fun _ _ v => v = .nul

/-- The value a function body produces by completing rather than returning. -/
def undefT : Fam := fun _ _ v => v = .undef

/-- A cell that can actually change observably. -/
def boolT : Fam := fun _ _ v => v = .tru ∨ v = .fls

/-- Every number, at any spelling: the union of its singletons and nothing
more, and what arithmetic yields. -/
def numT : Fam := fun _ _ v => ∃ b, v = .num b

/-- Every string. As with numbers, the family is the union of its singletons. -/
def strT : Fam := fun _ _ v => ∃ s, v = .str s

/-! ### A rigid parameter under a reference -/


theorem ref_param_inhabited (F : Fam) (k : Nat) :
    refT F k (ofList [res F]) (.obj 0 .absent) :=
  refT_cell (c := res F) (by simp [lookup]) (fun _ _ _ _ => Iff.rfl)

theorem ref_param_universal :
    ∀ (F : Fam) (k : Nat), ∃ (W : WorldT k) (v : Val), refT F k W v :=
  fun F k => ⟨ofList [res F], .obj 0 .absent, ref_param_inhabited F k⟩

/-! ## The guarded fixed point -/


def topF : Fam := fun _ _ _ => True

/-- Inclusion of families, at every budget and world. -/
def FamLe (A B : Fam) : Prop := ∀ (n : Nat) (W : WorldT n) (v : Val), A n W v → B n W v

def Agree (T U : Fam) (n : Nat) : Prop := ∀ m, m < n → ∀ W v, T m W v ↔ U m W v

def Contractive (F : Fam → Fam) : Prop :=
  ∀ n T U, Agree T U n → ∀ W v, F T n W v ↔ F U n W v

def iter (F : Fam → Fam) : Nat → Fam
  | 0 => topF
  | k + 1 => F (iter F k)

def fixF (F : Fam → Fam) : Fam := fun n => iter F (n + 1) n

private theorem natStrong {G : Nat → Prop} (h : ∀ n, (∀ m, m < n → G m) → G n) :
    ∀ n, G n := by
  have aux : ∀ n, ∀ m, m < n → G m := by
    intro n
    induction n with
    | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
    | succ k ih =>
      intro m hm
      by_cases hk : m = k
      · subst hk; exact h m ih
      · exact ih m (by omega)
  exact fun n => h n (aux n)

theorem iter_stable (F : Fam → Fam) (hF : Contractive F) :
    ∀ m k j, m < k → m < j → ∀ W v, iter F k m W v ↔ iter F j m W v := by
  refine natStrong ?_
  intro m ih k j hk hj W v
  cases k with
  | zero => omega
  | succ k' =>
    cases j with
    | zero => omega
    | succ j' =>
      show F (iter F k') m W v ↔ F (iter F j') m W v
      exact hF m _ _ (fun m' hm' W' v' => ih m' hm' k' j' (by omega) (by omega) W' v') W v

theorem fix_unfold (F : Fam → Fam) (hF : Contractive F) (n : Nat) (W : WorldT n) (v : Val) :
    fixF F n W v ↔ F (fixF F) n W v := by
  show F (iter F n) n W v ↔ F (fixF F) n W v
  exact hF n _ _ (fun m hm W' v' => iter_stable F hF m n (m + 1) hm (by omega) W' v') W v

/-- A reference reads its element type only strictly below the current level,
so it is a guard. -/
theorem refT_contractive : Contractive refT := by
  intro n T U hag W v
  simp only [refT_iff]
  constructor <;> rintro ⟨flds, l, c, rfl, hf, hl, h⟩ <;>
      refine ⟨flds, l, c, rfl, hf, hl, ?_⟩ <;> intro j hj W' u
  · exact (h j hj W' u).trans (hag j hj W' u)
  · exact (h j hj W' u).trans (hag j hj W' u).symm

/-- **The fixed point is unique.** Any family satisfying the equation *is* it,
so a recursive type is determined by its equation and not merely a solution of
it. -/
theorem fix_unique (F : Fam → Fam) (hF : Contractive F) (U : Fam)
    (hU : ∀ (n : Nat) (W : WorldT n) (v : Val), U n W v ↔ F U n W v) :
    ∀ (n : Nat) (W : WorldT n) (v : Val), U n W v ↔ fixF F n W v := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro W v
    rw [hU n W v, fix_unfold F hF n W v]
    exact hF n U (fixF F) (fun m hm W' v' => ih m hm W' v') W v

/-! ## `R = ref R` -/


def R : Fam := fixF refT

theorem R_unfold (n : Nat) (W : WorldT n) (v : Val) : R n W v ↔ refT R n W v :=
  fix_unfold refT refT_contractive n W v

/-- Inhabited by a genuinely cyclic world: one location whose contract is `R`
itself, holding a reference to that same location. -/
theorem R_cyclic (n : Nat) : R n (ofList [res R]) (.obj 0 .absent) :=
  (R_unfold n _ _).mpr (refT_cell (c := res R) (by simp [lookup]) (fun _ _ _ _ => Iff.rfl))

/-- And `R` is not everything: a non-location is excluded at every level. -/
theorem R_not_trivial (n : Nat) (W : WorldT n) : ¬ R n W .nul := by
  intro h
  obtain ⟨flds, l, c, hv, -, -, -⟩ := refT_iff.mp ((R_unfold n W _).mp h)
  exact absurd hv (by simp)

/-- A reference respects equality of its element type. -/
theorem refT_congr {A B : Fam} (h : ∀ (n : Nat) (W : WorldT n) (v : Val), A n W v ↔ B n W v) :
    ∀ (n : Nat) (W : WorldT n) (v : Val), refT A n W v ↔ refT B n W v :=
  fun n => refT_contractive n A B (fun m _ W v => h m W v)

theorem refT_refT_contractive : Contractive (fun X => refT (refT X)) := by
  intro n T U hag W v
  exact refT_contractive n (refT T) (refT U)
    (fun m hm => refT_contractive m T U (fun m' hm' => hag m' (by omega))) W v

/-- **`μX. ref X` and `μX. ref (ref X)` are the same type**: an instance of
uniqueness, and the smallest case where two spellings of one recursive type
must be identified. -/
theorem R_eq_ref_ref :
    ∀ (n : Nat) (W : WorldT n) (v : Val), R n W v ↔ fixF (fun X => refT (refT X)) n W v := by
  refine fix_unique _ refT_refT_contractive R ?_
  intro n W v
  exact (R_unfold n W v).trans
    (refT_contractive n R (refT R) (fun m _ W' v' => R_unfold m W' v') W v)

/-- Allocation cannot invalidate a reference claim: a future world keeps every
contract it already had. -/
theorem recT_mono (fs : List (String × Fam)) (k : Nat) (W W' : WorldT k) (h : WExt W W')
    (v : Val) (hv : recT fs k W v) : recT fs k W' v := by
  obtain ⟨flds, rfl, hfs⟩ := hv
  refine ⟨flds, rfl, ?_⟩
  intro f T hm
  obtain ⟨l, c, hf, hl, hag⟩ := hfs f T hm
  exact ⟨l, c, hf, WExt_lookup h hl, hag⟩

theorem refT_mono (T : Fam) (k : Nat) (W W' : WorldT k) (h : WExt W W') (v : Val)
    (hv : refT T k W v) : refT T k W' v :=
  recT_mono _ k W W' h v hv

/-! ## Admissibility -/


structure Adm (T : Fam) : Prop where
  down : ∀ (n : Nat) (W : WorldT (n + 1)) (v : Val),
    T (n + 1) W v → T n (trunc n (Nat.le_succ n) W) v
  mono : ∀ (n : Nat) (W W' : WorldT n), WExt W W' → ∀ v, T n W v → T n W' v

theorem nulT_adm : Adm nulT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
theorem undefT_adm : Adm undefT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem boolT_adm : Adm boolT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem numT_adm : Adm numT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem strT_adm : Adm strT := ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem topF_adm : Adm topF := ⟨fun _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩

/-- A reference is admissible whatever its element type is: the level drop is
absorbed by restricting the stored contract, and allocation only appends. -/
theorem recT_adm (fs : List (String × Fam)) : Adm (recT fs) := by
  refine ⟨?_, fun n W W' hx v hv => recT_mono fs n W W' hx v hv⟩
  rintro n W v ⟨flds, rfl, hfs⟩
  refine ⟨flds, rfl, ?_⟩
  intro f T hm
  obtain ⟨l, c, hf, hl, hag⟩ := hfs f T hm
  refine ⟨l, _, hf, lookup_trunc (Nat.le_succ n) W l c hl, ?_⟩
  intro j hj W' u
  exact hag j (by omega) W' u

theorem refT_adm (T : Fam) : Adm (refT T) := recT_adm _

/-- **A read capability** on named fields. Each names a location whose stored
contract implies the stated family, so a read observes that family; nothing
here permits a write, and the backing invariant, which may be stronger, is
never retyped. A readonly view of a mutable cell is such a capability. -/
def viewT (fs : Fields) : Fam := fun k W v =>
  ∀ (f : String) (T : Fam), (f, T) ∈ fs →
    ∃ (flds : List (String × Nat)) (l : Nat) (c : Ctr k), v = .objAt flds .absent ∧
      flds.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → T j W' u

/-- A readonly string index signature constrains every *present* own field.
The map of locations is finite, while the signature ranges over all strings.
An absent key has no location and is read as `undefined` by `Step.readMissing`.
This is a read capability: the actual cell contract may be stricter than `A`.
The plain-object restriction is the same one used by `recT` and `viewT`. -/
def dictViewT (A : Fam) : Fam := fun k W v =>
  ∃ flds : List (String × Nat), v = .objAt flds .absent ∧
    ∀ (f : String) (l : Nat), flds.lookup f = some l →
      ∃ c : Ctr k, lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → A j W' u

/-- A dictionary's read guarantee is guarded by the world level, including
when its element type is a recursive graph label. -/
theorem dictViewT_congr {A B : Fam} {k : Nat} (h : Agree A B k)
    (W : WorldT k) (v : Val) : dictViewT A k W v ↔ dictViewT B k W v := by
  constructor <;> rintro ⟨flds, rfl, hf⟩ <;> refine ⟨flds, rfl, ?_⟩
  · intro f l hl
    obtain ⟨c, hc, hA⟩ := hf f l hl
    exact ⟨c, hc, fun j hj W' u hu => (h j hj W' u).mp (hA j hj W' u hu)⟩
  · intro f l hl
    obtain ⟨c, hc, hB⟩ := hf f l hl
    exact ⟨c, hc, fun j hj W' u hu => (h j hj W' u).mpr (hB j hj W' u hu)⟩

/-- A dictionary view supplies a contract for a key only when that key is
present. Looking up an arbitrary string cannot use this witness alone. -/
theorem dictViewT_present {A : Fam} {k : Nat} {W : WorldT k}
    {fs : List (String × Nat)} (hd : dictViewT A k W (.objAt fs .absent))
    {f : String} {l : Nat} (hl : fs.lookup f = some l) :
    ∃ c : Ctr k, lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → A j W' u := by
  obtain ⟨fs', heq, hf⟩ := hd
  cases heq
  exact hf f l hl

/-- Even a Boolean dictionary admits an empty object. Its missing read is
`undefined`, which is not Boolean; the indexed-read result must include it. -/
theorem empty_bool_dict_missing {k : Nat} {W : WorldT k} {h : Heap} {f : String} :
    dictViewT boolT k W (.objAt [] .absent) ∧
    Step h (.readAt f (.objAt [] .absent)) h .undef ∧
    ¬ boolT k W .undef := by
  refine ⟨⟨[], rfl, ?_⟩, .readMissing (by simp), ?_⟩
  · intro f' l hl; simp at hl
  · simp [boolT]

theorem viewT_at {fs : Fields} {f : String} {A : Fam} (hm : (f, A) ∈ fs)
    {k} {W : WorldT k} {v} (h : viewT fs k W v) :
    ∃ (flds : List (String × Nat)) (l : Nat) (c : Ctr k),
      v = .objAt flds .absent ∧ flds.lookup f = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → A j W' u := h f A hm

theorem viewT_append (A B : Fields) (k : Nat) (W : WorldT k) (v : Val) :
    viewT (A ++ B) k W v ↔ viewT A k W v ∧ viewT B k W v := by
  simp only [viewT, List.mem_append, or_imp, forall_and]

/-- A readable slot provides an upper bound. A writable slot additionally
accepts every member of that bound, without changing the backing invariant. -/
def SlotContract (readonly : Bool) (P Q : Prop) : Prop :=
  (P → Q) ∧ (readonly = false → Q → P)

theorem SlotContract.refl (r : Bool) (P : Prop) : SlotContract r P P :=
  ⟨id, fun _ => id⟩

theorem SlotContract.congr {r : Bool} {P Q R : Prop}
    (h : SlotContract r P Q) (e : Q ↔ R) : SlotContract r P R :=
  ⟨fun p => e.mp (h.1 p), fun hr r => h.2 hr (e.mpr r)⟩

theorem SlotContract.weaken {r s : Bool} {P Q R : Prop}
    (h : SlotContract r P Q) (mode : s = false → r = false)
    (read : Q → R) (write : s = false → R → Q) : SlotContract s P R :=
  ⟨fun p => read (h.1 p), fun hs r => h.2 (mode hs) (write hs r)⟩

/-- A tuple contract on an array store: the required positions' families, the
optional positions', and what any further position must hold, if any may. -/
structure TupleF where
  required : List Fam
  optional : List Fam
  rest : Option Fam
  readonly : Bool := false

/-- **A store under a tuple contract.** Every required position has a location
under its family (or implying it for a readonly contract); an optional
position is a hole or a location under the same capability; a further position exists only under a rest family, and holds a
location under it. Lengths follow: at least the required positions, and no
more than the optional ones without a rest. -/
def listT (T : TupleF) : Fam := fun k W v =>
  ∃ ls : List (Option Nat), v = .arr ls ∧ T.required.length ≤ ls.length ∧
    (T.rest = none → ls.length ≤ T.required.length + T.optional.length) ∧
    (∀ (i : Nat) (A : Fam), T.required[i]? = some A → ∃ (l : Nat) (c : Ctr k),
      ls[i]? = some (some l) ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), SlotContract T.readonly (c j hj W' u) (A j W' u)) ∧
    (∀ (i : Nat) (A : Fam) (l : Nat), T.optional[i]? = some A →
      ls[T.required.length + i]? = some (some l) → ∃ c : Ctr k, lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), SlotContract T.readonly (c j hj W' u) (A j W' u)) ∧
    (∀ (i l : Nat), T.required.length + T.optional.length ≤ i → ls[i]? = some (some l) →
      ∃ (E : Fam) (c : Ctr k), T.rest = some E ∧ lookup W l = some c ∧
        ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), SlotContract T.readonly (c j hj W' u) (E j W' u))

theorem listT_adm (T : TupleF) : Adm (listT T) := by
  refine ⟨?_, ?_⟩
  · rintro n W v ⟨ls, rfl, hlen, hbound, hreq, hopt, hrest⟩
    refine ⟨ls, rfl, hlen, hbound, ?_, ?_, ?_⟩
    · intro i A hA
      obtain ⟨l, c, hl, hw, hag⟩ := hreq i A hA
      exact ⟨l, _, hl, lookup_trunc (Nat.le_succ n) W l c hw, fun j hj W' u => hag j (by omega) W' u⟩
    · intro i A l hA hl
      obtain ⟨c, hw, hag⟩ := hopt i A l hA hl
      exact ⟨_, lookup_trunc (Nat.le_succ n) W l c hw, fun j hj W' u => hag j (by omega) W' u⟩
    · intro i l hi hl
      obtain ⟨E, c, hE, hw, hag⟩ := hrest i l hi hl
      exact ⟨E, _, hE, lookup_trunc (Nat.le_succ n) W l c hw, fun j hj W' u => hag j (by omega) W' u⟩
  · rintro n W W' hx v ⟨ls, rfl, hlen, hbound, hreq, hopt, hrest⟩
    refine ⟨ls, rfl, hlen, hbound, ?_, ?_, ?_⟩
    · intro i A hA
      obtain ⟨l, c, hl, hw, hag⟩ := hreq i A hA
      exact ⟨l, c, hl, WExt_lookup hx hw, hag⟩
    · intro i A l hA hl
      obtain ⟨c, hw, hag⟩ := hopt i A l hA hl
      exact ⟨c, WExt_lookup hx hw, hag⟩
    · intro i l hi hl
      obtain ⟨E, c, hE, hw, hag⟩ := hrest i l hi hl
      exact ⟨E, c, hE, WExt_lookup hx hw, hag⟩

/-- The family a tuple contract states for an index: a required position's,
an optional position's, or the rest's where any further position may be. -/
def positionFam (T : TupleF) (i : Nat) : Option Fam :=
  match T.required[i]? with
  | some A => some A
  | none => match T.optional[i - T.required.length]? with
    | some A => some A
    | none => if T.required.length + T.optional.length ≤ i then T.rest else none

theorem elemSlots_getElem? (base n i : Nat) :
    (elemSlots base n)[i]? = if i < n then some (some (base + i)) else none := by
  simp only [elemSlots, List.getElem?_map]
  by_cases hi : i < n
  · rw [List.getElem?_eq_getElem (by simpa using hi)]
    simp [hi, List.getElem_range]
  · rw [List.getElem?_eq_none (by simpa using hi)]
    simp [hi]

theorem placeAt_getElem? (ls : List (Option Nat)) (k m i : Nat) :
    (placeAt ls k m)[i]? = if i = k then some (some m)
      else if i < ls.length then ls[i]? else if i < k + 1 then some none else none := by
  unfold placeAt
  have hlen : (ls ++ List.replicate (k + 1 - ls.length) none).length = ls.length + (k + 1 - ls.length) := by
    simp [List.length_append, List.length_replicate]
  by_cases hik : i = k
  · subst hik
    rw [List.getElem?_set_self]
    simp only [hlen, if_true]
    have : i < ls.length + (i + 1 - ls.length) := by omega
    simp [this]
  · rw [List.getElem?_set_ne (Ne.symm hik)]
    simp only [hik, if_false]
    by_cases hi : i < ls.length
    · simp [List.getElem?_append_left hi, hi]
    · simp only [hi, if_false]
      rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
      by_cases hk : i < k + 1
      · simp only [hk, if_true]; simp; omega
      · simp only [hk, if_false]; simp; omega

theorem placeAt_length (ls : List (Option Nat)) (k m : Nat) :
    (placeAt ls k m).length = ls.length + (k + 1 - ls.length) := by
  simp [placeAt, List.length_set, List.length_append, List.length_replicate]

/-- **The store a literal allocates.** Each position's location holds the
contract of its family, in order, so the store meets any tuple contract whose
positions those families are, and whose bounds the count respects. -/
theorem listT_alloc {n : Nat} {W : WorldT n} {T : TupleF} {As : List Fam} {base : Nat}
    (hreq : T.required.length ≤ As.length)
    (hbound : T.rest = none → As.length ≤ T.required.length + T.optional.length)
    (hpos : ∀ i A, As[i]? = some A → positionFam T i = some A)
    (hl : ∀ (i : Nat) (hi : i < As.length), lookup W (base + i) = some (res (As[i]'hi))) :
    listT T n W (.arr (elemSlots base As.length)) := by
  have hpos' : ∀ (i : Nat) (hi : i < As.length), positionFam T i = some (As[i]'hi) :=
    fun i hi => hpos i _ (List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩)
  refine ⟨_, rfl, by simp [elemSlots, hreq], fun hn => by simpa [elemSlots] using hbound hn, ?_, ?_, ?_⟩
  · intro i A hA
    have hi : i < As.length := by
      have := (List.getElem?_eq_some_iff.mp hA).1; omega
    refine ⟨base + i, res (As[i]'hi), by simp [elemSlots_getElem?, hi], hl i hi, ?_⟩
    have := hpos' i hi
    simp only [positionFam, hA, Option.some.injEq] at this
    subst this
    exact fun _ _ _ _ => SlotContract.refl _ _
  · intro i A l hA hl'
    rw [elemSlots_getElem?] at hl'
    split at hl'
    · rename_i hlt
      cases Option.some.inj (Option.some.inj hl')
      refine ⟨res (As[T.required.length + i]'hlt), hl _ hlt, ?_⟩
      have := hpos' _ hlt
      have hr : T.required[T.required.length + i]? = none := List.getElem?_eq_none (by omega)
      simp only [positionFam, hr, Nat.add_sub_cancel_left, hA, Option.some.injEq] at this
      subst this
      exact fun _ _ _ _ => SlotContract.refl _ _
    · contradiction
  · intro i l hi hl'
    rw [elemSlots_getElem?] at hl'
    split at hl'
    · rename_i hlt
      cases Option.some.inj (Option.some.inj hl')
      have := hpos' i hlt
      have hr : T.required[i]? = none := List.getElem?_eq_none (by omega)
      have ho : T.optional[i - T.required.length]? = none := List.getElem?_eq_none (by omega)
      simp only [positionFam, hr, ho, hi, if_true] at this
      exact ⟨_, res (As[i]'hlt), this, hl i hlt, fun _ _ _ _ => SlotContract.refl _ _⟩
    · contradiction

/-- **A grown store.** Filling a hole, or a position past the end, with a fresh
location under the position's family keeps the tuple contract: every other
position is as before, and the bounds still hold because the position is one
the contract names. -/
theorem listT_grow {n : Nat} {W : WorldT n} {T : TupleF} {ls : List (Option Nat)} {k m : Nat} {A : Fam}
    (h : listT T n W (.arr ls)) (hpos : positionFam T k = some A)
    (hhole : (ls[k]?).bind id = none) (hm : lookup W m = some (res A)) :
    listT T n W (.arr (placeAt ls k m)) := by
  obtain ⟨ls', he, hlen, hbound, hreq, hopt, hrest⟩ := h
  cases he
  have hnamed : T.rest = none → k < T.required.length + T.optional.length := by
    intro hn
    simp only [positionFam] at hpos
    split at hpos
    · rename_i hk; have := (List.getElem?_eq_some_iff.mp hk).1; omega
    · split at hpos
      · rename_i hk; have := (List.getElem?_eq_some_iff.mp hk).1; omega
      · split at hpos
        · rw [hn] at hpos; cases hpos
        · cases hpos
  refine ⟨_, rfl, by rw [placeAt_length]; omega, fun hn => by rw [placeAt_length]; have := hbound hn; have := hnamed hn; omega, ?_, ?_, ?_⟩
  · intro i A' hA
    obtain ⟨l, c, hl, hw, hag⟩ := hreq i A' hA
    have hik : i ≠ k := by
      rintro rfl
      simp [hl] at hhole
    have hi : i < ls.length := (List.getElem?_eq_some_iff.mp hl).1
    exact ⟨l, c, by rw [placeAt_getElem?]; simp only [hik, hi, if_false, if_true]; exact hl, hw, hag⟩
  · intro i A' l hA hl
    rw [placeAt_getElem?] at hl
    split at hl
    · rename_i hik
      cases Option.some.inj (Option.some.inj hl)
      subst hik
      have hr : T.required[T.required.length + i]? = none := List.getElem?_eq_none (by omega)
      simp only [positionFam, hr, Nat.add_sub_cancel_left, hA, Option.some.injEq] at hpos
      subst hpos
      exact ⟨res A', hm, fun _ _ _ _ => SlotContract.refl _ _⟩
    · split at hl
      · exact hopt i A' l hA hl
      · split at hl <;> cases hl
  · intro i l hi hl
    rw [placeAt_getElem?] at hl
    split at hl
    · rename_i hik
      cases Option.some.inj (Option.some.inj hl)
      subst hik
      have hr : T.required[i]? = none := List.getElem?_eq_none (by omega)
      have ho : T.optional[i - T.required.length]? = none := List.getElem?_eq_none (by omega)
      simp only [positionFam, hr, ho, hi, if_true] at hpos
      exact ⟨A, res A, hpos, hm, fun _ _ _ _ => SlotContract.refl _ _⟩
    · split at hl
      · exact hrest i l hi hl
      · split at hl <;> cases hl

theorem viewT_adm (fs : Fields) : Adm (viewT fs) := by
  refine ⟨?_, ?_⟩
  · intro n W v h f T hm
    obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ := h f T hm
    exact ⟨flds, l, _, rfl, hf, lookup_trunc (Nat.le_succ n) W l c hl,
      fun j hj W' u => hag j (by omega) W' u⟩
  · intro n W W' hx v h f T hm
    obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ := h f T hm
    exact ⟨flds, l, c, rfl, hf, WExt_lookup hx hl, hag⟩

theorem dictViewT_adm (A : Fam) : Adm (dictViewT A) := by
  refine ⟨?_, ?_⟩
  · intro n W v h
    obtain ⟨flds, rfl, hf⟩ := h
    refine ⟨flds, rfl, ?_⟩
    intro f l hl
    obtain ⟨c, hc, hag⟩ := hf f l hl
    exact ⟨_, lookup_trunc (Nat.le_succ n) W l c hc,
      fun j hj W' u hu => hag j (by omega) W' u hu⟩
  · intro n W W' hx v h
    obtain ⟨flds, rfl, hf⟩ := h
    refine ⟨flds, rfl, ?_⟩
    intro f l hl
    obtain ⟨c, hc, hag⟩ := hf f l hl
    exact ⟨c, WExt_lookup hx hc, hag⟩

theorem iter_adm (F : Fam → Fam) (hF : ∀ T, Adm T → Adm (F T)) : ∀ k, Adm (iter F k)
  | 0 => topF_adm
  | k + 1 => hF _ (iter_adm F hF k)

theorem fix_adm (F : Fam → Fam) (hC : Contractive F) (hF : ∀ T, Adm T → Adm (F T)) :
    Adm (fixF F) := by
  constructor
  · intro n W v hv
    have h1 : iter F (n + 2) n (trunc n (Nat.le_succ n) W) v :=
      (iter_adm F hF (n + 2)).down n W v hv
    exact (iter_stable F hC n (n + 2) (n + 1) (by omega) (by omega) _ v).mp h1
  · intro n W W' hx v hv
    exact (iter_adm F hF (n + 1)).mono n W W' hx v hv

theorem R_adm : Adm R := fix_adm refT refT_contractive (fun T _ => refT_adm T)

theorem Adm.down_le {A : Fam} (hA : Adm A) :
    ∀ (n i : Nat) (h : i ≤ n) (W : WorldT n) (v : Val), A n W v → A i (trunc i h W) v := by
  intro n
  induction n with
  | zero =>
    intro i h W v hv
    have hi : i = 0 := by omega
    subst hi; rw [trunc_id]; exact hv
  | succ p ih =>
    intro i h W v hv
    by_cases hip : i = p + 1
    · subst hip; rw [trunc_id]; exact hv
    · have hle : i ≤ p := by omega
      have := ih i hle (trunc p (Nat.le_succ p) W) v (hA.down p W v hv)
      rwa [trunc_trunc] at this

/-! ## Types whose members are values -/


/-- A type whose members are values. Needed wherever a term must beta-reduce or
be stored. -/
def ValOnly (A : Fam) : Prop := ∀ (j : Nat) (W : WorldT j) (a : Val), A j W a → isVal a = true

theorem nulT_valOnly : ValOnly nulT := by rintro _ _ _ rfl; rfl
theorem undefT_valOnly : ValOnly undefT := by rintro _ _ _ rfl; rfl

theorem boolT_valOnly : ValOnly boolT := by rintro _ _ _ (rfl | rfl) <;> rfl

theorem recT_valOnly (fs : List (String × Fam)) : ValOnly (recT fs) := by
  rintro _ _ _ ⟨flds, rfl, -⟩; rfl

theorem refT_valOnly (A : Fam) : ValOnly (refT A) := recT_valOnly _

/-- Restricting a semantic type to a contract is level-independent. -/
theorem trunc_res {k j : Nat} (h : j ≤ k) (T : Fam) :
    trunc j h (ofList [res T]) = ofList [res T] := by
  simp only [trunc, toList_ofList, List.map_cons, List.map_nil]
  rfl

/-! ## Pointwise union and intersection

Union and intersection of families are the set operations at each index.
Both preserve admissibility. They are *not* guards: `F(X) = X ∪ A` is only
non-expansive, so a recursive node `μX. X ∨ null` is excluded the same way
`μX. X` is — flatten unions, recurse only through `ref` / `arr`. -/

def unionT (A B : Fam) : Fam := fun n W v => A n W v ∨ B n W v

def interT (A B : Fam) : Fam := fun n W v => A n W v ∧ B n W v

theorem unionT_comm (A B : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    unionT A B n W v ↔ unionT B A n W v := or_comm

theorem unionT_idemp (A : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    unionT A A n W v ↔ A n W v := ⟨fun h => h.elim id id, Or.inl⟩

theorem unionT_assoc (A B C : Fam) (n : Nat) (W : WorldT n) (v : Val) :
    unionT (unionT A B) C n W v ↔ unionT A (unionT B C) n W v := or_assoc

theorem unionT_adm (A B : Fam) (hA : Adm A) (hB : Adm B) : Adm (unionT A B) := by
  constructor
  · intro n W v hv
    rcases hv with h | h
    · exact Or.inl (hA.down n W v h)
    · exact Or.inr (hB.down n W v h)
  · intro n W W' hx v hv
    rcases hv with h | h
    · exact Or.inl (hA.mono n W W' hx v h)
    · exact Or.inr (hB.mono n W W' hx v h)

theorem interT_adm (A B : Fam) (hA : Adm A) (hB : Adm B) : Adm (interT A B) := by
  constructor
  · intro n W v hv
    exact ⟨hA.down n W v hv.1, hB.down n W v hv.2⟩
  · intro n W W' hx v hv
    exact ⟨hA.mono n W W' hx v hv.1, hB.mono n W W' hx v hv.2⟩

theorem unionT_valOnly (A B : Fam) (hA : ValOnly A) (hB : ValOnly B) :
    ValOnly (unionT A B) := by
  intro j W a ha
  rcases ha with h | h
  · exact hA j W a h
  · exact hB j W a h

end ExperimentState
end Verification
