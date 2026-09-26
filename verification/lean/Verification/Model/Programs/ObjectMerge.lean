import Verification.Model.Programs.CallableObjects
import Verification.Model.Types.PositiveCertificates

/-!
# Allocation from parts

An object literal with spreads, `{ a: e, ...x, b: f }`, is a chain of merges
(`Tm.merge`) from a fresh accumulator: each copies what its source owns now
onto a fresh object (`mergeParts`). This module states what a merge's result
is known to hold, clause by clause, from what its two operands' types say
(`MergeClause`), and proves it (`merge_values_safe`).

The facts are about keys. For the source (`b`), a key is *never* copied when
it is dropped or reserved, or when a key bound excludes it and, if it could be
an array index, excludes the array store too; it is *surely* copied at a type
when the source's type names it as a field or view; and whatever is copied
under it is *within* a type when, besides, its optional field or index says so
and it cannot come from an array's store. The accumulator (`a`) is read the
same way, all its keys but the store's copied. A result field is surely there
at its type: the source's, or the accumulator's where whatever the source
copies over it is within the type. A result's optional field is within its
type on both sides, and the result then has no prototype. A result's key
bound admits every key either side may give.
-/
namespace Verification.Model.ObjectMerge
open PositiveNormalization PositiveGraphs PositiveRules Tower

variable {ι : Type}

/-! ### Lookups through the copy -/

theorem lookup_append {β : Type} (xs ys : List (PropKey × β)) (k : PropKey) :
    (xs ++ ys).lookup k = (xs.lookup k).or (ys.lookup k) := by
  induction xs with
  | nil => simp [List.lookup]
  | cons p xs ih =>
    obtain ⟨g, x⟩ := p
    by_cases hk : k = g
    · subst hk; simp [List.lookup]
    · have : (k == g) = false := by simpa using hk
      simp [List.lookup, this, ih]

theorem lookup_filter_key {β : Type} (p : PropKey → Bool) (fs : List (PropKey × β)) (k : PropKey) :
    (fs.filter (fun q => p q.1)).lookup k = if p k then fs.lookup k else none := by
  induction fs with
  | nil => simp [List.lookup]
  | cons q fs ih =>
    obtain ⟨g, x⟩ := q
    by_cases hk : k = g
    · subst hk
      by_cases hp : p k <;> simp [List.filter_cons, hp, List.lookup, ih]
    · have : (k == g) = false := by simpa using hk
      by_cases hp : p g <;> simp [List.filter_cons, hp, List.lookup, this, ih]

theorem lookup_map_snd {β γ : Type} (f : β → γ) (fs : List (PropKey × β)) (k : PropKey) :
    (fs.map fun q => (q.1, f q.2)).lookup k = (fs.lookup k).map f := by
  induction fs with
  | nil => simp [List.lookup]
  | cons q fs ih =>
    obtain ⟨g, x⟩ := q
    by_cases hk : k = g
    · subst hk; simp [List.lookup]
    · have : (k == g) = false := by simpa using hk
      simp [List.lookup, this, ih]

theorem any_key_iff {β : Type} (b : List (PropKey × β)) (k : PropKey) :
    b.any (·.1 == k) = true ↔ k ∈ b.map Prod.fst := by
  simp only [List.any_eq_true, beq_iff_eq, List.mem_map]

theorem lookup_eq_none {β : Type} : ∀ {b : List (PropKey × β)} {k : PropKey},
    k ∉ b.map Prod.fst → b.lookup k = none
  | [], _, _ => rfl
  | (g, x) :: b, k, h => by
    have hg : k ≠ g := fun he => h (by simp [he])
    have : (k == g) = false := by simpa using hg
    simp only [List.lookup, this]
    exact lookup_eq_none (fun hm => h (by simp [hm]))

theorem lookup_isSome {β : Type} : ∀ {b : List (PropKey × β)} {k : PropKey},
    k ∈ b.map Prod.fst → ∃ v, b.lookup k = some v
  | [], _, h => by simp at h
  | (g, x) :: b, k, h => by
    by_cases hg : k = g
    · subst hg; exact ⟨x, by simp [List.lookup]⟩
    · have : (k == g) = false := by simpa using hg
      simp only [List.lookup, this]
      exact lookup_isSome (by simpa [hg] using h)

/-- What a merged list gives under a key: the source's, else the
accumulator's. -/
theorem lookup_mergeData (a b : List (PropKey × Tm)) (k : PropKey) :
    (mergeData a b).lookup k = (b.lookup k).or (a.lookup k) := by
  unfold mergeData
  rw [lookup_append, lookup_filter_key (fun k => !b.any (·.1 == k))]
  by_cases hk : k ∈ b.map Prod.fst
  · obtain ⟨v, hv⟩ := lookup_isSome hk
    have : b.any (·.1 == k) = true := (any_key_iff b k).mpr hk
    simp [this, hv]
  · have : b.any (·.1 == k) = false := by
      cases h : b.any (·.1 == k)
      · rfl
      · exact absurd ((any_key_iff b k).mp h) hk
    simp [this, lookup_eq_none hk]

theorem mergeData_nodup {a b : List (PropKey × Tm)} (ha : (a.map Prod.fst).Nodup)
    (hb : (b.map Prod.fst).Nodup) : ((mergeData a b).map Prod.fst).Nodup := by
  unfold mergeData
  rw [List.map_append]
  refine List.nodup_append.mpr ⟨ha.sublist (List.Sublist.map _ List.filter_sublist), hb, ?_⟩
  intro x hx y hy hxy
  subst hxy
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  have := (List.mem_filter.mp hp).2
  rw [Bool.not_eq_true', ← Bool.not_eq_true] at this
  exact this ((any_key_iff b p.1).mpr hy)

/-- In a list naming each key once, an entry is what its key looks up. -/
theorem lookup_of_mem {β : Type} : ∀ {ps : List (PropKey × β)}, (ps.map Prod.fst).Nodup →
    ∀ {k : PropKey} {v : β}, (k, v) ∈ ps → ps.lookup k = some v
  | [], _, _, _, h => by simp at h
  | (g, x) :: ps, hnd, k, v, h => by
    rw [List.map_cons] at hnd
    rcases List.mem_cons.mp h with he | hm
    · cases he; simp [List.lookup]
    · have hg : k ≠ g := by
        intro he; subst he
        exact (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨(k, v), hm, rfl⟩)
      have : (k == g) = false := by simpa using hg
      simp only [List.lookup, this]
      exact lookup_of_mem (List.nodup_cons.mp hnd).2 hm

theorem mem_of_lookup {β : Type} : ∀ {ps : List (PropKey × β)} {k : PropKey} {v : β},
    ps.lookup k = some v → (k, v) ∈ ps
  | [], _, _, h => by simp [List.lookup] at h
  | (g, x) :: ps, k, v, h => by
    by_cases hk : k = g
    · subst hk; simp [List.lookup] at h; subst h; exact List.mem_cons_self
    · have : (k == g) = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-! ### What the copy reads from an object -/

/-- A key an array's store gives: its index, spelled in decimal. -/
def indexKey : PropKey → Bool
  | .str s => s.toList.all Char.isDigit
  | .sym _ => false

theorem indexKey_toString (n : Nat) : indexKey (.str (toString n)) = true := by
  simp only [indexKey, List.all_eq_true]
  intro c hc
  rw [Nat.toString_eq_repr, Nat.toList_repr] at hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

/-- A store's copied entries are under index keys. -/
theorem storeData_lookup_none {h : List Tm} {fs : List (PropKey × Nat)} {k : PropKey}
    (hk : indexKey k = false ∨ fs.lookup arrayStoreKey = none) : (storeData h fs).lookup k = none := by
  unfold storeData
  rcases hk with hk | hk
  · split
    · split
      · rename_i ls _
        cases hl : (ls.zipIdx.filterMap fun p => p.1.map fun m => (PropKey.str (toString p.2), heapVal h m)).lookup k with
        | none => rfl
        | some v =>
          exfalso
          obtain ⟨p, -, hp⟩ := List.mem_filterMap.mp (mem_of_lookup hl)
          obtain ⟨m, -, he⟩ := Option.map_eq_some_iff.mp hp
          cases he
          rw [indexKey_toString] at hk
          cases hk
      · rfl
    · rfl
  · rw [hk]; rfl

/-- What the source's copy gives under a key: its own field's value if it has
one the copy takes, else an array element. -/
theorem ownData_lookup {h : List Tm} {fs : List (PropKey × Nat)} {qs : List (PropKey × Tm)}
    (hq : ownData h (.objAt fs .absent) = some qs) (k : PropKey) :
    qs.lookup k = ((if copiedKey k then fs.lookup k else none).map (heapVal h)).or
      ((storeData h fs).lookup k) := by
  simp only [ownData, Option.some.injEq] at hq
  subst hq
  rw [lookup_firstKeys, lookup_append]
  congr 1
  rw [show (fs.filter (copiedKey ·.1)).map (fun p => (p.1, heapVal h p.2))
      = (fs.filter (copiedKey ·.1)).map (fun q => (q.1, heapVal h q.2)) from rfl,
    lookup_map_snd, lookup_filter_key (fun k => copiedKey k)]

theorem ownData_nodup {h : List Tm} {v : Tm} {qs : List (PropKey × Tm)} (hq : ownData h v = some qs) :
    (qs.map Prod.fst).Nodup := by
  unfold ownData at hq
  split at hq
  · cases hq; exact firstKeys_nodup _
  all_goals (cases hq <;> simp)

theorem ownAll_lookup {h : List Tm} {fs : List (PropKey × Nat)} {ps : List (PropKey × Tm)}
    (hp : ownAll h (.objAt fs .absent) = some ps) (k : PropKey) :
    ps.lookup k = (if k != arrayStoreKey then fs.lookup k else none).map (heapVal h) := by
  simp only [ownAll, Option.some.injEq] at hp
  subst hp
  rw [lookup_firstKeys, lookup_map_snd, lookup_filter_key (fun k => k != arrayStoreKey)]

theorem ownAll_nodup {h : List Tm} {v : Tm} {ps : List (PropKey × Tm)} (hp : ownAll h v = some ps) :
    (ps.map Prod.fst).Nodup := by
  unfold ownAll at hp
  split at hp
  · cases hp; exact firstKeys_nodup _
  · cases hp


/-! ### What a clause says of a merge's operand -/

variable [DecidableEq ι]

/-- `A`'s labels are among `T`'s, so every value of `A` is one of `T`. -/
def inLabels (A T : List ι) : Bool := A.all (· ∈ T)

theorem inLabels_sound {G : NormalGraph ι} {A T : List ι} (h : inLabels A T = true)
    {n : Nat} {W : WorldT n} {v : Val} (hv : meaning G A n W v) : meaning G T n W v := by
  obtain ⟨i, hi, hv⟩ := hv
  exact ⟨i, List.all_eq_true.mp h i hi |> of_decide_eq_true, hv⟩

theorem meaning_isVal {G : NormalGraph ι} {A : List ι} {n : Nat} {W : WorldT n} {v : Val}
    (h : meaning G A n W v) : isVal v = true := by
  obtain ⟨_, _, h⟩ := h
  exact (normalDenote_value h).1

/-- Some bound excludes the key: no object under the bounds owns it. -/
def excludes (ks : List KeyBound) (k : PropKey) : Bool := ks.any fun K => !K.admits k

theorem excludes_lookup {ks : List KeyBound} {k : PropKey} (h : excludes ks k = true)
    {n : Nat} {W : WorldT n} {fs : List (PropKey × Nat)}
    (hb : ∀ K ∈ ks, ownKeysT K n W (.objAt fs .absent)) : fs.lookup k = none := by
  obtain ⟨K, hK, hn⟩ := List.any_eq_true.mp h
  exact ownKeysT_lookup (hb K hK) (by simpa using hn)

/-- A string key, which an index signature speaks of. -/
def strKey : PropKey → Bool
  | .str _ => true
  | .sym _ => false

/-- The part of a plain-object clause a merge reads: its fields and views,
its optional fields, its index types and its key bounds. -/
structure Obj (ι : Type) where
  named : List (PropKey × List ι)
  optional : List (OptionalField (List ι))
  indexes : List (IndexKeys × List ι)
  bounds : List KeyBound

def objOf : Clause (List ι) → Option (Obj ι)
  | .refs a bs vs os _ ks => some ⟨(a :: bs).flatten ++ vs, os, [], ks⟩
  | .dict a bs vs ds os _ ks _ => some ⟨(a :: bs).flatten ++ vs, os, ds, ks⟩
  | _ => none

/-- A clause whose values own no enumerable property: `null`, `undefined`,
Booleans, numbers, bigints and symbols. A spread of one copies nothing. -/
def emptyClause : Clause (List ι) → Bool
  | .nul | .undef | .bool | .boolLit _ | .num | .numLit _ | .bigint | .bigintLit _ | .symbol => true
  | _ => false

/-- What the semantics of a plain-object clause gives a merge. -/
structure ObjFacts (G : NormalGraph ι) (o : Obj ι) (n : Nat) (W : WorldT n)
    (fs : List (PropKey × Nat)) : Prop where
  named : ∀ p ∈ o.named, ∃ (l : Nat) (c : Ctr n), fs.lookup p.1 = some l ∧ lookup W l = some c ∧
    ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → meaning G p.2 j U u
  optional : ∀ q ∈ o.optional, ∀ l, fs.lookup q.key = some l → ∃ c : Ctr n, lookup W l = some c ∧
    ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → meaning G q.type j U u
  indexes : ∀ x ∈ o.indexes, ∀ (f : PropKey) l, x.1.Admits f → fs.lookup f = some l → ∃ c : Ctr n,
    lookup W l = some c ∧ ∀ (j : Nat) (hj : j < n) (U : WorldT j) (u : Val), c j hj U u → meaning G x.2 j U u
  bounds : ∀ K ∈ o.bounds, ownKeysT K n W (.objAt fs .absent)

theorem objFacts_of_sem {G : NormalGraph ι} {c : Clause (List ι)} {o : Obj ι} (ho : objOf c = some o)
    {n : Nat} {W : WorldT n} {v : Val} (hv : clauseSem G c n W v) :
    ∃ fs, v = .objAt fs .absent ∧ ObjFacts G o n W fs := by
  unfold objOf at ho
  split at ho
  · rename_i a bs vs os ms ks
    cases ho
    obtain ⟨hr, hw, hopt, -, hb⟩ := hv
    obtain ⟨fs, rfl, -⟩ := hr.1
    refine ⟨fs, rfl, ⟨fun p hp => ?_, fun q hq l hl => ?_, fun x hx => by simp at hx, hb⟩⟩
    · obtain ⟨fs', l, c, he, hl, hc, hag⟩ := fields_at (η := G.env) hr hw p hp
      cases he
      exact ⟨l, c, hl, hc, hag⟩
    · obtain ⟨fs', he, -, hall⟩ := hopt
      cases he
      obtain ⟨c, hc, hag⟩ := hall _ (List.mem_map_of_mem hq) l hl
      exact ⟨c, hc, fun j hj U u hu => (hag j hj U u).1 hu⟩
  · rename_i a bs vs ds os ms ks cs
    cases ho
    obtain ⟨hr, hw, ⟨hd, -⟩, hopt, -, hb⟩ := hv
    obtain ⟨fs, rfl, -⟩ := hr.1
    refine ⟨fs, rfl, ⟨fun p hp => ?_, fun q hq l hl => ?_, fun x hx f l hk hl => ?_, hb⟩⟩
    · obtain ⟨fs', l, c, he, hl, hc, hag⟩ := fields_at (η := G.env) hr hw p hp
      cases he
      exact ⟨l, c, hl, hc, hag⟩
    · obtain ⟨fs', he, -, hall⟩ := hopt
      cases he
      obtain ⟨c, hc, hag⟩ := hall _ (List.mem_map_of_mem hq) l hl
      exact ⟨c, hc, fun j hj U u hu => (hag j hj U u).1 hu⟩
    · exact dictViewT_present (hd x hx) hk hl
  · cases ho

theorem emptyClause_ownData {G : NormalGraph ι} {c : Clause (List ι)} (he : emptyClause c = true)
    {n : Nat} {W : WorldT n} {v : Val} (hv : clauseSem G c n W v) (h : List Tm) :
    ownData h v = some [] ∧ isVal v = true := by
  cases c <;> simp [emptyClause] at he <;> simp only [clauseSem, semWithArgs] at hv
  · subst hv; exact ⟨rfl, rfl⟩
  · rcases hv with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · rename_i b; subst hv; cases b <;> exact ⟨rfl, rfl⟩
  · obtain ⟨_, rfl⟩ := hv; exact ⟨rfl, rfl⟩
  · subst hv; exact ⟨rfl, rfl⟩
  · subst hv; exact ⟨rfl, rfl⟩
  · obtain ⟨_, rfl⟩ := hv; exact ⟨rfl, rfl⟩
  · obtain ⟨_, rfl⟩ := hv; exact ⟨rfl, rfl⟩
  · subst hv; exact ⟨rfl, rfl⟩


/-- The source side of a merge: values owning no enumerable property, or a
plain object. -/
inductive Src (ι : Type) where
  | prim
  | obj (o : Obj ι)

def srcOf (c : Clause (List ι)) : Option (Src ι) :=
  if emptyClause c then some .prim else (objOf c).map .obj

/-- The source never gives the key: it is dropped or reserved, or a bound
excludes it and, if an array could give it as an index, the store too. -/
def Src.never : Src ι → List PropKey → PropKey → Bool
  | .prim, _, _ => true
  | .obj o, d, k => d.contains k || !copiedKey k ||
      (excludes o.bounds k && (!indexKey k || excludes o.bounds arrayStoreKey))

/-- The source surely gives the key, at a value within `T`: its type names it. -/
def Src.sure : Src ι → List PropKey → PropKey → List ι → Bool
  | .prim, _, _, _ => false
  | .obj o, d, k, T => !d.contains k && copiedKey k && o.named.any fun p => p.1 == k && inLabels p.2 T

/-- Whatever the source gives under the key is within `T`. -/
def Src.within : Src ι → List PropKey → PropKey → List ι → Bool
  | .prim, _, _, _ => true
  | .obj o, d, k, T => (Src.obj o).never d k || (Src.obj o).sure d k T ||
      ((o.optional.any fun q => q.key == k && inLabels q.type T) ||
        (o.indexes.any fun x => x.1.surely k && inLabels x.2 T)) &&
        (!indexKey k || excludes o.bounds arrayStoreKey)

/-- The accumulator never gives the key: it is the store's, or excluded. -/
def Obj.neverA (o : Obj ι) (k : PropKey) : Bool := k == arrayStoreKey || excludes o.bounds k

def Obj.sureA (o : Obj ι) (k : PropKey) (T : List ι) : Bool :=
  k != arrayStoreKey && o.named.any fun p => p.1 == k && inLabels p.2 T

def Obj.withinA (o : Obj ι) (k : PropKey) (T : List ι) : Bool :=
  o.neverA k || o.sureA k T ||
    (k != arrayStoreKey && ((o.optional.any fun q => q.key == k && inLabels q.type T) ||
      (o.indexes.any fun x => x.1.surely k && inLabels x.2 T)))

/-! ### The copied values are the types say -/

/-- A location's value, at the level below, meets what its contract implies. -/
theorem heap_contract {G : NormalGraph ι} {p : Nat} {W : WorldT (p + 1)} {h : Heap}
    (hok : HeapOk (p + 1) W h) {l : Nat} {c : Ctr (p + 1)} {A : List ι} (hc : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < p + 1) (U : WorldT j) (u : Val), c j hj U u → meaning G A j U u) :
    meaning G A p (trunc p (Nat.le_succ p) W) (heapVal h l) := by
  obtain ⟨v, hv, hmem⟩ := hok.2 l c hc
  have hA := hag p (Nat.lt_succ_self p) _ v (hmem p (Nat.lt_succ_self p))
  have : heapVal h l = v := by simp [heapVal, hv, meaning_isVal hA]
  rw [this]; exact hA

theorem heap_contract_within {G : NormalGraph ι} {p : Nat} {W : WorldT (p + 1)} {h : Heap}
    (hok : HeapOk (p + 1) W h) {l : Nat} {c : Ctr (p + 1)} {A T : List ι} (hc : lookup W l = some c)
    (hag : ∀ (j : Nat) (hj : j < p + 1) (U : WorldT j) (u : Val), c j hj U u → meaning G A j U u)
    (hw : inLabels A T = true) :
    meaning G T p (trunc p (Nat.le_succ p) W) (heapVal h l) :=
  inLabels_sound hw (heap_contract hok hc hag)

/-- The source's copy under a key, less the dropped keys. -/
theorem srcData_lookup {h : List Tm} {fs : List (PropKey × Nat)} {qs : List (PropKey × Tm)}
    (hq : ownData h (.objAt fs .absent) = some qs) (d : List PropKey) (k : PropKey) :
    (qs.filter fun e => !d.contains e.1).lookup k =
      if d.contains k then none else
        ((if copiedKey k then fs.lookup k else none).map (heapVal h)).or ((storeData h fs).lookup k) := by
  rw [lookup_filter_key (fun k => !d.contains k), ownData_lookup hq]
  by_cases hd : d.contains k <;> simp [hd]

theorem any_named {o : List (PropKey × List ι)} {k : PropKey} {T : List ι}
    (h : (o.any fun p => p.1 == k && inLabels p.2 T) = true) :
    ∃ A, (k, A) ∈ o ∧ inLabels A T = true := by
  obtain ⟨⟨g, A⟩, hm, he⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  obtain ⟨rfl, hw⟩ := he
  exact ⟨A, hm, hw⟩

theorem indexKey_of_not_copied {k : PropKey} (h : copiedKey k = false) : indexKey k = false := by
  cases k with
  | sym => rfl
  | str s =>
    simp only [copiedKey, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at h
    rcases h with rfl | rfl <;> decide

theorem src_never {G : NormalGraph ι} {o : Obj ι} {n : Nat} {W : WorldT n} {fs : List (PropKey × Nat)}
    (hf : ObjFacts G o n W fs) {h : List Tm} {qs : List (PropKey × Tm)}
    (hq : ownData h (.objAt fs .absent) = some qs) {d : List PropKey} {k : PropKey}
    (hn : (Src.obj o).never d k = true) : (qs.filter fun e => !d.contains e.1).lookup k = none := by
  rw [srcData_lookup hq]
  simp only [Src.never, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at hn
  by_cases hd : d.contains k = true
  · rw [if_pos hd]
  · rw [if_neg hd]
    rcases hn with (hd' | hc) | ⟨hx, hi⟩
    · exact absurd hd' hd
    · rw [if_neg (by simp [hc]), Option.map_none, Option.none_or]
      exact storeData_lookup_none (.inl (indexKey_of_not_copied hc))
    · have hl := excludes_lookup hx hf.bounds
      rw [show (if copiedKey k = true then fs.lookup k else none) = none by split <;> simp [hl],
        Option.map_none, Option.none_or]
      rcases hi with hi | hs
      · exact storeData_lookup_none (.inl hi)
      · exact storeData_lookup_none (.inr (excludes_lookup hs hf.bounds))

/-- The world a merge's values are read at: one level down. -/
abbrev below {p : Nat} (W : WorldT (p + 1)) : WorldT p := trunc p (Nat.le_succ p) W

theorem src_sure {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {qs : List (PropKey × Tm)} (hq : ownData h (.objAt fs .absent) = some qs) {d : List PropKey}
    {k : PropKey} {T : List ι} (hs : (Src.obj o).sure d k T = true) :
    ∃ v, (qs.filter fun e => !d.contains e.1).lookup k = some v ∧ meaning G T p (below W) v := by
  simp only [Src.sure, Bool.and_eq_true, Bool.not_eq_true'] at hs
  obtain ⟨⟨hd, hc⟩, hn⟩ := hs
  obtain ⟨A, hA, hw⟩ := any_named hn
  obtain ⟨l, c, hl, hcw, hag⟩ := hf.named (k, A) hA
  refine ⟨heapVal h l, ?_, heap_contract_within hok hcw hag hw⟩
  rw [srcData_lookup hq, if_neg (by simpa using hd), if_pos hc, hl]
  rfl

theorem src_within {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {qs : List (PropKey × Tm)} (hq : ownData h (.objAt fs .absent) = some qs) {d : List PropKey}
    {k : PropKey} {T : List ι} (hs : (Src.obj o).within d k T = true) {v : Tm}
    (hv : (qs.filter fun e => !d.contains e.1).lookup k = some v) : meaning G T p (below W) v := by
  simp only [Src.within, Bool.or_eq_true, Bool.and_eq_true] at hs
  rcases hs with (hn | hsure) | ⟨hopt, hidx⟩
  · rw [src_never hf hq hn] at hv; cases hv
  · obtain ⟨v', hv', hm⟩ := src_sure hf hok hq hsure
    rw [hv] at hv'; cases hv'; exact hm
  · rw [srcData_lookup hq] at hv
    by_cases hd : d.contains k = true
    · rw [if_pos hd] at hv; cases hv
    rw [if_neg hd] at hv
    have hstore : (storeData h fs).lookup k = none := by
      simp only [Bool.or_eq_true, Bool.not_eq_true'] at hidx
      rcases hidx with hi | hs
      · exact storeData_lookup_none (.inl hi)
      · exact storeData_lookup_none (.inr (excludes_lookup hs hf.bounds))
    rw [hstore, Option.or_none] at hv
    by_cases hc : copiedKey k = true
    · rw [if_pos hc] at hv
      cases hl : fs.lookup k with
      | none => rw [hl] at hv; cases hv
      | some l =>
        rw [hl] at hv
        cases hv
        rcases hopt with ho | hix
        · obtain ⟨q, hqm, hqe⟩ := List.any_eq_true.mp ho
          simp only [Bool.and_eq_true, beq_iff_eq] at hqe
          obtain ⟨hk, hw⟩ := hqe
          obtain ⟨c, hcw, hag⟩ := hf.optional q hqm l (hk ▸ hl)
          exact heap_contract_within hok hcw hag hw
        · obtain ⟨x, hxm, hxe⟩ := List.any_eq_true.mp hix
          simp only [Bool.and_eq_true] at hxe
          obtain ⟨c, hcw, hag⟩ := hf.indexes x hxm k l (IndexKeys.surely_admits hxe.1) hl
          exact heap_contract_within hok hcw hag hxe.2
    · rw [if_neg hc] at hv; cases hv

/-- What the accumulator's copy gives under a key. -/
theorem acc_never {G : NormalGraph ι} {o : Obj ι} {n : Nat} {W : WorldT n} {fs : List (PropKey × Nat)}
    (hf : ObjFacts G o n W fs) {h : List Tm} {ps : List (PropKey × Tm)}
    (hp : ownAll h (.objAt fs .absent) = some ps) {k : PropKey}
    (hn : o.neverA k = true) : ps.lookup k = none := by
  rw [ownAll_lookup hp]
  simp only [Obj.neverA, Bool.or_eq_true, beq_iff_eq] at hn
  rcases hn with rfl | hx
  · simp
  · simp [excludes_lookup hx hf.bounds]

theorem acc_sure {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {ps : List (PropKey × Tm)} (hp : ownAll h (.objAt fs .absent) = some ps)
    {k : PropKey} {T : List ι} (hs : o.sureA k T = true) :
    ∃ v, ps.lookup k = some v ∧ meaning G T p (below W) v := by
  simp only [Obj.sureA, Bool.and_eq_true] at hs
  obtain ⟨hk, hn⟩ := hs
  obtain ⟨A, hA, hw⟩ := any_named hn
  obtain ⟨l, c, hl, hcw, hag⟩ := hf.named (k, A) hA
  refine ⟨heapVal h l, ?_, heap_contract_within hok hcw hag hw⟩
  rw [ownAll_lookup hp, if_pos hk, hl]
  rfl

theorem acc_within {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {ps : List (PropKey × Tm)} (hp : ownAll h (.objAt fs .absent) = some ps)
    {k : PropKey} {T : List ι} (hs : o.withinA k T = true) {v : Tm}
    (hv : ps.lookup k = some v) : meaning G T p (below W) v := by
  simp only [Obj.withinA, Bool.or_eq_true, Bool.and_eq_true] at hs
  rcases hs with (hn | hsure) | ⟨hk, hopt⟩
  · rw [acc_never hf hp hn] at hv; cases hv
  · obtain ⟨v', hv', hm⟩ := acc_sure hf hok hp hsure
    rw [hv] at hv'; cases hv'; exact hm
  · rw [ownAll_lookup hp, if_pos hk] at hv
    cases hl : fs.lookup k with
    | none => rw [hl] at hv; cases hv
    | some l =>
      rw [hl] at hv
      cases hv
      rcases hopt with ho | hix
      · obtain ⟨q, hqm, hqe⟩ := List.any_eq_true.mp ho
        simp only [Bool.and_eq_true, beq_iff_eq] at hqe
        obtain ⟨hk', hw⟩ := hqe
        obtain ⟨c, hcw, hag⟩ := hf.optional q hqm l (hk' ▸ hl)
        exact heap_contract_within hok hcw hag hw
      · obtain ⟨x, hxm, hxe⟩ := List.any_eq_true.mp hix
        simp only [Bool.and_eq_true] at hxe
        obtain ⟨c, hcw, hag⟩ := hf.indexes x hxm k l (IndexKeys.surely_admits hxe.1) hl
        exact heap_contract_within hok hcw hag hxe.2

/-! ### The rule -/

/-- A result key bound follows from the operands': listing keys, the
accumulator's and the source's own keys are among them (the source owning no
store, so no index); excluding keys, neither side gives one. -/
def boundOk (oa : Obj ι) (sb : Src ι) (d : List PropKey) (K : KeyBound) : Bool :=
  if K.among then
    (oa.bounds.any fun Ka => Ka.among && Ka.keys.all fun x => x == arrayStoreKey || K.admits x) &&
    (match sb with
     | .prim => true
     | .obj ob => ob.bounds.any fun Kb => Kb.among && !Kb.keys.contains arrayStoreKey &&
         Kb.keys.all fun x => !copiedKey x || d.contains x || K.admits x)
  else K.keys.all fun x => oa.neverA x && sb.never d x

/-- **A merge's result, clause by clause.** The accumulator is a plain object
and the source a plain object or a value owning no enumerable property; the
result is a record of fields and optional fields with key bounds. Each field
is surely given within its type: by the source, or by the accumulator where
whatever the source gives is within it too. Each optional field is within its
type on both sides, and then the accumulator gives no prototype, so the
result has none. Each bound admits every key either side may give. -/
def MergeClause (d : List PropKey) (ca cb cr : Clause (List ι)) : Bool :=
  match objOf ca, srcOf cb, cr with
  | some oa, some sb, .refs fs [] [] os [] ks =>
    decide ((fs.map Prod.fst ++ os.map (·.key)).Nodup) &&
    fs.all (fun p => sb.sure d p.1 p.2 || (oa.sureA p.1 p.2 && sb.within d p.1 p.2)) &&
    os.all (fun q => oa.withinA q.key q.type && sb.within d q.key q.type) &&
    (os.isEmpty || oa.neverA CallArguments.protoField) &&
    ks.all (boundOk oa sb d)
  | _, _, _ => false

/-- Every pair of the operands' clauses merges into a clause of the result. -/
def MergeOk (G : NormalGraph ι) (d : List PropKey) (A B R : List ι) : Bool :=
  G.plainTy A && G.plainTy B &&
    (expand G A).all fun ca => (expand G B).all fun cb => (expand G R).any fun cr =>
      MergeClause d ca cb cr

theorem lookup_slots_none {ns : List PropKey} {k : PropKey} (h : k ∉ ns) (base : Nat) :
    (slots base ns).lookup k = none := by
  induction ns generalizing base with
  | nil => rfl
  | cons n ns ih =>
    have hkn : (k == n) = false := by simp only [beq_eq_false_iff_ne]; intro he; exact h (he ▸ List.mem_cons_self)
    simp only [slots, List.lookup, hkn]
    exact ih (fun hm => h (List.mem_cons_of_mem _ hm)) _

theorem mem_of_lookup_slots {ns : List PropKey} {k : PropKey} {base l : Nat}
    (h : (slots base ns).lookup k = some l) : k ∈ ns := by
  by_cases hk : k ∈ ns
  · exact hk
  · rw [lookup_slots_none hk] at h
    cases h

/-- The family a merge's allocation stores under an entry: the result's
field type, or its optional field's, or, for a key the result does not state,
exactly the value copied. -/
def entryFam (G : NormalGraph ι) (fs : List (PropKey × List ι)) (os : List (OptionalField (List ι)))
    (e : PropKey × Tm) : Fam :=
  match fs.lookup e.1 with
  | some T => meaning G T
  | none => match os.find? (·.key == e.1) with
    | some q => meaning G q.type
    | none => fun _ _ u => u = e.2

theorem entryFam_adm (G : NormalGraph ι) (fs os) (e : PropKey × Tm) : Adm (entryFam G fs os e) := by
  unfold entryFam
  split
  · exact setSem_adm (normalDenote_adm G) _
  · split
    · exact setSem_adm (normalDenote_adm G) _
    · exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

/-- The entries a merge allocates, read through its two sides. -/
structure Sides (G : NormalGraph ι) (d : List PropKey) (oa : Obj ι) (sb : Src ι)
    (p : Nat) (W : WorldT (p + 1)) (pa qs : List (PropKey × Tm)) : Prop where
  neverA : ∀ k, oa.neverA k = true → pa.lookup k = none
  sureA : ∀ k T, oa.sureA k T = true → ∃ v, pa.lookup k = some v ∧ meaning G T p (below W) v
  withinA : ∀ k T, oa.withinA k T = true → ∀ v, pa.lookup k = some v → meaning G T p (below W) v
  never : ∀ k, sb.never d k = true → qs.lookup k = none
  sure : ∀ k T, sb.sure d k T = true → ∃ v, qs.lookup k = some v ∧ meaning G T p (below W) v
  within : ∀ k T, sb.within d k T = true → ∀ v, qs.lookup k = some v → meaning G T p (below W) v
  /-- A key the source gives is one it copied, not dropped, or an index. -/
  bound : ∀ K ∈ (match sb with | .prim => [] | .obj ob => ob.bounds),
    ∀ k v, qs.lookup k = some v → K.among = true → K.admits arrayStoreKey = false →
      copiedKey k = true ∧ d.contains k = false ∧ K.admits k = true
  /-- A key the accumulator gives is its own, not the store. -/
  boundA : ∀ K ∈ oa.bounds, ∀ k v, pa.lookup k = some v → k ≠ arrayStoreKey ∧ K.admits k = true
  proto : qs.lookup CallArguments.protoField = none

theorem proto_not_copied : copiedKey CallArguments.protoField = false := by decide
theorem proto_not_index : indexKey CallArguments.protoField = false := by decide

/-- A plain-object source's copy, read through its clause. -/
theorem sides_obj {G : NormalGraph ι} {d : List PropKey} {oa ob : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fa fb : List (PropKey × Nat)} (hfa : ObjFacts G oa (p + 1) W fa) (hfb : ObjFacts G ob (p + 1) W fb)
    {h : Heap} (hok : HeapOk (p + 1) W h) {pa qs : List (PropKey × Tm)}
    (hp : ownAll h (.objAt fa .absent) = some pa) (hq : ownData h (.objAt fb .absent) = some qs) :
    Sides G d oa (.obj ob) p W pa (qs.filter fun e => !d.contains e.1) where
  neverA _ hn := acc_never hfa hp hn
  sureA _ _ hs := acc_sure hfa hok hp hs
  withinA _ _ hs _ hv := acc_within hfa hok hp hs hv
  never _ hn := src_never hfb hq hn
  sure _ _ hs := src_sure hfb hok hq hs
  within _ _ hs _ hv := src_within hfb hok hq hs hv
  bound K hK k v hv hamong hstore := by
    rw [srcData_lookup hq] at hv
    by_cases hd : d.contains k = true
    · rw [if_pos hd] at hv; cases hv
    rw [if_neg hd] at hv
    have hs : fb.lookup arrayStoreKey = none := ownKeysT_lookup (hfb.bounds K hK) hstore
    rw [storeData_lookup_none (.inr hs), Option.or_none] at hv
    by_cases hc : copiedKey k = true
    · rw [if_pos hc] at hv
      cases hl : fb.lookup k with
      | none => rw [hl] at hv; cases hv
      | some l => exact ⟨hc, by simpa using hd, ownKeysT_admits (hfb.bounds K hK) hl⟩
    · rw [if_neg hc] at hv; cases hv
  boundA K hK k v hv := by
    rw [ownAll_lookup hp] at hv
    by_cases hk : (k != arrayStoreKey) = true
    · rw [if_pos hk] at hv
      cases hl : fa.lookup k with
      | none => rw [hl] at hv; cases hv
      | some l => exact ⟨by simpa using hk, ownKeysT_admits (hfa.bounds K hK) hl⟩
    · rw [if_neg hk] at hv; cases hv
  proto := by
    rw [srcData_lookup hq]
    split
    · rfl
    · rw [if_neg (by simp [proto_not_copied]), Option.map_none, Option.none_or]
      exact storeData_lookup_none (.inl proto_not_index)

/-- A source owning no enumerable property gives nothing. -/
theorem sides_prim {G : NormalGraph ι} {d : List PropKey} {oa : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fa : List (PropKey × Nat)} (hfa : ObjFacts G oa (p + 1) W fa)
    {h : Heap} (hok : HeapOk (p + 1) W h) {pa : List (PropKey × Tm)}
    (hp : ownAll h (.objAt fa .absent) = some pa) :
    Sides G d oa .prim p W pa [] where
  neverA _ hn := acc_never hfa hp hn
  sureA _ _ hs := acc_sure hfa hok hp hs
  withinA _ _ hs _ hv := acc_within hfa hok hp hs hv
  never _ _ := rfl
  sure _ _ hs := by simp [Src.sure] at hs
  within _ _ _ _ hv := by simp [List.lookup] at hv
  bound _ hK := by simp at hK
  boundA K hK k v hv := by
    rw [ownAll_lookup hp] at hv
    by_cases hk : (k != arrayStoreKey) = true
    · rw [if_pos hk] at hv
      cases hl : fa.lookup k with
      | none => rw [hl] at hv; cases hv
      | some l => exact ⟨by simpa using hk, ownKeysT_admits (hfa.bounds K hK) hl⟩
    · rw [if_neg hk] at hv; cases hv
  proto := rfl

theorem admits_among {K : KeyBound} (ha : K.among = true) {k : PropKey} :
    K.admits k = true ↔ k ∈ K.keys := by
  simp [KeyBound.admits, ha]

theorem admits_outside {K : KeyBound} (ha : K.among = false) {k : PropKey} :
    K.admits k = true ↔ k ∉ K.keys := by
  simp [KeyBound.admits, ha]

/-- What the merged entries hold, from the two sides and the clause. -/
theorem result_facts {G : NormalGraph ι} {d : List PropKey} {oa : Obj ι} {sb : Src ι} {p : Nat}
    {W : WorldT (p + 1)} {pa qs : List (PropKey × Tm)} (hs : Sides G d oa sb p W pa qs)
    {fs : List (PropKey × List ι)} {os : List (OptionalField (List ι))} {ks : List KeyBound}
    (hfs : ∀ q ∈ fs, (sb.sure d q.1 q.2 || (oa.sureA q.1 q.2 && sb.within d q.1 q.2)) = true)
    (hos : ∀ q ∈ os, (oa.withinA q.key q.type && sb.within d q.key q.type) = true)
    (hpr : (os.isEmpty || oa.neverA CallArguments.protoField) = true)
    (hks : ∀ K ∈ ks, boundOk oa sb d K = true) :
    (∀ q ∈ fs, ∃ v, (mergeData pa qs).lookup q.1 = some v ∧ meaning G q.2 p (below W) v) ∧
    (∀ q ∈ os, ∀ v, (mergeData pa qs).lookup q.key = some v → meaning G q.type p (below W) v) ∧
    (os ≠ [] → (mergeData pa qs).lookup CallArguments.protoField = none) ∧
    (∀ K ∈ ks, ∀ k ∈ (mergeData pa qs).map Prod.fst, K.admits k = true) := by
  refine ⟨fun q hq => ?_, fun q hq v hv => ?_, fun hne => ?_, fun K hK k hk => ?_⟩
  · have h := hfs q hq
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rw [lookup_mergeData]
    rcases h with hsure | ⟨hsa, hw⟩
    · obtain ⟨v, hv, hm⟩ := hs.sure _ _ hsure
      exact ⟨v, by rw [hv]; rfl, hm⟩
    · cases hq' : qs.lookup q.1 with
      | some v => exact ⟨v, rfl, hs.within _ _ hw v hq'⟩
      | none =>
        obtain ⟨v, hv, hm⟩ := hs.sureA _ _ hsa
        exact ⟨v, by rw [Option.none_or, hv], hm⟩
  · have h := hos q hq
    simp only [Bool.and_eq_true] at h
    rw [lookup_mergeData] at hv
    cases hq' : qs.lookup q.key with
    | some w =>
      rw [hq', Option.some_or] at hv; cases hv
      exact hs.within _ _ h.2 _ hq'
    | none =>
      rw [hq', Option.none_or] at hv
      exact hs.withinA _ _ h.1 _ hv
  · have hn : oa.neverA CallArguments.protoField = true := by
      simp only [Bool.or_eq_true, List.isEmpty_iff] at hpr
      rcases hpr with h | h
      · exact absurd h hne
      · exact h
    rw [lookup_mergeData, hs.proto, Option.none_or]
    exact hs.neverA _ hn
  · obtain ⟨v, hv⟩ := lookup_isSome hk
    rw [lookup_mergeData] at hv
    have hb := hks K hK
    unfold boundOk at hb
    split at hb
    · rename_i hamong
      simp only [Bool.and_eq_true] at hb
      obtain ⟨hA, hB⟩ := hb
      cases hq' : qs.lookup k with
      | some w =>
        cases sb with
        | prim => rw [hs.never k rfl] at hq'; cases hq'
        | obj ob =>
          obtain ⟨Kb, hKb, hbits⟩ := List.any_eq_true.mp hB
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hbits
          obtain ⟨⟨hKa, hst⟩, hall⟩ := hbits
          have hstore : Kb.admits arrayStoreKey = false := by
            simp only [KeyBound.admits, hKa, hst]; rfl
          obtain ⟨hc, hd, hadm⟩ := hs.bound Kb hKb k w hq' hKa hstore
          have := hall k ((admits_among hKa).mp hadm)
          simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
          rcases this with (h1 | h1) | h1
          · rw [hc] at h1; cases h1
          · rw [hd] at h1; cases h1
          · exact h1
      | none =>
        rw [hq', Option.none_or] at hv
        obtain ⟨Ka, hKa, hbits⟩ := List.any_eq_true.mp hA
        simp only [Bool.and_eq_true, List.all_eq_true] at hbits
        obtain ⟨hKam, hall⟩ := hbits
        obtain ⟨hne, hadm⟩ := hs.boundA Ka hKa k v hv
        have := hall k ((admits_among hKam).mp hadm)
        simp only [Bool.or_eq_true, beq_iff_eq] at this
        rcases this with h1 | h1
        · exact absurd h1 hne
        · exact h1
    · rename_i hamong
      rw [admits_outside (by simpa using hamong)]
      intro hkK
      have := List.all_eq_true.mp hb k hkK
      simp only [Bool.and_eq_true] at this
      rw [hs.never k this.2, Option.none_or, hs.neverA k this.1] at hv
      cases hv

theorem slots_fst_mem {base : Nat} {ns : List PropKey} {q : PropKey × Nat}
    (h : q ∈ slots base ns) : q.1 ∈ ns := by
  induction ns generalizing base with
  | nil => simp [slots] at h
  | cons n ns ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem key_unique {os : List (OptionalField (List ι))} (hnd : (os.map (·.key)).Nodup)
    {q q' : OptionalField (List ι)} (hq : q ∈ os) (hq' : q' ∈ os) (hk : q.key = q'.key) : q = q' := by
  induction os with
  | nil => simp at hq
  | cons o os ih =>
    rw [List.map_cons] at hnd
    have hn := List.nodup_cons.mp hnd
    have h1 := List.mem_cons.mp hq
    have h2 := List.mem_cons.mp hq'
    rcases h1 with e1 | m1
    · rcases h2 with e2 | m2
      · rw [e1, e2]
      · exfalso; apply hn.1; rw [← e1, hk]; exact List.mem_map_of_mem m2
    · rcases h2 with e2 | m2
      · exfalso; apply hn.1; rw [← e2, ← hk]; exact List.mem_map_of_mem m1
      · exact ih hn.2 m1 m2

/-- **The merge step, from values.** Once both operands are values, the merge
reads the properties they own now and allocates them: the entries the result
states at their types, and every other at exactly the value copied. -/
theorem merge_finish {G : NormalGraph ι} {d : List PropKey} {oa : Obj ι} {sb : Src ι} {p : Nat}
    {W : WorldT (p + 1)} {h : Heap} {va vb : Val} {pa qs : List (PropKey × Tm)}
    (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h) (hs : Sides G d oa sb p W pa qs)
    (hpn : (pa.map Prod.fst).Nodup) (hqn : (qs.map Prod.fst).Nodup)
    (hva : isVal va = true) (hvb : isVal vb = true)
    (hparts : mergeParts h d va vb = some (mergeData pa qs))
    {R : List ι} {fs : List (PropKey × List ι)} {os : List (OptionalField (List ι))} {ks : List KeyBound}
    (hcr : .refs fs [] [] os [] ks ∈ expand G R)
    (hnd : (fs.map Prod.fst ++ os.map (·.key)).Nodup)
    (hfs : ∀ q ∈ fs, (sb.sure d q.1 q.2 || (oa.sureA q.1 q.2 && sb.within d q.1 q.2)) = true)
    (hos : ∀ q ∈ os, (oa.withinA q.key q.type && sb.within d q.key q.type) = true)
    (hpr : (os.isEmpty || oa.neverA CallArguments.protoField) = true)
    (hks : ∀ K ∈ ks, boundOk oa sb d K = true) :
    Safe (meaning G R) (p + 1) W h (.merge d va vb) := by
  have hnodup := mergeData_nodup hpn hqn
  obtain ⟨hF, hO, hP, hK⟩ := result_facts hs hfs hos hpr hks
  have hfn : (fs.map Prod.fst).Nodup := hnd.sublist (List.sublist_append_left _ _)
  have hon : (os.map (·.key)).Nodup := hnd.sublist (List.sublist_append_right _ _)
  have hdisj : ∀ q ∈ os, fs.lookup q.key = none := by
    intro q hq
    apply lookup_eq_none
    intro hm
    exact (List.nodup_append.mp hnd).2.2 _ hm _ (List.mem_map_of_mem hq) rfl
  generalize mergeData pa qs = ps at hparts hnodup hF hO hP hK
  have hvals : ∀ v ∈ ps.map Prod.snd, isVal v = true := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
    rcases mergeParts_vals hparts e he with h1 | ⟨-, h2⟩
    · rw [h1]; rfl
    · exact h2
  -- The family an entry's location is given, and why its value meets it.
  have hfam : ∀ e ∈ ps, entryFam G fs os e p (below W) e.2 := by
    intro e he
    have hl := lookup_of_mem hnodup he
    cases hT : fs.lookup e.1 with
    | some T =>
      simp only [entryFam, hT]
      obtain ⟨v, hv, hm⟩ := hF (e.1, T) (mem_of_lookup hT)
      rw [hl] at hv; cases hv; exact hm
    | none =>
      cases hq : os.find? (·.key == e.1) with
      | some q =>
        simp only [entryFam, hT, hq]
        have hk : q.key = e.1 := by simpa using List.find?_some hq
        exact hO q (List.mem_of_find?_eq_some hq) e.2 (hk ▸ hl)
      | none => simp only [entryFam, hT, hq]
  refine Or.inr ⟨below W, h, .makeAt .absent (ps.map Prod.fst) (ps.map Prod.snd), WExt_refl _,
    WorldAdm_trunc _ hadm, Step.mergeV hva hvb hparts, HeapOk_trunc p W h hok, ?_⟩
  apply make_fields_rule (As := ps.map (entryFam G fs os))
    (fun A hA => by obtain ⟨e, -, rfl⟩ := List.mem_map.mp hA; exact entryFam_adm G fs os e)
    p (below W) h .absent (ps.map Prod.fst) (ps.map Prod.snd) hnodup (by simp) (by simp) hvals
    (WorldAdm_trunc _ hadm) (HeapOk_trunc p W h hok)
  · intro q hq
    rw [List.zip_map', List.mem_map] at hq
    obtain ⟨e, he, rfl⟩ := hq
    exact hfam e he
  · intro j hj U hx hrec
    -- The pair each entry contributes to the record the allocation meets.
    have hzip : ∀ e ∈ ps, (e.1, entryFam G fs os e) ∈ (ps.map Prod.fst).zip (ps.map (entryFam G fs os)) := by
      intro e he
      rw [List.zip_map', List.mem_map]
      exact ⟨e, he, rfl⟩
    refine (expand_sem G R (plain_of_mem_expand hcr) j U _).mpr ⟨_, hcr, ?_⟩
    simp only [clauseSem, semWithArgs]
    refine ⟨⟨⟨_, rfl, ?_⟩, by simp⟩, ?_, ⟨_, rfl, ?_, ?_⟩, MethodMembers.methodT_nil _ _ _, ?_⟩
    · intro f F hm
      obtain ⟨T, hT, rfl⟩ := ReferenceConjunctions.mem_famsOf.mp hm
      obtain ⟨v, hv, -⟩ := hF (f, T) hT
      have he := mem_of_lookup hv
      obtain ⟨fl, l, c, hfl, hl, hU, hag⟩ := recT_at (hzip _ he) hrec
      cases hfl
      have : entryFam G fs os (f, v) = meaning G T := by
        simp [entryFam, lookup_of_mem hfn hT]
      exact ⟨l, c, hl, hU, fun i hi U' u => (hag i hi U' u).trans (by rw [this])⟩
    · intro f F hm; simp [ReferenceConjunctions.famsOf] at hm
    · intro o ho _
      have hne : os ≠ [] := by
        intro he; subst he; simp at ho
      apply lookup_slots_none
      intro hm
      obtain ⟨v, hv⟩ := lookup_isSome hm
      rw [hP hne] at hv; cases hv
    · intro o ho l hl
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
      have hmem := mem_of_lookup_slots hl
      obtain ⟨v, hv⟩ := lookup_isSome hmem
      have he := mem_of_lookup hv
      obtain ⟨fl, l', c, hfl, hl', hU, hag⟩ := recT_at (hzip _ he) hrec
      cases hfl
      rw [hl] at hl'; cases hl'
      have hfind : ∃ q', os.find? (·.key == q.key) = some q' ∧ q' = q := by
        cases hf : os.find? (·.key == q.key) with
        | none =>
          exfalso
          have := List.find?_eq_none.mp hf q hq
          simp at this
        | some q' =>
          refine ⟨q', rfl, key_unique hon (List.mem_of_find?_eq_some hf) hq ?_⟩
          simpa using List.find?_some hf
      obtain ⟨q', hf, rfl⟩ := hfind
      have : entryFam G fs os (q'.key, v) = meaning G q'.type := by
        simp only [entryFam, hdisj q' hq, hf]
      refine ⟨c, hU, fun i hi U' u => ?_⟩
      have hiff : c i hi U' u ↔ meaning G q'.type i U' u :=
        (hag i hi U' u).trans (by simp only [OptionalField.map]; rw [this])
      exact ⟨hiff.mp, fun _ => hiff.mpr⟩
    · intro K hKm
      exact ⟨_, rfl, fun q hq => hK K hKm q.1 (slots_fst_mem hq)⟩

/-- **A merge of two values is safe at a result the rule states.** -/
theorem merge_values_safe {G : NormalGraph ι} {d : List PropKey} {A B R : List ι}
    (hm : MergeOk G d A B R = true) {n : Nat} {W : WorldT n} {h : Heap} {va vb : Val}
    (hadm : WorldAdm W) (hok : HeapOk n W h) (ha : meaning G A n W va) (hb : meaning G B n W vb) :
    Safe (meaning G R) n W h (.merge d va vb) := by
  cases n with
  | zero => trivial
  | succ p =>
  simp only [MergeOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hm
  obtain ⟨⟨hpA, hpB⟩, hall⟩ := hm
  obtain ⟨ca, hca, hsa⟩ := (expand_sem G A hpA _ _ _).mp ha
  obtain ⟨cb, hcb, hsb⟩ := (expand_sem G B hpB _ _ _).mp hb
  obtain ⟨cr, hcr, hmc⟩ := hall ca hca cb hcb
  unfold MergeClause at hmc
  split at hmc
  · rename_i oa sb fs os ks hoa hsrc
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hmc
    obtain ⟨⟨⟨⟨hnd, hfs⟩, hos⟩, hpr⟩, hks⟩ := hmc
    obtain ⟨fa, rfl, hfa⟩ := objFacts_of_sem hoa hsa
    have hp : ownAll h (.objAt fa .absent) = some (firstKeys
        ((fa.filter (·.1 != arrayStoreKey)).map (fun p => (p.1, heapVal h p.2)))) := rfl
    unfold srcOf at hsrc
    split at hsrc
    · rename_i hempty
      cases hsrc
      obtain ⟨hq, hvb⟩ := emptyClause_ownData hempty hsb h
      exact merge_finish hadm hok (sides_prim hfa hok hp) (ownAll_nodup hp) (by simp) rfl hvb
        (by simp [mergeParts, hp, hq]) hcr hnd hfs (fun q hq => by simpa using hos q hq) hpr hks
    · obtain ⟨ob, hob, rfl⟩ := Option.map_eq_some_iff.mp hsrc
      obtain ⟨fb, rfl, hfb⟩ := objFacts_of_sem hob hsb
      have hq : ownData h (.objAt fb .absent) = some (firstKeys
          ((fb.filter (copiedKey ·.1)).map (fun p => (p.1, heapVal h p.2)) ++ storeData h fb)) := rfl
      exact merge_finish hadm hok (sides_obj hfa hfb hok hp hq) (ownAll_nodup hp)
        ((ownData_nodup hq).sublist (List.Sublist.map _ List.filter_sublist)) rfl rfl
        (by simp [mergeParts, hp, hq]) hcr hnd hfs (fun q hq => by simpa using hos q hq) hpr hks
  · cases hmc

/-! ### The result a merge is typed at

Untrusted: what extraction proposes for a merge, one clause per pair of the
operands' clauses. `MergeClause` checks it, as any claim. -/

/-- The type a side's field or view states for a key. -/
def Obj.namedType (o : Obj ι) (k : PropKey) : Option (List ι) :=
  (o.named.find? (·.1 == k)).map (·.2)

/-- The types a side may hold under a key it need not own: its optional
field's, and, for a string key, its index types. -/
def Obj.maybeTypes (o : Obj ι) (k : PropKey) : List ι :=
  (o.optional.filter (·.key == k)).flatMap (·.type) ++ (o.indexes.filter (·.1.may k)).flatMap (·.2)

def Obj.keys (o : Obj ι) : List PropKey := o.named.map (·.1) ++ o.optional.map (·.key)

/-- The record a merge of two clauses gives: each key the source surely
copies, at its type; each the accumulator surely has, at its type with what
the source may copy over it; the rest, where both sides' types say what they
may hold, optional; and, when both sides list their keys, the keys listed. -/
def mergeResult (d : List PropKey) (ca cb : Clause (List ι)) : Option (Clause (List ι)) := do
  let oa ← objOf ca
  let sb ← srcOf cb
  let bKeys := match sb with | .prim => [] | .obj ob => ob.keys
  let keys := (oa.keys ++ bKeys).eraseDups.filter (· != arrayStoreKey)
  let bNamed (k : PropKey) : Option (List ι) := match sb with
    | .prim => none
    | .obj ob => if !d.contains k && copiedKey k then ob.namedType k else none
  let bMaybe (k : PropKey) : List ι := match sb with
    | .prim => []
    | .obj ob => if !d.contains k && copiedKey k then ob.maybeTypes k else []
  let fields := keys.filterMap fun k =>
    match bNamed k with
    | some T => some (k, T)
    | none => match oa.namedType k with
      | some Ta =>
        let T := (Ta ++ bMaybe k).eraseDups
        if sb.within d k T then some (k, T) else none
      | none => none
  let optional : List (OptionalField (List ι)) :=
    if oa.neverA CallArguments.protoField then keys.filterMap fun k =>
      if fields.any (·.1 == k) then none else
      let T := (oa.maybeTypes k ++ bMaybe k).eraseDups
      if !T.isEmpty && oa.withinA k T && sb.within d k T then some ⟨k, false, T⟩ else none
    else []
  let bound : List KeyBound := match oa.bounds.find? (·.among), sb with
    | some Ka, .prim => [⟨true, Ka.keys.filter (· != arrayStoreKey)⟩]
    | some Ka, .obj ob =>
      match ob.bounds.find? (fun K => K.among && !K.keys.contains arrayStoreKey) with
      | some Kb => [⟨true, (Ka.keys.filter (· != arrayStoreKey) ++
          Kb.keys.filter (fun x => copiedKey x && !d.contains x)).eraseDups⟩]
      | none => []
    | none, _ => []
  -- Without a prototype from the accumulator the result has none, which a
  -- later merge's optional fields need.
  let bound := if oa.neverA CallArguments.protoField && bound.isEmpty
    then [⟨false, [CallArguments.protoField]⟩] else bound
  pure (.refs fields [] [] optional [] bound)

#print axioms merge_values_safe

end Verification.Model.ObjectMerge
