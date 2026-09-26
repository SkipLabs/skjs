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
bound admits every key either side may give. A result may also state an
index (`DictOk`): whatever either side gives under a key its class admits is
within its type, which both sides say through an index or their exact keys
(`classWithinA`, `Src.classWithin`).
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
its optional fields, its index types (views and writable ones alike), its key
bounds, and whether it states no prototype, as an index does. -/
structure Obj (ι : Type) where
  named : List (PropKey × List ι)
  optional : List (OptionalField (List ι))
  indexes : List (IndexKeys × List ι)
  bounds : List KeyBound
  plain : Bool

def objOf : Clause (List ι) → Option (Obj ι)
  | .refs a bs vs os _ ks => some ⟨(a :: bs).flatten ++ vs, os, [], ks, false⟩
  | .dict a bs vs ds os _ ks cs => some ⟨(a :: bs).flatten ++ vs, os, ds ++ cs, ks, !(ds ++ cs).isEmpty⟩
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
  plain : o.plain = true → fs.lookup CallArguments.protoField = none

theorem objFacts_of_sem {G : NormalGraph ι} {c : Clause (List ι)} {o : Obj ι} (ho : objOf c = some o)
    {n : Nat} {W : WorldT n} {v : Val} (hv : clauseSem G c n W v) :
    ∃ fs, v = .objAt fs .absent ∧ ObjFacts G o n W fs := by
  unfold objOf at ho
  split at ho
  · rename_i a bs vs os ms ks
    cases ho
    obtain ⟨hr, hw, hopt, -, hb⟩ := hv
    obtain ⟨fs, rfl, -⟩ := hr.1
    refine ⟨fs, rfl, ⟨fun p hp => ?_, fun q hq l hl => ?_, fun x hx => by simp at hx, hb,
      fun hp => by simp at hp⟩⟩
    · obtain ⟨fs', l, c, he, hl, hc, hag⟩ := fields_at (η := G.env) hr hw p hp
      cases he
      exact ⟨l, c, hl, hc, hag⟩
    · obtain ⟨fs', he, -, hall⟩ := hopt
      cases he
      obtain ⟨c, hc, hag⟩ := hall _ (List.mem_map_of_mem hq) l hl
      exact ⟨c, hc, fun j hj U u hu => (hag j hj U u).1 hu⟩
  · rename_i a bs vs ds os ms ks cs
    cases ho
    obtain ⟨hr, hw, ⟨hd, hcs⟩, hopt, -, hb⟩ := hv
    obtain ⟨fs, rfl, -⟩ := hr.1
    have hview : ∀ x ∈ ds ++ cs, dictViewT x.1 (meaning G x.2) n W (.objAt fs .absent) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hd x hx
      · exact dictCellT_view (hcs x hx)
    refine ⟨fs, rfl, ⟨fun p hp => ?_, fun q hq l hl => ?_, fun x hx f l hk hl => ?_, hb,
      fun hp => ?_⟩⟩
    · obtain ⟨fs', l, c, he, hl, hc, hag⟩ := fields_at (η := G.env) hr hw p hp
      cases he
      exact ⟨l, c, hl, hc, hag⟩
    · obtain ⟨fs', he, -, hall⟩ := hopt
      cases he
      obtain ⟨c, hc, hag⟩ := hall _ (List.mem_map_of_mem hq) l hl
      exact ⟨c, hc, fun j hj U u hu => (hag j hj U u).1 hu⟩
    · exact dictViewT_present (hview x hx) hk hl
    · cases hne : ds ++ cs with
      | nil => rw [hne] at hp; simp at hp
      | cons x _ => exact dictViewT_no_proto (hview x (by rw [hne]; exact List.mem_cons_self))
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

/-- The accumulator never gives the key: it is the store's, or excluded, or
the prototype of an object its index says has none. -/
def Obj.neverA (o : Obj ι) (k : PropKey) : Bool :=
  k == arrayStoreKey || excludes o.bounds k || (o.plain && k == CallArguments.protoField)

def Obj.sureA (o : Obj ι) (k : PropKey) (T : List ι) : Bool :=
  k != arrayStoreKey && o.named.any fun p => p.1 == k && inLabels p.2 T

def Obj.withinA (o : Obj ι) (k : PropKey) (T : List ι) : Bool :=
  o.neverA k || o.sureA k T ||
    (k != arrayStoreKey && ((o.optional.any fun q => q.key == k && inLabels q.type T) ||
      (o.indexes.any fun x => x.1.surely k && inLabels x.2 T)))

/-! ### What a side gives under the keys of an index class

A result with an index states what every present key its class admits holds,
so each side must say that of every such key it may give: through an index
of a class containing it, or by listing its own keys (an `among` bound) and
typing each the class may admit. -/

/-- Whatever the accumulator gives under a key the class `K` admits is within
`T`. -/
def Obj.classWithinA (o : Obj ι) (K : IndexKeys) (T : List ι) : Bool :=
  o.named.all (fun p => !K.may p.1 || inLabels p.2 T) &&
  o.optional.all (fun q => !K.may q.key || inLabels q.type T) &&
  (o.indexes.any (fun x => K.within x.1 && inLabels x.2 T) ||
   o.bounds.any fun B => B.among && B.keys.all fun x =>
     !K.may x || x == arrayStoreKey || o.named.any (·.1 == x) || o.optional.any (·.key == x))

/-- A type none of whose members is an array's store: every clause is a
primitive's or a plain object's. A string index at such a type rules out the
store key, `[]`, which is a string. -/
def noStore (G : NormalGraph ι) (T : List ι) : Bool :=
  G.plainTy T && (expand G T).all fun c => match c with
    | .nul | .undef | .bool | .boolLit _ | .num | .numLit _ | .str | .strLit _
    | .bigint | .bigintLit _ | .symbol | .refs .. | .dict .. => true
    | _ => false

theorem noStore_sound {G : NormalGraph ι} {T : List ι} (h : noStore G T = true)
    {n : Nat} {W : WorldT n} {ls : List (Option Nat)} : ¬ meaning G T n W (.arr ls) := by
  intro hm
  simp only [noStore, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨c, hc, hs⟩ := (expand_sem G T h.1 _ _ _).mp hm
  have hw := h.2 c hc
  cases c with
  | nul => simp only [clauseSem, semWithArgs, nulT] at hs; cases hs
  | undef => simp only [clauseSem, semWithArgs, undefT] at hs; cases hs
  | bool => simp only [clauseSem, semWithArgs, boolT] at hs; rcases hs with h1 | h1 <;> cases h1
  | boolLit b => simp only [clauseSem, semWithArgs] at hs; cases b <;> cases hs
  | num => simp only [clauseSem, semWithArgs, numT] at hs; obtain ⟨_, h1⟩ := hs; cases h1
  | numLit _ => simp only [clauseSem, semWithArgs] at hs; cases hs
  | str => simp only [clauseSem, semWithArgs, strT] at hs; obtain ⟨_, h1⟩ := hs; cases h1
  | strLit _ => simp only [clauseSem, semWithArgs] at hs; cases hs
  | bigint => simp only [clauseSem, semWithArgs, bigintT] at hs; obtain ⟨_, h1⟩ := hs; cases h1
  | bigintLit _ => simp only [clauseSem, semWithArgs] at hs; cases hs
  | symbol => simp only [clauseSem, semWithArgs, symbolT] at hs; obtain ⟨_, h1⟩ := hs; cases h1
  | refs a bs vs os ms ks =>
    simp only [clauseSem, semWithArgs, ReferenceConjunctions.refsT, recT] at hs
    obtain ⟨⟨⟨_, h1, -⟩, -⟩, -⟩ := hs; cases h1
  | dict a bs vs ds os ms ks cs =>
    simp only [clauseSem, semWithArgs, ReferenceConjunctions.refsT, recT] at hs
    obtain ⟨⟨⟨_, h1, -⟩, -⟩, -⟩ := hs; cases h1
  | arrs L S => simp at hw
  | callable a bs L S => simp at hw
  | top => simp at hw
  | list a bs => simp at hw
  | ctors L S => simp at hw
  | pack a bs => simp at hw

/-- Whatever the source gives under a key the class `K` admits is within `T`:
a symbol class admits none of the string keys a copy gives; otherwise the
source owns no store whose elements it would give under index keys, and each
key it copies is typed. -/
def Src.classWithin (G : NormalGraph ι) : Src ι → List PropKey → IndexKeys → List ι → Bool
  | .prim, _, _, _ => true
  | .obj o, d, K, T => K == .symbols ||
    (excludes o.bounds arrayStoreKey || o.indexes.any (fun x => x.1 == .strings && noStore G x.2)) &&
    o.named.all (fun p => !K.may p.1 || d.contains p.1 || !copiedKey p.1 || inLabels p.2 T) &&
    o.optional.all (fun q => !K.may q.key || d.contains q.key || !copiedKey q.key || inLabels q.type T) &&
    (o.indexes.any (fun x => K.within x.1 && inLabels x.2 T) ||
     o.bounds.any fun B => B.among && B.keys.all fun x =>
       !K.may x || d.contains x || !copiedKey x || o.named.any (·.1 == x) || o.optional.any (·.key == x))

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
  simp only [Obj.neverA, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hn
  rcases hn with (rfl | hx) | ⟨hpl, rfl⟩
  · simp
  · simp [excludes_lookup hx hf.bounds]
  · simp [hf.plain hpl]

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

/-- What the accumulator gives under a key its class admits, read through
`classWithinA`. -/
theorem acc_class {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {ps : List (PropKey × Tm)} (hp : ownAll h (.objAt fs .absent) = some ps)
    {K : IndexKeys} {T : List ι} (hc : o.classWithinA K T = true) {k : PropKey} (hk : K.Admits k)
    {v : Tm} (hv : ps.lookup k = some v) : meaning G T p (below W) v := by
  have hmay := IndexKeys.may_of_admits hk
  rw [ownAll_lookup hp] at hv
  by_cases hs : (k != arrayStoreKey) = true
  · rw [if_pos hs] at hv
    cases hl : fs.lookup k with
    | none => rw [hl] at hv; cases hv
    | some l =>
      rw [hl] at hv; cases hv
      simp only [Obj.classWithinA, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', List.any_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hnamed, hopt⟩, hroute⟩ := hc
      have typed : (∃ q ∈ o.named, q.1 = k) ∨ (∃ q ∈ o.optional, q.key = k) →
          meaning G T p (below W) (heapVal h l) := by
        rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
        · obtain ⟨l', c, hl', hcw, hag⟩ := hf.named q hq
          rw [hl] at hl'; cases hl'
          have hin : inLabels q.2 T = true := by
            rcases hnamed q hq with h1 | h1
            · rw [hmay] at h1; cases h1
            · exact h1
          exact heap_contract_within hok hcw hag hin
        · obtain ⟨c, hcw, hag⟩ := hf.optional q hq l hl
          have hin : inLabels q.type T = true := by
            rcases hopt q hq with h1 | h1
            · rw [hmay] at h1; cases h1
            · exact h1
          exact heap_contract_within hok hcw hag hin
      rcases hroute with ⟨x, hx, hwithin, hlab⟩ | ⟨B, hB, hamong, hkeys⟩
      · obtain ⟨c, hcw, hag⟩ := hf.indexes x hx k l (IndexKeys.within_admits hwithin hk) hl
        exact heap_contract_within hok hcw hag hlab
      · have hadm := ownKeysT_admits (hf.bounds B hB) hl
        have hkB : k ∈ B.keys := by simpa [KeyBound.admits, hamong] using hadm
        rcases hkeys k hkB with ((h1 | h1) | h1) | h1
        · rw [hmay] at h1; cases h1
        · simp [h1] at hs
        · exact typed (.inl h1)
        · exact typed (.inr h1)
  · rw [if_neg hs] at hv; cases hv

/-- The store key is a string key: a string index constrains it. -/
theorem strings_admit_store : IndexKeys.strings.Admits arrayStoreKey := trivial

/-- What the source gives under a key its class admits, read through
`classWithin`. -/
theorem src_class {G : NormalGraph ι} {o : Obj ι} {p : Nat} {W : WorldT (p + 1)}
    {fs : List (PropKey × Nat)} (hf : ObjFacts G o (p + 1) W fs) {h : Heap} (hok : HeapOk (p + 1) W h)
    {qs : List (PropKey × Tm)} (hq : ownData h (.objAt fs .absent) = some qs) {d : List PropKey}
    {K : IndexKeys} {T : List ι} (hc : (Src.obj o).classWithin G d K T = true) {k : PropKey}
    (hk : K.Admits k) {v : Tm} (hv : (qs.filter fun e => !d.contains e.1).lookup k = some v) :
    meaning G T p (below W) v := by
  have hmay := IndexKeys.may_of_admits hk
  rw [srcData_lookup hq] at hv
  by_cases hd : d.contains k = true
  · rw [if_pos hd] at hv; cases hv
  rw [if_neg hd] at hv
  simp only [Src.classWithin, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_true, beq_iff_eq] at hc
  rcases hc with hsym | ⟨⟨⟨hstore, hnamed⟩, hopt⟩, hroute⟩
  · subst hsym
    cases k with
    | str s => exact absurd hk (by simp [IndexKeys.Admits])
    | sym i =>
      rw [if_neg (by simp [copiedKey]), Option.map_none, Option.none_or,
        storeData_lookup_none (.inl rfl)] at hv
      cases hv
  · have hnone : (storeData h fs).lookup k = none := by
      rcases hstore with hx | ⟨x, hx, hstr, hns⟩
      · exact storeData_lookup_none (.inr (excludes_lookup hx hf.bounds))
      · unfold storeData
        cases hl : fs.lookup arrayStoreKey with
        | none => rfl
        | some l =>
          obtain ⟨c, hcw, hag⟩ := hf.indexes x hx arrayStoreKey l (by rw [hstr]; exact strings_admit_store) hl
          obtain ⟨u, hu, hmem⟩ := hok.2 l c hcw
          have hm := hag p (Nat.lt_succ_self p) _ u (hmem p (Nat.lt_succ_self p))
          simp only [hu]
          cases u with
          | arr ls => exact absurd hm (noStore_sound hns)
          | _ => rfl
    rw [hnone, Option.or_none] at hv
    by_cases hcp : copiedKey k = true
    · rw [if_pos hcp] at hv
      cases hl : fs.lookup k with
      | none => rw [hl] at hv; cases hv
      | some l =>
        rw [hl] at hv; cases hv
        have hd' : d.contains k = false := by simpa using hd
        have typed : (∃ q ∈ o.named, q.1 = k) ∨ (∃ q ∈ o.optional, q.key = k) →
            meaning G T p (below W) (heapVal h l) := by
          rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
          · obtain ⟨l', c, hl', hcw, hag⟩ := hf.named q hq
            rw [hl] at hl'; cases hl'
            have hin : inLabels q.2 T = true := by
              rcases hnamed q hq with ((h1 | h1) | h1) | h1
              · rw [hmay] at h1; cases h1
              · rw [hd'] at h1; cases h1
              · rw [hcp] at h1; cases h1
              · exact h1
            exact heap_contract_within hok hcw hag hin
          · obtain ⟨c, hcw, hag⟩ := hf.optional q hq l hl
            have hin : inLabels q.type T = true := by
              rcases hopt q hq with ((h1 | h1) | h1) | h1
              · rw [hmay] at h1; cases h1
              · rw [hd'] at h1; cases h1
              · rw [hcp] at h1; cases h1
              · exact h1
            exact heap_contract_within hok hcw hag hin
        rcases hroute with ⟨x, hx, hwithin, hlab⟩ | ⟨B, hB, hamong, hkeys⟩
        · obtain ⟨c, hcw, hag⟩ := hf.indexes x hx k l (IndexKeys.within_admits hwithin hk) hl
          exact heap_contract_within hok hcw hag hlab
        · have hadm := ownKeysT_admits (hf.bounds B hB) hl
          have hkB : k ∈ B.keys := by simpa [KeyBound.admits, hamong] using hadm
          rcases hkeys k hkB with ((((h1 | h1) | h1) | h1) | h1)
          · rw [hmay] at h1; cases h1
          · rw [hd'] at h1; cases h1
          · rw [hcp] at h1; cases h1
          · exact typed (.inl h1)
          · exact typed (.inr h1)
    · rw [if_neg hcp] at hv; cases hv

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

/-- A merge result's fields, optional fields and key bounds. Each field is
surely given within its type: by the source, or by the accumulator where
whatever the source gives is within it too. Each optional field is within its
type on both sides, and then the accumulator gives no prototype, so the
result has none. Each bound admits every key either side may give. -/
def FieldsOk (d : List PropKey) (oa : Obj ι) (sb : Src ι) (fs : List (PropKey × List ι))
    (os : List (OptionalField (List ι))) (ks : List KeyBound) : Bool :=
  decide ((fs.map Prod.fst ++ os.map (·.key)).Nodup) &&
  fs.all (fun p => sb.sure d p.1 p.2 || (oa.sureA p.1 p.2 && sb.within d p.1 p.2)) &&
  os.all (fun q => oa.withinA q.key q.type && sb.within d q.key q.type) &&
  (os.isEmpty || oa.neverA CallArguments.protoField) &&
  ks.all (boundOk oa sb d)

/-- A merge result's index: views (`ds`) and writable ones (`cs`), all at one
type `V`. Whatever either side gives under a key a class admits is within
`V`, and the accumulator gives no prototype. A field or optional field whose
key a class may admit is at a type within `V`, and exactly `V` where a
writable index may admit it, whose locations hold exactly `V`. -/
def DictOk (G : NormalGraph ι) (d : List PropKey) (oa : Obj ι) (sb : Src ι)
    (fs : List (PropKey × List ι)) (os : List (OptionalField (List ι)))
    (ds cs : List (IndexKeys × List ι)) : Bool :=
  match (ds ++ cs).head? with
  | none => false
  | some (_, V) =>
    oa.neverA CallArguments.protoField &&
    (ds ++ cs).all (fun x => x.2 == V && oa.classWithinA x.1 V && sb.classWithin G d x.1 V) &&
    fs.all (fun p => (!cs.any (·.1.may p.1) || p.2 == V) && (!ds.any (·.1.may p.1) || inLabels p.2 V)) &&
    os.all (fun q => (!cs.any (·.1.may q.key) || q.type == V) &&
      (!ds.any (·.1.may q.key) || inLabels q.type V))

/-- **A merge's result, clause by clause.** The accumulator is a plain object
and the source a plain object or a value owning no enumerable property; the
result is a record of fields and optional fields with key bounds
(`FieldsOk`), and, where both sides say what they give under an index's
keys, a dictionary (`DictOk`). A writable index lets outside code add keys,
which an own-key bound listing keys would deny: a result with one lists
none. -/
def MergeClause (G : NormalGraph ι) (d : List PropKey) (ca cb cr : Clause (List ι)) : Bool :=
  match objOf ca, srcOf cb, cr with
  | some oa, some sb, .refs fs [] [] os [] ks => FieldsOk d oa sb fs os ks
  | some oa, some sb, .dict fs [] [] ds os [] ks cs =>
    FieldsOk d oa sb fs os ks && DictOk G d oa sb fs os ds cs && (cs.isEmpty || ks.all (!·.among))
  | _, _, _ => false

/-- Every pair of the operands' clauses merges into a clause of the result. -/
def MergeOk (G : NormalGraph ι) (d : List PropKey) (A B R : List ι) : Bool :=
  G.plainTy A && G.plainTy B &&
    (expand G A).all fun ca => (expand G B).all fun cb => (expand G R).any fun cr =>
      MergeClause G d ca cb cr

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

open Classical in
/-- The family a merge's allocation stores under an entry: the result's
field type, or its optional field's, or the type of its index `ix` for a key
one of the index's classes admits, or, for a key the result does not state,
exactly the value copied. -/
noncomputable def entryFam (G : NormalGraph ι) (fs : List (PropKey × List ι))
    (os : List (OptionalField (List ι))) (ix : List IndexKeys × List ι) (e : PropKey × Tm) : Fam :=
  match fs.lookup e.1 with
  | some T => meaning G T
  | none => match os.find? (·.key == e.1) with
    | some q => meaning G q.type
    | none => if ∃ K ∈ ix.1, K.Admits e.1 then meaning G ix.2 else fun _ _ u => u = e.2

theorem entryFam_adm (G : NormalGraph ι) (fs os ix) (e : PropKey × Tm) : Adm (entryFam G fs os ix e) := by
  unfold entryFam
  split
  · exact setSem_adm (normalDenote_adm G) _
  · split
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
  /-- What either side gives under a key an index class admits. -/
  classA : ∀ K T, oa.classWithinA K T = true → ∀ k v, K.Admits k → pa.lookup k = some v →
    meaning G T p (below W) v
  classB : ∀ K T, sb.classWithin G d K T = true → ∀ k v, K.Admits k → qs.lookup k = some v →
    meaning G T p (below W) v

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
  classA _ _ hc _ _ hk hv := acc_class hfa hok hp hc hk hv
  classB _ _ hc _ _ hk hv := src_class hfb hok hq hc hk hv

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
  classA _ _ hc _ _ hk hv := acc_class hfa hok hp hc hk hv
  classB _ _ _ _ _ _ hv := by simp [List.lookup] at hv

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
states at their types, the keys its index admits at the index's type, and
every other at exactly the value copied. The result is a record (`cr` a
`refs` clause) or a dictionary over the index `ds`, `cs` at `V`. -/
theorem merge_finish {G : NormalGraph ι} {d : List PropKey} {oa : Obj ι} {sb : Src ι} {p : Nat}
    {W : WorldT (p + 1)} {h : Heap} {va vb : Val} {pa qs : List (PropKey × Tm)}
    (hadm : WorldAdm W) (hok : HeapOk (p + 1) W h) (hs : Sides G d oa sb p W pa qs)
    (hpn : (pa.map Prod.fst).Nodup) (hqn : (qs.map Prod.fst).Nodup)
    (hva : isVal va = true) (hvb : isVal vb = true)
    (hparts : mergeParts h d va vb = some (mergeData pa qs))
    {R : List ι} {cr : Clause (List ι)} {fs : List (PropKey × List ι)}
    {os : List (OptionalField (List ι))} {ks : List KeyBound}
    {ds cs : List (IndexKeys × List ι)} {V : List ι}
    (hcr : cr ∈ expand G R)
    (hshape : cr = .refs fs [] [] os [] ks ∨ (cr = .dict fs [] [] ds os [] ks cs ∧ ds ++ cs ≠ []))
    (hnd : (fs.map Prod.fst ++ os.map (·.key)).Nodup)
    (hfs : ∀ q ∈ fs, (sb.sure d q.1 q.2 || (oa.sureA q.1 q.2 && sb.within d q.1 q.2)) = true)
    (hos : ∀ q ∈ os, (oa.withinA q.key q.type && sb.within d q.key q.type) = true)
    (hpr : (os.isEmpty || oa.neverA CallArguments.protoField) = true)
    (hks : ∀ K ∈ ks, boundOk oa sb d K = true)
    (hV : ∀ x ∈ ds ++ cs, x.2 = V)
    (hcls : ∀ x ∈ ds ++ cs, ∀ k v, x.1.Admits k → (mergeData pa qs).lookup k = some v →
      meaning G V p (below W) v)
    (hnp : ds ++ cs ≠ [] → (mergeData pa qs).lookup CallArguments.protoField = none)
    (hfd : ∀ q ∈ fs, (∀ x ∈ cs, x.1.Admits q.1 → q.2 = V) ∧
      (∀ x ∈ ds, x.1.Admits q.1 → inLabels q.2 V = true))
    (hod : ∀ q ∈ os, (∀ x ∈ cs, x.1.Admits q.key → q.type = V) ∧
      (∀ x ∈ ds, x.1.Admits q.key → inLabels q.type V = true)) :
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
  let ix : List IndexKeys × List ι := ((ds ++ cs).map Prod.fst, V)
  generalize mergeData pa qs = ps at hparts hnodup hF hO hP hK hcls hnp
  have hvals : ∀ v ∈ ps.map Prod.snd, isVal v = true := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
    rcases mergeParts_vals hparts e he with h1 | ⟨-, h2⟩
    · rw [h1]; rfl
    · exact h2
  -- The family an entry's location is given, and why its value meets it.
  have hfam : ∀ e ∈ ps, entryFam G fs os ix e p (below W) e.2 := by
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
      | none =>
        simp only [entryFam, hT, hq]
        split
        · rename_i hadmits
          obtain ⟨K, hK, hadmK⟩ := hadmits
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hK
          exact hcls x hx e.1 e.2 hadmK hl
        · rfl
  refine Or.inr ⟨below W, h, .makeAt .absent (ps.map Prod.fst) (ps.map Prod.snd), WExt_refl _,
    WorldAdm_trunc _ hadm, Step.mergeV hva hvb hparts, HeapOk_trunc p W h hok, ?_⟩
  apply make_fields_rule (As := ps.map (entryFam G fs os ix))
    (fun A hA => by obtain ⟨e, -, rfl⟩ := List.mem_map.mp hA; exact entryFam_adm G fs os ix e)
    p (below W) h .absent (ps.map Prod.fst) (ps.map Prod.snd) hnodup (by simp) (by simp) hvals
    (WorldAdm_trunc _ hadm) (HeapOk_trunc p W h hok)
  · intro q hq
    rw [List.zip_map', List.mem_map] at hq
    obtain ⟨e, he, rfl⟩ := hq
    exact hfam e he
  · intro j hj U hx hrec
    -- The pair each entry contributes to the record the allocation meets.
    have hzip : ∀ e ∈ ps, (e.1, entryFam G fs os ix e) ∈
        (ps.map Prod.fst).zip (ps.map (entryFam G fs os ix)) := by
      intro e he
      rw [List.zip_map', List.mem_map]
      exact ⟨e, he, rfl⟩
    -- The location under a key the object owns, and what its contract is.
    have hat : ∀ f l, (slots h.length (ps.map Prod.fst)).lookup f = some l →
        ∃ v c, ps.lookup f = some v ∧ lookup U l = some c ∧
          ∀ i (hi : i < j) (U' : WorldT i) u, c i hi U' u ↔ entryFam G fs os ix (f, v) i U' u := by
      intro f l hl
      have hmem := mem_of_lookup_slots hl
      obtain ⟨v, hv⟩ := lookup_isSome hmem
      have he := mem_of_lookup hv
      obtain ⟨fl, l', c, hfl, hl', hU, hag⟩ := recT_at (hzip _ he) hrec
      cases hfl
      rw [hl] at hl'; cases hl'
      exact ⟨v, c, hv, hU, hag⟩
    have hrefs : ReferenceConjunctions.refsT (ReferenceConjunctions.famsOf (meaning G) fs) [] j U
        (.objAt (slots h.length (ps.map Prod.fst)) .absent) := by
      refine ⟨⟨_, rfl, ?_⟩, by simp⟩
      intro f F hm
      obtain ⟨T, hT, rfl⟩ := ReferenceConjunctions.mem_famsOf.mp hm
      obtain ⟨v, hv, -⟩ := hF (f, T) hT
      have he := mem_of_lookup hv
      obtain ⟨fl, l, c, hfl, hl, hU, hag⟩ := recT_at (hzip _ he) hrec
      cases hfl
      have : entryFam G fs os ix (f, v) = meaning G T := by
        simp [entryFam, lookup_of_mem hfn hT]
      exact ⟨l, c, hl, hU, fun i hi U' u => (hag i hi U' u).trans (by rw [this])⟩
    have hviews : viewT (ReferenceConjunctions.famsOf (meaning G) []) j U
        (.objAt (slots h.length (ps.map Prod.fst)) .absent) := by
      intro f F hm; simp [ReferenceConjunctions.famsOf] at hm
    have hopt : optT (os.map (·.map (meaning G))) j U
        (.objAt (slots h.length (ps.map Prod.fst)) .absent) := by
      refine ⟨_, rfl, ?_, ?_⟩
      · intro o ho _
        have hne : os ≠ [] := by
          intro he; subst he; simp at ho
        apply lookup_slots_none
        intro hm
        obtain ⟨v, hv⟩ := lookup_isSome hm
        rw [hP hne] at hv; cases hv
      · intro o ho l hl
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
        obtain ⟨v, c, hv, hU, hag⟩ := hat _ l hl
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
        have : entryFam G fs os ix (q'.key, v) = meaning G q'.type := by
          simp only [entryFam, hdisj q' hq, hf]
        refine ⟨c, hU, fun i hi U' u => ?_⟩
        have hiff : c i hi U' u ↔ meaning G q'.type i U' u :=
          (hag i hi U' u).trans (by simp only [OptionalField.map]; rw [this])
        exact ⟨hiff.mp, fun _ => hiff.mpr⟩
    have hbounds : ∀ K ∈ ks, ownKeysT K j U (.objAt (slots h.length (ps.map Prod.fst)) .absent) := by
      intro K hKm
      exact ⟨_, rfl, fun q hq => hK K hKm q.1 (slots_fst_mem hq)⟩
    refine (expand_sem G R (plain_of_mem_expand hcr) j U _).mpr ⟨_, hcr, ?_⟩
    rcases hshape with rfl | ⟨rfl, hne⟩
    · simp only [clauseSem, semWithArgs]
      exact ⟨hrefs, hviews, hopt, MethodMembers.methodT_nil _ _ _, hbounds⟩
    · simp only [clauseSem, semWithArgs]
      -- What a location under a key an index class admits holds: exactly
      -- `V` where a writable index admits it, and within `V` in any case.
      have hkey : ∀ x ∈ ds ++ cs, ∀ f l, (slots h.length (ps.map Prod.fst)).lookup f = some l →
          x.1.Admits f → ∃ c : Ctr j, lookup U l = some c ∧
            ((∀ y ∈ cs, y.1.Admits f →
                ∀ i (hi : i < j) (U' : WorldT i) u, c i hi U' u ↔ meaning G V i U' u) ∧
             ∀ i (hi : i < j) (U' : WorldT i) u, c i hi U' u → meaning G V i U' u) := by
        intro x hx f l hl hxf
        obtain ⟨v, c, hv, hU, hag⟩ := hat f l hl
        refine ⟨c, hU, ?_⟩
        cases hT : fs.lookup f with
        | some T =>
          have hq := hfd (f, T) (mem_of_lookup hT)
          simp only at hq
          have hfam : entryFam G fs os ix (f, v) = meaning G T := by simp [entryFam, hT]
          refine ⟨fun y hy hyf i hi U' u => ?_, fun i hi U' u hc => ?_⟩
          · rw [hag i hi U' u, hfam, hq.1 y hy hyf]
          · rw [hag i hi U' u, hfam] at hc
            rcases List.mem_append.mp hx with hx | hx
            · exact inLabels_sound (hq.2 x hx hxf) hc
            · rw [hq.1 x hx hxf] at hc; exact hc
        | none =>
          cases hf : os.find? (·.key == f) with
          | some q =>
            have hqk : q.key = f := by simpa using List.find?_some hf
            have hq := hod q (List.mem_of_find?_eq_some hf)
            rw [hqk] at hq
            have hfam : entryFam G fs os ix (f, v) = meaning G q.type := by
              simp only [entryFam, hT, hf]
            refine ⟨fun y hy hyf i hi U' u => ?_, fun i hi U' u hc => ?_⟩
            · rw [hag i hi U' u, hfam, hq.1 y hy hyf]
            · rw [hag i hi U' u, hfam] at hc
              rcases List.mem_append.mp hx with hx | hx
              · exact inLabels_sound (hq.2 x hx hxf) hc
              · rw [hq.1 x hx hxf] at hc; exact hc
          | none =>
            have hfam : entryFam G fs os ix (f, v) = meaning G V := by
              simp only [entryFam, hT, hf]
              rw [if_pos ⟨x.1, List.mem_map_of_mem hx, hxf⟩]
            refine ⟨fun y hy hyf i hi U' u => ?_, fun i hi U' u hc => ?_⟩
            · rw [hag i hi U' u, hfam]
            · rw [hag i hi U' u, hfam] at hc; exact hc
      have hnoproto : (slots h.length (ps.map Prod.fst)).lookup CallArguments.protoField = none := by
        apply lookup_slots_none
        intro hm
        obtain ⟨v, hv⟩ := lookup_isSome hm
        rw [hnp hne] at hv; cases hv
      refine ⟨hrefs, hviews, ⟨fun x hx => ⟨_, rfl, hnoproto, fun f l hl hxf => ?_⟩,
        fun x hx => ⟨_, rfl, hnoproto, fun f l hl hxf => ?_⟩⟩, hopt, MethodMembers.methodT_nil _ _ _,
        hbounds⟩
      · obtain ⟨c, hU, -, himp⟩ := hkey x (List.mem_append_left _ hx) f l hl hxf
        rw [hV x (List.mem_append_left _ hx)]
        exact ⟨c, hU, himp⟩
      · obtain ⟨c, hU, hiff, -⟩ := hkey x (List.mem_append_right _ hx) f l hl hxf
        rw [hV x (List.mem_append_right _ hx)]
        exact ⟨c, hU, hiff x hx hxf⟩

/-- The conditions `FieldsOk` states, as `merge_finish` takes them. -/
theorem fieldsOk_facts {d : List PropKey} {oa : Obj ι} {sb : Src ι} {fs : List (PropKey × List ι)}
    {os : List (OptionalField (List ι))} {ks : List KeyBound} (h : FieldsOk d oa sb fs os ks = true) :
    (fs.map Prod.fst ++ os.map (·.key)).Nodup ∧
    (∀ q ∈ fs, (sb.sure d q.1 q.2 || (oa.sureA q.1 q.2 && sb.within d q.1 q.2)) = true) ∧
    (∀ q ∈ os, (oa.withinA q.key q.type && sb.within d q.key q.type) = true) ∧
    (os.isEmpty || oa.neverA CallArguments.protoField) = true ∧
    (∀ K ∈ ks, boundOk oa sb d K = true) := by
  simp only [FieldsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hnd, hfs⟩, hos⟩, hpr⟩, hks⟩ := h
  exact ⟨hnd, hfs, fun q hq => by simpa using hos q hq, hpr, hks⟩

/-- The conditions `DictOk` states, as `merge_finish` takes them. -/
theorem dictOk_facts {G : NormalGraph ι} {d : List PropKey} {oa : Obj ι} {sb : Src ι}
    {fs : List (PropKey × List ι)} {os : List (OptionalField (List ι))}
    {ds cs : List (IndexKeys × List ι)} (h : DictOk G d oa sb fs os ds cs = true) :
    ∃ V, ds ++ cs ≠ [] ∧ oa.neverA CallArguments.protoField = true ∧
      (∀ x ∈ ds ++ cs, x.2 = V ∧ oa.classWithinA x.1 V = true ∧ sb.classWithin G d x.1 V = true) ∧
      (∀ q ∈ fs, (∀ x ∈ cs, x.1.Admits q.1 → q.2 = V) ∧
        (∀ x ∈ ds, x.1.Admits q.1 → inLabels q.2 V = true)) ∧
      (∀ q ∈ os, (∀ x ∈ cs, x.1.Admits q.key → q.type = V) ∧
        (∀ x ∈ ds, x.1.Admits q.key → inLabels q.type V = true)) := by
  unfold DictOk at h
  split at h
  · cases h
  · rename_i K V hhead
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, List.any_eq_false] at h
    obtain ⟨⟨⟨hnp, hix⟩, hfs⟩, hos⟩ := h
    refine ⟨V, ?_, hnp, fun x hx => ?_, fun q hq => ⟨fun x hx hxa => ?_, fun x hx hxa => ?_⟩,
      fun q hq => ⟨fun x hx hxa => ?_, fun x hx hxa => ?_⟩⟩
    · intro he; rw [he] at hhead; cases hhead
    · obtain ⟨⟨h1, h2⟩, h3⟩ := hix x hx
      exact ⟨h1, h2, h3⟩
    · rcases (hfs q hq).1 with h1 | h1
      · exact absurd (IndexKeys.may_of_admits hxa) (by simpa using h1 x hx)
      · exact h1
    · rcases (hfs q hq).2 with h1 | h1
      · exact absurd (IndexKeys.may_of_admits hxa) (by simpa using h1 x hx)
      · exact h1
    · rcases (hos q hq).1 with h1 | h1
      · exact absurd (IndexKeys.may_of_admits hxa) (by simpa using h1 x hx)
      · exact h1
    · rcases (hos q hq).2 with h1 | h1
      · exact absurd (IndexKeys.may_of_admits hxa) (by simpa using h1 x hx)
      · exact h1

/-- The two sides of a merge, read through their clauses. -/
theorem merge_sides {G : NormalGraph ι} {d : List PropKey} {ca cb : Clause (List ι)}
    {oa : Obj ι} {sb : Src ι} (hoa : objOf ca = some oa) (hsrc : srcOf cb = some sb)
    {p : Nat} {W : WorldT (p + 1)} {h : Heap} {va vb : Val} (hok : HeapOk (p + 1) W h)
    (hsa : clauseSem G ca (p + 1) W va) (hsb : clauseSem G cb (p + 1) W vb) :
    ∃ pa qs, (pa.map Prod.fst).Nodup ∧ (qs.map Prod.fst).Nodup ∧ isVal va = true ∧
      isVal vb = true ∧ mergeParts h d va vb = some (mergeData pa qs) ∧
      Sides G d oa sb p W pa qs := by
  obtain ⟨fa, rfl, hfa⟩ := objFacts_of_sem hoa hsa
  have hp : ownAll h (.objAt fa .absent) = some (firstKeys
      ((fa.filter (·.1 != arrayStoreKey)).map (fun p => (p.1, heapVal h p.2)))) := rfl
  unfold srcOf at hsrc
  split at hsrc
  · rename_i hempty
    cases hsrc
    obtain ⟨hq, hvb⟩ := emptyClause_ownData hempty hsb h
    exact ⟨_, [], ownAll_nodup hp, by simp, rfl, hvb, by simp [mergeParts, hp, hq],
      sides_prim hfa hok hp⟩
  · obtain ⟨ob, hob, rfl⟩ := Option.map_eq_some_iff.mp hsrc
    obtain ⟨fb, rfl, hfb⟩ := objFacts_of_sem hob hsb
    have hq : ownData h (.objAt fb .absent) = some (firstKeys
        ((fb.filter (copiedKey ·.1)).map (fun p => (p.1, heapVal h p.2)) ++ storeData h fb)) := rfl
    exact ⟨_, _, ownAll_nodup hp,
      (ownData_nodup hq).sublist (List.Sublist.map _ List.filter_sublist), rfl, rfl,
      by simp [mergeParts, hp, hq], sides_obj hfa hfb hok hp hq⟩

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
    obtain ⟨pa, qs, hpn, hqn, hva, hvb, hparts, hs⟩ := merge_sides (d := d) hoa hsrc hok hsa hsb
    obtain ⟨hnd, hfs, hos, hpr, hks⟩ := fieldsOk_facts hmc
    exact merge_finish (ds := []) (cs := []) (V := []) hadm hok hs hpn hqn hva hvb hparts hcr
      (.inl rfl) hnd hfs hos hpr hks (by simp) (by simp) (by simp)
      (fun _ _ => ⟨by simp, by simp⟩) (fun _ _ => ⟨by simp, by simp⟩)
  · rename_i oa sb fs ds os ks cs hoa hsrc
    obtain ⟨pa, qs, hpn, hqn, hva, hvb, hparts, hs⟩ := merge_sides (d := d) hoa hsrc hok hsa hsb
    simp only [Bool.and_eq_true] at hmc
    obtain ⟨⟨hmf, hmd⟩, -⟩ := hmc
    obtain ⟨hnd, hfs, hos, hpr, hks⟩ := fieldsOk_facts hmf
    obtain ⟨V, hne, hnp, hix, hfd, hod⟩ := dictOk_facts hmd
    refine merge_finish (V := V) hadm hok hs hpn hqn hva hvb hparts hcr (.inr ⟨rfl, hne⟩) hnd hfs
      hos hpr hks (fun x hx => (hix x hx).1) ?_ ?_ hfd hod
    · intro x hx k v hk hv
      rw [lookup_mergeData] at hv
      cases hq : qs.lookup k with
      | some w =>
        rw [hq, Option.some_or] at hv; cases hv
        exact hs.classB _ _ (hix x hx).2.2 k _ hk hq
      | none =>
        rw [hq, Option.none_or] at hv
        exact hs.classA _ _ (hix x hx).2.1 k v hk hv
    · intro _
      rw [lookup_mergeData, hs.proto, Option.none_or]
      exact hs.neverA _ hnp
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
def mergeResult (G : NormalGraph ι) (d : List PropKey) (ca cb : Clause (List ι)) :
    Option (Clause (List ι)) := do
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
  let record : Clause (List ι) := .refs fields [] [] optional [] bound
  -- Where a side states an index, the result states one over the same
  -- classes, writable, at what either side and the fields those classes may
  -- admit hold, where the rule admits it; otherwise the record.
  let bIndexes := match sb with | .prim => [] | .obj ob => ob.indexes
  let classes := (oa.indexes.map Prod.fst ++ bIndexes.map Prod.fst).eraseDups
  if classes.isEmpty then pure record else
  let admitted (k : PropKey) := classes.any (·.may k)
  let V := (oa.indexes.flatMap (·.2) ++ bIndexes.flatMap (·.2) ++
    (fields.filter (admitted ·.1)).flatMap (·.2) ++
    (optional.filter (admitted ·.key)).flatMap (·.type)).eraseDups
  let ix := classes.map (·, V)
  let dict : Clause (List ι) :=
    .dict (fields.map fun (k, T) => if admitted k then (k, V) else (k, T)) [] [] ix
      (optional.map fun q => if admitted q.key then { q with type := V } else q) []
      (bound.filter (!·.among)) ix
  pure (if MergeClause G d ca cb dict then dict else record)

#print axioms merge_values_safe

end Verification.Model.ObjectMerge
