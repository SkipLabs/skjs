import Verification.Model.Programs.PointClaims

/-! Refinement of immutable environment slots under observed Boolean or tag outcomes.
Heap contents are not refined: the witness concerns the tested value,
not a retained observation about a mutable location. -/
namespace Verification.Model.BranchRefinement
open ProgramTyping PositiveGraphs PositiveRules PositiveNormalization PointClaims
open PositiveCertificates (InstanceImageCheck finiteInstanceImages)

def booleanMember [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) (q : Bool) : Bool :=
  (expand G A).any fun c => match c with
    | .bool => true
    | .boolLit b => b == q
    | _ => false

def onlyBoolean (G : NormalGraph ι) (A : Ty ι) : Bool :=
  G.plainTy A && (expand G A).all fun c => match c with
    | .bool | .boolLit _ => true
    | _ => false

theorem booleanMember_sound [DecidableEq ι] {G : NormalGraph ι} {A q}
    (h : booleanMember G A q = true) (n W) :
    meaning G A n W (if q then .tru else .fls) := by
  obtain ⟨c,hc,h⟩ := List.any_eq_true.mp h
  have hrec : c.record = false := by cases c <;> simp_all [Clause.record]
  refine expand_sem_mpr ⟨c,expand_sub hc,?_,realmInvariant_of_not_record hrec _ _ _⟩
  cases c <;> simp_all [semWithArgs, boolT]

theorem onlyBoolean_sound {G : NormalGraph ι} {A n W v}
    (h : onlyBoolean G A = true) (hv : meaning G A n W v) :
    v = .tru ∨ v = .fls := by
  simp only [onlyBoolean, Bool.and_eq_true] at h
  rw [expand_sem G A h.1] at hv
  obtain ⟨c,hc,hv,-⟩ := hv
  have h := List.all_eq_true.mp h.2 c hc
  cases c <;> simp_all [semWithArgs, boolT]

/-- Drop only labels whose every clause contradicts the observed tag. A mixed
label is retained intact: this does not assume that labels have uniform shapes.
A parameter or scheme row has no clauses to contradict it, and is retained. -/
def tagSlice (G : NormalGraph ι) (A : Ty ι) (tag : Tag) (q : Bool) : Ty ι :=
  A.filter fun a => !(G.plain a && (expand G [a]).all fun c => (tagClause tag c) == some (!q))

theorem tagSlice_sound {G : NormalGraph ι} {A tag q n W v}
    (hv : meaning G A n W v) (hq : tagHolds tag v = q ∨ protoFree tag v = false) :
    meaning G (tagSlice G A tag q) n W v := by
  obtain ⟨a, ha, hv⟩ := hv
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hv⟩
  cases h : (G.plain a && (expand G [a]).all fun c => (tagClause tag c) == some (!q)) with
  | false => rfl
  | true =>
    simp only [Bool.and_eq_true] at h
    have hop : Answers G [a] tag (!q) := by
      refine ⟨by simp [NormalGraph.plainTy, h.1], fun c hc => ?_⟩
      exact beq_iff_eq.mp (List.all_eq_true.mp h.2 c hc)
    have he := answers_weak hop (show meaning G [a] n W v from ⟨a, by simp, hv⟩) hq
    cases q <;> simp at he

/-! ### Refinement by an observed field

A tag observed on a value read from a field of an object excludes each label
whose record contract for that field answers the other way: the field's
location holds the read value, and its world contract, fixed at allocation,
admits only values of the field's type. The exclusion concerns the object's
label, which is timeless; what the field holds later is not claimed. -/

/-- Whether a record clause fixes the field `f` at a type answering `tag`
with `q`: an invariant field or a readonly view. -/
def fieldAnswers (G : NormalGraph ι) (c : Clause (Ty ι)) (f : PropKey) (tag : Tag) (q : Bool) : Bool :=
  match c with
  | .refs a _ vs _ _ _ => (a ++ vs).any fun p =>
      decide (p.1 = f) && G.plainTy p.2 && (expand G p.2).all fun c => tagClause tag c == some q
  | _ => false

/-- The labels of `A` an object may still have once the value of its field
`f` answered `tag` with `q`. A label is dropped only where every clause of it
fixes `f` at a type answering the other way. -/
def fieldSlice (G : NormalGraph ι) (A : Ty ι) (f : PropKey) (tag : Tag) (q : Bool) : Ty ι :=
  A.filter fun a => !(G.plain a && (expand G [a]).all fun c => fieldAnswers G c f tag (!q))

/-- The value in a record's field location is of the field's type, one level
down: its contract says so, and a heap meeting the world holds it. -/
theorem field_value {G : NormalGraph ι} {c : Clause (Ty ι)} {f : PropKey} {K : Ty ι}
    {n W h v flds code l u}
    (hK : match c with
      | .refs a _ vs _ _ _ => (f, K) ∈ a ++ vs
      | _ => False)
    (hv : semWithArgs (meaning G) (argMeaning G) c (n+1) W v) (hh : HeapOk (n+1) W h)
    (hl : v = .objAt flds code) (hf : flds.lookup f = some l) (hu : h[l]? = some u) :
    meaning G K n (trunc n (Nat.le_succ n) W) u := by
  cases c with
  | refs a bs vs os ms ks =>
    simp only at hK
    have take : ∀ (c' : Ctr (n+1)), lookup W l = some c' →
        (∀ (W' : WorldT n) (w : Val), c' n (Nat.lt_succ_self n) W' w → meaning G K n W' w) →
        meaning G K n (trunc n (Nat.le_succ n) W) u := by
      intro c' hc' himp
      obtain ⟨u', hu', hall⟩ := hh.2 l c' hc'
      rw [hu] at hu'
      cases hu'
      exact himp _ _ (hall n (Nat.lt_succ_self n))
    rcases List.mem_append.mp hK with hK | hK
    · obtain ⟨flds', hv', hall⟩ := hv.1.1
      rw [hl] at hv'
      cases hv'
      obtain ⟨l', c', hl', hc', hag⟩ := hall f (meaning G K) (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩)
      rw [hf] at hl'
      cases hl'
      exact take c' hc' fun W' w hw => (hag n (Nat.lt_succ_self n) W' w).mp hw
    · obtain ⟨flds', l', c', hv', hl', hc', himp⟩ :=
        hv.2.1 f (meaning G K) (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩)
      rw [hl] at hv'
      cases hv'
      rw [hf] at hl'
      cases hl'
      exact take c' hc' fun W' w hw => himp n (Nat.lt_succ_self n) W' w hw
  | _ => exact hK.elim

theorem fieldSlice_sound {G : NormalGraph ι} {A : Ty ι} {f tag q n W h v flds code l u}
    (hv : meaning G A (n+1) W v) (hh : HeapOk (n+1) W h)
    (hl : v = .objAt flds code) (hf : flds.lookup f = some l) (hu : h[l]? = some u)
    (hq : tagHolds tag u = q ∨ protoFree tag u = false) : meaning G (fieldSlice G A f tag q) (n+1) W v := by
  obtain ⟨a, ha, hva⟩ := hv
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hva⟩
  cases hd : (G.plain a && (expand G [a]).all fun c => fieldAnswers G c f tag (!q)) with
  | false => rfl
  | true =>
    exfalso
    simp only [Bool.and_eq_true, List.all_eq_true] at hd
    have hm : meaning G [a] (n+1) W v := ⟨a, by simp, hva⟩
    rw [expand_sem G [a] (by simp [NormalGraph.plainTy, hd.1])] at hm
    obtain ⟨c, hc, hcv, -⟩ := hm
    have hans := hd.2 c hc
    cases c with
    | refs a' bs vs os ms ks =>
      simp only [fieldAnswers, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hans
      obtain ⟨⟨g, K⟩, hp, ⟨rfl, hplain⟩, hall⟩ := hans
      have hK : Answers G K tag (!q) :=
        ⟨hplain, fun c hc => beq_iff_eq.mp (List.all_eq_true.mp hall c hc)⟩
      have hu' := field_value (c := .refs a' bs vs os ms ks) (K := K) hp hcv hh hl hf hu
      have := answers_weak hK hu' hq
      cases q <;> simp at this
    | _ => simp [fieldAnswers] at hans

/-- An object lacking the key `f` is of no label every clause of which fixes
`f` (an invariant field or a view is a key the object has): the field slice
keeps its label, whatever the observation. This is what a read through a key
the object may lack (an optional link) needs where the key was absent. -/
theorem fieldSlice_absent {G : NormalGraph ι} {A : Ty ι} {f tag q n W v flds code}
    (hv : meaning G A (n+1) W v) (hl : v = .objAt flds code) (hf : flds.lookup f = none) :
    meaning G (fieldSlice G A f tag q) (n+1) W v := by
  obtain ⟨a, ha, hva⟩ := hv
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hva⟩
  cases hd : (G.plain a && (expand G [a]).all fun c => fieldAnswers G c f tag (!q)) with
  | false => rfl
  | true =>
    exfalso
    simp only [Bool.and_eq_true, List.all_eq_true] at hd
    have hm : meaning G [a] (n+1) W v := ⟨a, by simp, hva⟩
    rw [expand_sem G [a] (by simp [NormalGraph.plainTy, hd.1])] at hm
    obtain ⟨c, hc, hcv, -⟩ := hm
    have hans := hd.2 c hc
    cases c with
    | refs a' bs vs os ms ks =>
      simp only [fieldAnswers, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hans
      obtain ⟨⟨g, K⟩, hp, ⟨rfl, _⟩, _⟩ := hans
      rcases List.mem_append.mp hp with hK | hK
      · obtain ⟨flds', hv', hall⟩ := hcv.1.1
        rw [hl] at hv'
        cases hv'
        obtain ⟨l', _, hl', _⟩ := hall g (meaning G K) (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩)
        rw [hf] at hl'
        cases hl'
      · obtain ⟨flds', l', _, hv', hl', _⟩ :=
          hcv.2.1 g (meaning G K) (ReferenceConjunctions.mem_famsOf.mpr ⟨K, hK, rfl⟩)
        rw [hl] at hv'
        cases hv'
        rw [hf] at hl'
        cases hl'
    | _ => simp [fieldAnswers] at hans

/-! ### Presence of an optional key

An object owns its keys from its allocation on: a key found present stays
present. An optional field of a record clause is, on an object that has the
key, a field of the clause proper: invariant where the key is writable, a view
where it is readonly (`optT`, `SlotContract`). -/

/-- The record clause `c` with its optional key `k` taken as present. Other
clauses, and a record without that optional key, are unchanged. -/
def promote (k : PropKey) : Clause α → Clause α
  | .refs a bs vs os ms ks =>
    match os.find? (fun o => decide (o.key = k)) with
    | some o =>
      if o.readonly then .refs a bs (vs ++ [(k, o.type)]) os ms ks
      else .refs (a ++ [(k, o.type)]) bs vs os ms ks
    | none => .refs a bs vs os ms ks
  | c => c

/-- What a test or a read says of an object and a key: where it lacks the
key, it holds a prototype. An object of a record naming the key as optional
holds none where it lacks it (`optT`), so there it has the key. -/
def KeyFound (k : PropKey) (v : Tm) : Prop :=
  ∀ flds code, v = .objAt flds code → flds.lookup k = none →
    (flds.lookup CallArguments.protoField).isSome = true

theorem promote_sound {X : α → Fam} {P : α → ArgFam} {k : PropKey} {c : Clause α} {n W v}
    (hc : semWithArgs X P c n W v) (hk : KeyFound k v) :
    semWithArgs X P (promote k c) n W v := by
  cases c with
  | refs a bs vs os ms ks =>
    simp only [promote]
    split
    · rename_i o ho
      have hmem := List.mem_of_find?_eq_some ho
      have hkey : o.key = k := by simpa using List.find?_some ho
      obtain ⟨⟨⟨flds, hv, hrec⟩, hbs⟩, hview, hopt, hmeth, hkeys⟩ := hc
      subst hv
      have hmem' : o.map X ∈ os.map (·.map X) := List.mem_map.mpr ⟨o, hmem, rfl⟩
      obtain ⟨l, hl⟩ : ∃ l, flds.lookup k = some l := by
        cases hlk : flds.lookup k with
        | some l => exact ⟨l, rfl⟩
        | none =>
          have hnp := optT_no_proto hmem' hopt (by simpa [OptionalField.map, hkey] using hlk)
          have hp := hk flds .absent rfl hlk
          rw [hnp] at hp
          cases hp
      have hl' : flds.lookup (o.map X).key = some l := by simpa [OptionalField.map, hkey] using hl
      obtain ⟨c', hw, hsc⟩ := optT_present hmem' hopt hl'
      cases hro : o.readonly
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨⟨⟨flds, rfl, ?_⟩, hbs⟩, hview, hopt, hmeth, hkeys⟩
        intro f T hm
        simp only [ReferenceConjunctions.famsOf, List.map_append, List.mem_append,
          List.map_cons, List.map_nil, List.mem_singleton] at hm
        rcases hm with hm | hm
        · exact hrec f T hm
        · cases hm
          refine ⟨l, c', hl, hw, fun j hj W' u => ⟨(hsc j hj W' u).1, ?_⟩⟩
          exact (hsc j hj W' u).2 (by simp [OptionalField.map, hro])
      · simp only [↓reduceIte]
        refine ⟨⟨⟨flds, rfl, hrec⟩, hbs⟩, ?_, hopt, hmeth, hkeys⟩
        intro f T hm
        simp only [ReferenceConjunctions.famsOf, List.map_append, List.mem_append,
          List.map_cons, List.map_nil, List.mem_singleton] at hm
        rcases hm with hm | hm
        · exact hview f T hm
        · cases hm
          exact ⟨flds, l, c', rfl, hl, hw, fun j hj W' u hu => (hsc j hj W' u).1 hu⟩
    · exact hc
  | _ => exact hc

/-- Whether every member of `xs` is one of `ys`. -/
def within [DecidableEq β] (xs ys : List β) : Bool := xs.all fun x => decide (x ∈ ys)

theorem within_mem [DecidableEq β] {xs ys : List β} (h : within xs ys = true) {x} (hx : x ∈ xs) :
    x ∈ ys := of_decide_eq_true (List.all_eq_true.mp h x hx)

/-- A record clause asking no more than another: each of its operands is one
of the other's. Every part of a record clause's meaning is a statement about
each of its operands, so asking fewer is weaker. -/
def weaker [DecidableEq α] : Clause α → Clause α → Bool
  | .refs a bs vs os ms ks, .refs a' bs' vs' os' ms' ks' =>
    within a a' && within bs bs' && within vs vs' && within os os' && within ms ms' && within ks ks'
  | _, _ => false

theorem weaker_sound [DecidableEq α] {X : α → Fam} {P : α → ArgFam} {d c : Clause α} {n W v}
    (hw : weaker d c = true) (hc : semWithArgs X P c n W v) : semWithArgs X P d n W v := by
  cases d with
  | refs a bs vs os ms ks =>
    cases c with
    | refs a' bs' vs' os' ms' ks' =>
      simp only [weaker, Bool.and_eq_true] at hw
      obtain ⟨⟨⟨⟨⟨ha, hb⟩, hv⟩, ho⟩, hm⟩, hk⟩ := hw
      obtain ⟨⟨⟨flds, hvf, hrec⟩, hbs⟩, hview, hopt, hmeth, hkeys⟩ := hc
      refine ⟨⟨⟨flds, hvf, fun f T hmem => ?_⟩, fun B hB => ?_⟩, fun f T hmem => ?_, ?_,
        fun m hm' => ?_, fun K hK => hkeys K (within_mem hk hK)⟩
      · obtain ⟨i, hi, rfl⟩ := ReferenceConjunctions.mem_famsOf.mp hmem
        exact hrec f _ (ReferenceConjunctions.mem_famsOf.mpr ⟨i, within_mem ha hi, rfl⟩)
      · obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hB
        exact hbs _ (List.mem_map.mpr ⟨B', within_mem hb hB', rfl⟩)
      · obtain ⟨i, hi, rfl⟩ := ReferenceConjunctions.mem_famsOf.mp hmem
        exact hview f _ (ReferenceConjunctions.mem_famsOf.mpr ⟨i, within_mem hv hi, rfl⟩)
      · obtain ⟨flds', hv', hp, hf⟩ := hopt
        refine ⟨flds', hv', fun o hmo => ?_, fun o hmo => ?_⟩
        · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hmo
          exact hp _ (List.mem_map.mpr ⟨o', within_mem ho ho', rfl⟩)
        · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hmo
          exact hf _ (List.mem_map.mpr ⟨o', within_mem ho ho', rfl⟩)
      · obtain ⟨m', hm'', rfl⟩ := List.mem_map.mp hm'
        exact hmeth _ (List.mem_map.mpr ⟨m', within_mem hm hm'', rfl⟩)
    | _ => simp [weaker] at hw
  | _ => simp [weaker] at hw

/-- Every value of `A` that has the key `k` is one of `B`: each clause of `A`,
with `k` taken as present, asks at least what one clause of `B` does. -/
def promotes [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) (k : PropKey) : Bool :=
  G.plainTy A && (expand G A).all fun c => (expand G B).any fun d => weaker d (promote k c)

theorem promotes_sound [DecidableEq ι] {G : NormalGraph ι} {A B : Ty ι} {k : PropKey} {n W v}
    (hp : promotes G A B k = true) (hv : meaning G A n W v)
    (hk : KeyFound k v) : meaning G B n W v := by
  simp only [promotes, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hp
  obtain ⟨c, hc, hcv, hinv⟩ := (expand_sem G A hp.1 n W v).mp hv
  obtain ⟨d, hd, hw⟩ := hp.2 c hc
  have hdr : d.record = true ∧ c.record = true := by
    cases d <;> cases hpc : promote k c <;> simp [weaker, hpc] at hw
    all_goals
      refine ⟨rfl, ?_⟩
      cases c <;> simp_all [promote, Clause.record]
  exact expand_sem_mpr ⟨d, expand_sub hd, weaker_sound hw (promote_sound hcv hk),
    (realmInvariant_record hdr.2 hdr.1).mp hinv⟩

/-- A small, explicit vocabulary of observations established by execution. -/
inductive Observation where
  | boolean (value : Bool)
  | tag (test : Tag) (answer : Bool)

def Observation.holds : Observation → Tm → Prop
  | .boolean q, v => v = (if q then .tru else .fls)
  -- `key in o` on an object reading a prototype may answer either way.
  | .tag t q, v => tagHolds t v = q ∨ protoFree t v = false

/-- The durable refinement obligation. B is supplied; no canonical filtered
representation, join, or inferred invariant is required by this contract. -/
def ObservedSub (G : NormalGraph ι) (A B : Ty ι) (o : Observation) : Prop :=
  ∀ n W v, meaning G A n W v → o.holds v → meaning G B n W v

def isSubset : PositiveCertificates.Proof ι → Bool
  | .subset => true
  | _ => false

/-- Whether one clause of `B` holds every value a passed tag test admits:
`string` after `typeof x === "string"`, whatever `x` was before, `unknown`
included. Only the tests that name one primitive family do. -/
def tagMember (G : NormalGraph ι) (B : Ty ι) : Tag → Bool → Bool
  | .isStr, true => (expand G B).any fun c => match c with | .str => true | _ => false
  | .isNum, true => (expand G B).any fun c => match c with | .num => true | _ => false
  | .isBigint, true => (expand G B).any fun c => match c with | .bigint => true | _ => false
  | .isSymbol, true => (expand G B).any fun c => match c with | .symbol => true | _ => false
  | .isUndef, true => (expand G B).any fun c => match c with | .undef => true | _ => false
  | .isNul, true => (expand G B).any fun c => match c with | .nul => true | _ => false
  | .isBool, true => (expand G B).any fun c => match c with | .bool => true | _ => false
  -- Equality with one number other than a zero, or one string, holds of that
  -- value alone.
  | .numEq b, true => b &&& 0x7fffffffffffffff != 0 &&
      (expand G B).any fun c => match c with | .numLit b' => b' == b | _ => false
  | .strEq s, true => (expand G B).any fun c => match c with | .strLit s' => s' == s | _ => false
  | _, _ => false

theorem tagMember_sound {G : NormalGraph ι} {B : Ty ι} {t : Tag} {q : Bool}
    (hm : tagMember G B t q = true) {n W v} (hv : isVal v = true) (ht : tagHolds t v = q) :
    meaning G B n W v := by
  cases t <;> cases q <;> simp only [tagMember, Bool.false_eq_true] at hm
  case numEq.true b =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hm
    obtain ⟨c, hc, hk⟩ := List.any_eq_true.mp hm.2
    cases c <;> simp at hk
    subst hk
    cases v <;> simp [tagHolds, isVal] at ht hv
    rename_i bits
    simp only [numberEqual, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht.2 with h | h
    · subst h
      exact expand_sem_mpr ⟨_, expand_sub hc, by simp [semWithArgs], realmInvariant_of_not_record rfl _ _ _⟩
    · exact absurd h.2 hm.1
  case strEq.true s =>
    obtain ⟨c, hc, hk⟩ := List.any_eq_true.mp hm
    cases c <;> simp at hk
    subst hk
    cases v <;> simp [tagHolds, isVal] at ht hv
    subst ht
    exact expand_sem_mpr ⟨_, expand_sub hc, by simp [semWithArgs], realmInvariant_of_not_record rfl _ _ _⟩
  all_goals
    obtain ⟨c, hc, hk⟩ := List.any_eq_true.mp hm
    cases c <;> simp at hk
    cases v <;> simp [tagHolds, isVal] at ht hv <;>
      exact expand_sem_mpr ⟨_, expand_sub hc, by
        simp [semWithArgs, nulT, undefT, boolT, numT, strT, bigintT, symbolT],
        realmInvariant_of_not_record rfl _ _ _⟩

/-- A passed `hasKey` test finds its key present: `check` of the key. -/
def presentKey (t : Tag) (q : Bool) (check : PropKey → Bool) : Bool :=
  match t, q with
  | .hasKey k, true => check k
  | _, _ => false

/-- A passed `in` test found the key on the object's chain: the object's own,
or, where it lacks it, one its prototype chain holds. -/
theorem presentKey_sound {t : Tag} {q : Bool} {check : PropKey → Bool}
    (h : presentKey t q check = true) {v} (hv : tagHolds t v = q ∨ protoFree t v = false) :
    ∃ k, check k = true ∧ KeyFound k v := by
  cases t <;> cases q <;> simp only [presentKey, Bool.false_eq_true] at h
  rename_i k
  refine ⟨k, h, ?_⟩
  intro flds code he hl
  subst he
  rcases hv with hv | hv
  · simp [tagHolds, hl] at hv
  · simp only [protoFree, hl, Option.isSome_none, Bool.false_or, Option.isNone_iff_eq_none] at hv
    simpa [Option.isSome_iff_ne_none] using hv

/-! ### An array of the realm

`Array.isArray` finds that an object owns the store key. A record or
dictionary type is of objects meeting the realm's array invariant
(`PositiveGraphs.realmInvariant`): one owning the store key holds a possibly sparse store
and the realm's prototype and owns no key it provides. So where the test holds,
a member of such a type is a member of the realm's `sparse ReadonlyArray<unknown>`, the
array shape over a store of values (`realmArrayLabel`). -/

/-- A type every value meets: one of its rows holds `top`. -/
def valuesTy [DecidableEq ι] (G : NormalGraph ι) (T : Ty ι) : Bool :=
  T.any fun t => G.plain t && (G t).contains .top

theorem valuesTy_sound [DecidableEq ι] {G : NormalGraph ι} {T : Ty ι} (h : valuesTy G T = true)
    {n W v} (hv : topT n W v) : meaning G T n W v := by
  obtain ⟨t, ht, hp⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hp
  exact ⟨t, ht, (unfold_plain hp.1 n W v).mpr ⟨.top, hp.2, hv, realmInvariant_of_not_record rfl n W v⟩⟩

/-- A type holding every possibly sparse store of values: a readonly array store at a
type every value meets. -/
def storeOfValues [DecidableEq ι] (G : NormalGraph ι) (S : Ty ι) : Bool :=
  S.any fun s => G.plain s && (G s).any fun c => match c with
    | .list ⟨[], [], some T, true, .sparse⟩ [] => valuesTy G T
    | _ => false

theorem storeOfValues_sound [DecidableEq ι] {G : NormalGraph ι} {S : Ty ι}
    (h : storeOfValues G S = true) {n W v} (hv : anyStoreT n W v) : meaning G S n W v := by
  obtain ⟨s, hs, hp⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, List.any_eq_true] at hp
  obtain ⟨hplain, c, hc, hcv⟩ := hp
  refine ⟨s, hs, (unfold_plain hplain n W v).mpr ⟨c, hc, ?_, ?_⟩⟩
  · split at hcv
    · rename_i T
      obtain ⟨ls, rfl, hd, hlen, hbound, hreq, hopt, hrest⟩ := hv
      refine ⟨⟨ls, rfl, hd, by simp [tupleFams], by simp [tupleFams],
        fun i A hA => by simp [tupleFams] at hA, fun i A l hA => by simp [tupleFams] at hA, ?_⟩, by simp⟩
      intro i l hi hl
      obtain ⟨E, c', hE, hw, hag⟩ := hrest i l hi hl
      cases hE
      exact ⟨_, c', rfl, hw, fun j hj W' u => ⟨fun hu => valuesTy_sound hcv ((hag j hj W' u).1 hu),
        fun h => nomatch h⟩⟩
    · cases hcv
  · split at hcv
    · exact realmInvariant_of_not_record rfl n W v
    · cases hcv

/-- The realm's `readonly unknown[]`: a clause row holding the array shape
over a store of values, `ArrayProto` read at a type without parameters, and
the keys that prototype provides. -/
def realmArrayLabel [DecidableEq ι] (G : NormalGraph ι) (L : ι) : Bool :=
  match G.realm with
  | none => false
  | some r => realmFree G r.proto && G.plain L && match G L with
    | [.refs [] [] [(k, S), (p, P)] [] [] [K]] =>
      k == CallArguments.arrayStoreField && p == CallArguments.protoField && P == r.proto &&
        K == ⟨false, r.keys⟩ && storeOfValues G S
    | _ => false

/-- **An array of the realm.** A member of a record or dictionary clause that
owns the store key is a member of the realm's `sparse ReadonlyArray<unknown>`. -/
theorem realmArray_of_record [DecidableEq ι] {G : NormalGraph ι} {L : ι}
    (hL : realmArrayLabel G L = true) {c : Clause (Ty ι)} (hc : c.record = true) {n W v}
    (hinv : realmInvariant G (realmValues G) c n W v) (ha : tagHolds .isArray v = true) :
    meaning G [L] n W v := by
  unfold realmArrayLabel at hL
  cases hr : G.realm with
  | none => rw [hr] at hL; cases hL
  | some r =>
    rw [hr] at hL
    simp only [Bool.and_eq_true] at hL
    obtain ⟨⟨hfree, hplain⟩, hrow⟩ := hL
    split at hrow
    · rename_i k S p P K hGL
      simp only [Bool.and_eq_true, beq_iff_eq] at hrow
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hS⟩ := hrow
      -- The tested value is a plain object owning the store key.
      obtain ⟨flds, rfl, hst⟩ : ∃ flds, v = .objAt flds .absent ∧
          (flds.lookup CallArguments.arrayStoreField).isSome = true := by
        cases v with
        | objAt fs code =>
          cases code <;> simp [tagHolds] at ha
          exact ⟨fs, rfl, by simpa [CallArguments.arrayStoreField] using ha⟩
        | _ => simp [tagHolds] at ha
      have hinv' := hinv
      unfold realmInvariant at hinv'
      rw [hr] at hinv'
      simp only [hc, ite_true] at hinv'
      obtain ⟨hview, hkeys⟩ := hinv' flds rfl hst
      refine ⟨L, List.mem_singleton_self L, (unfold_plain hplain n W _).mpr
        ⟨.refs [] [] [(CallArguments.arrayStoreField, S), (CallArguments.protoField, r.proto)] [] []
          [⟨false, r.keys⟩], by rw [hGL]; simp, ?_, ?_⟩⟩
      · refine ⟨⟨⟨flds, rfl, fun f T hm => by simp [ReferenceConjunctions.famsOf] at hm⟩, by simp⟩,
          fun f T hm => ?_, by simpa [OptionalField.map] using optT_nil,
          MethodMembers.methodT_nil _ _ _, fun K hK => ?_⟩
        · simp only [ReferenceConjunctions.famsOf, List.map_cons, List.map_nil, List.mem_cons,
            Prod.mk.injEq, List.not_mem_nil, or_false] at hm
          rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · obtain ⟨flds', l, c', he, hl, hw, hag⟩ := hview CallArguments.arrayStoreField anyStoreT (by simp)
            exact ⟨flds', l, c', he, hl, hw, fun j hj W' u hu =>
              storeOfValues_sound hS (hag j hj W' u hu)⟩
          · obtain ⟨flds', l, c', he, hl, hw, hag⟩ := hview CallArguments.protoField (realmValues G r.proto) (by simp)
            exact ⟨flds', l, c', he, hl, hw, fun j hj W' u hu =>
              (realmFree_meaning hfree j W' u).mpr (hag j hj W' u hu)⟩
        · simp only [List.mem_singleton] at hK
          subst hK
          exact hkeys
      · exact (realmInvariant_record hc rfl).mp hinv
    · cases hrow

/-- Where `Array.isArray` holds, every label of the tested type is kept in
`B`, or is a clause row each clause of which is of no array or a record's,
whose members that are arrays `B`'s realm array label holds. -/
def arraySlice [DecidableEq ι] (G : NormalGraph ι) (A B : Ty ι) : Bool :=
  B.any (realmArrayLabel G) &&
    (tagSlice G A .isArray true).all fun a =>
      B.contains a || (G.plain a && (G a).all fun c => tagClause .isArray c == some false || c.record)

theorem arraySlice_sound [DecidableEq ι] {G : NormalGraph ι} {A B : Ty ι}
    (h : arraySlice G A B = true) {n W v} (hv : meaning G A n W v)
    (ha : tagHolds .isArray v = true) : meaning G B n W v := by
  simp only [arraySlice, Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨L, hLB, hL⟩, hall⟩ := h
  obtain ⟨a, haS, hva⟩ := tagSlice_sound (tag := .isArray) (q := true) hv (Or.inl ha)
  rcases Bool.or_eq_true_iff.mp (hall a haS) with hB | hrow
  · exact ⟨a, List.contains_iff_mem.mp hB, hva⟩
  · simp only [Bool.and_eq_true, List.all_eq_true] at hrow
    obtain ⟨c, hc, hcv, hinv⟩ := (unfold_plain hrow.1 n W v).mp hva
    rcases Bool.or_eq_true_iff.mp (hrow.2 c hc) with hno | hrec
    · have := tagClause_sound (beq_iff_eq.mp hno) hcv
      rw [ha] at this; cases this
    · obtain ⟨l, hl, hvl⟩ := realmArray_of_record hL hrec hinv ha
      cases List.mem_singleton.mp hl
      exact ⟨L, hLB, hvl⟩

/-- Sufficient implementations of ObservedSub. Whole-label filtering is only
an algorithm for the tag case, not the meaning of refinement. -/
def checkObservedSubUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (A B : Ty ι) (o : Observation) (p : PositiveCertificates.Proof ι) : Bool :=
  match o with
  | .boolean q => isSubset p && booleanMember G B q
  | .tag t q => PositiveCertificates.checkUsing G images (tagSlice G A t q) B p || (isSubset p && tagMember G B t q) ||
      (isSubset p && presentKey t q (promotes G (tagSlice G A t q) B)) ||
      (isSubset p && t == .isArray && q && arraySlice G A B)

theorem checkObservedSub_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {A B o p} (hc : checkObservedSubUsing G images A B o p = true) : ObservedSub G A B o := by
  intro n W v hv ho
  cases o with
  | boolean q =>
    simp only [checkObservedSubUsing, Bool.and_eq_true] at hc
    have hb := hc.2
    change v = (if q then .tru else .fls) at ho
    rw [ho]
    exact booleanMember_sound hb n W
  | tag t q =>
    simp only [checkObservedSubUsing, Bool.or_eq_true, Bool.and_eq_true] at hc
    rcases hc with ((hc | ⟨_, hm⟩) | ⟨_, hk⟩) | ⟨⟨⟨_, ht⟩, hq⟩, hs⟩
    · exact PositiveCertificates.acceptedUsing hc n W v (tagSlice_sound hv ho)
    · exact tagMember_sound hm (meaning_value hv).1 (ho.resolve_right (by
        cases t <;> simp [tagMember] at hm <;> simp [protoFree]))
    · obtain ⟨k, hp, hkey⟩ := presentKey_sound hk ho
      exact promotes_sound hp (tagSlice_sound hv ho) hkey
    · have ht := beq_iff_eq.mp ht
      subst ht; subst hq
      exact arraySlice_sound hs hv (ho.resolve_right (by simp [protoFree]))

/-- The finite image checker, the default. -/
abbrev checkObservedSub [DecidableEq ι] (G : NormalGraph ι) :=
  @checkObservedSubUsing _ _ G (finiteInstanceImages G)

/-- The field refinements a tag observation admits for other slots: each
object a current read link says the tested value was read from, and the
field it was read through. -/
def fieldRefinements [DecidableEq ι] (o : Observation) (fields : List (Nat × PropKey)) (A B : Ty ι)
    (j : Nat) (G : NormalGraph ι) (images : InstanceImageCheck G) (p : PositiveCertificates.Proof ι) :
    Bool :=
  match o with
  | .tag t q => fields.any fun (k, f) => k == j &&
      PositiveCertificates.checkUsing G images (fieldSlice G A f t q) B p
  | .boolean _ => false

/-- Whether an observation rules out `undefined`: a Boolean is not it, and a
tag answers it one way. -/
def excludesUndef : Observation → Bool
  | .boolean _ => true
  | .tag t q => tagHolds t .undef != q

theorem excludesUndef_sound {o : Observation} {v : Tm} (h : excludesUndef o = true)
    (ho : o.holds v) : v ≠ .undef := by
  rintro rfl
  cases o with
  | boolean q => cases q <;> simp [Observation.holds] at ho
  | tag t q =>
    simp only [excludesUndef, bne_iff_ne, ne_eq] at h
    rcases ho with ho | ho
    · exact h ho
    · simp [protoFree] at ho

/-- The promotions an observation admits for other slots: an object the
tested value was read from through an optional key (`optionals`), where the
observation rules out `undefined`, which is what a read of the key gives where
the object lacks it. The object then has the key, from then on. -/
def optionalRefinements [DecidableEq ι] (o : Observation) (optionals : List (Nat × PropKey)) (A B : Ty ι)
    (j : Nat) (G : NormalGraph ι) (p : PositiveCertificates.Proof ι) : Bool :=
  isSubset p && excludesUndef o && optionals.any fun (k, f) => k == j && promotes G A B f

/-- An observation no value of the tested type makes: a tag answer every
label contradicts, or a Boolean the type does not hold. The edge is then
never taken, and constrains nothing. -/
def impossible [DecidableEq ι] (G : NormalGraph ι) (A : Ty ι) : Observation → Bool
  | .tag t q => (tagSlice G A t q).isEmpty
  | .boolean q => G.plainTy A && (expand G A).all fun c =>
      c == .boolLit (!q) || tagClause .isBool c == some false

theorem impossible_sound [DecidableEq ι] {G : NormalGraph ι} {A o n W v}
    (h : impossible G A o = true) (hv : meaning G A n W v) (ho : o.holds v) : False := by
  cases o with
  | tag t q =>
    simp only [impossible, List.isEmpty_iff] at h
    obtain ⟨a, ha, _⟩ := tagSlice_sound hv ho
    rw [h] at ha
    cases ha
  | boolean q =>
    simp only [impossible, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨c, hc, hcv, -⟩ := (expand_sem G A h.1 n W v).mp hv
    change v = (if q then .tru else .fls) at ho
    subst ho
    rcases h.2 c hc with rfl | hb
    · cases q <;> simp [semWithArgs] at hcv
    · have := tagClause_sound hb hcv
      cases q <;> simp [tagHolds] at this

/-- One mapped-edge checker for all supported observations. Other slots use
ordinary subtype evidence, or, for an object the tested value was read from
(`fields`), subtype evidence from its field slice. The tested slot must
exist, even if forgotten. -/
def checkObservedUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G) (Γ Δ : List (Ty ι))
    (tested : Nat) (o : Observation) (mapping : Mapping) (ps : EdgeEvidence ι)
    (fields : List (Nat × PropKey) := []) (optionals : List (Nat × PropKey) := []) : Bool :=
  Γ[tested]?.isSome &&
  ((Γ[tested]?).any (impossible G · o) ||
  (match mapping with | none => true | some slots => slots.length == Δ.length) &&
  ps.length == Δ.length && (List.range Δ.length).all (fun j =>
    match Γ[slot mapping j]?, Δ[j]?, ps[j]? with
    | some A, some B, some p =>
      if slot mapping j == tested then checkObservedSubUsing G images A B o p
      else PositiveCertificates.checkUsing G images A B p ||
        fieldRefinements o (fields ++ optionals) A B (slot mapping j) G images p ||
        optionalRefinements o optionals A B (slot mapping j) G p
    | _, _, _ => false))

/-- The finite image checker, the default. -/
abbrev checkObserved [DecidableEq ι] (G : NormalGraph ι) :=
  @checkObservedUsing _ _ G (finiteInstanceImages G)

def ObservedCovers [DecidableEq ι] (G : NormalGraph ι) (Γ Δ : List (Ty ι))
    (tested : Nat) (o : Observation) (mapping : Mapping) (fields : List (Nat × PropKey) := [])
    (optionals : List (Nat × PropKey) := []) : Prop :=
  (∃ A, Γ[tested]? = some A ∧ ∀ n W v, meaning G A n W v → o.holds v → False) ∨
  ∀ j B, Δ[j]? = some B → ∃ A, Γ[slot mapping j]? = some A ∧
    (if slot mapping j = tested then ObservedSub G A B o
     else FamLe (meaning G A) (meaning G B) ∨
       (∃ t q f, o = .tag t q ∧ (slot mapping j, f) ∈ fields ++ optionals ∧
         FamLe (meaning G (fieldSlice G A f t q)) (meaning G B)) ∨
       ∃ f, (slot mapping j, f) ∈ optionals ∧ excludesUndef o = true ∧ promotes G A B f = true)

theorem checkObserved_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {Γ Δ i o mapping ps fields optionals}
    (h : checkObservedUsing G images Γ Δ i o mapping ps fields optionals = true) :
    ObservedCovers G Γ Δ i o mapping fields optionals := by
  simp only [checkObservedUsing, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at h
  rcases h.2 with hdead | h
  · left
    cases ht : Γ[i]? with
    | none => simp [ht] at hdead
    | some A =>
      rw [ht] at hdead
      exact ⟨A, rfl, fun n W v hv ho => impossible_sound (by simpa using hdead) hv ho⟩
  right
  intro j B hj
  have hc := h.2 j (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hj).1)
  rw [hj] at hc
  cases ha : Γ[slot mapping j]? with
  | none => simp [ha] at hc
  | some A =>
    cases hp : ps[j]? with
    | none => simp [ha,hp] at hc
    | some p =>
      refine ⟨A,rfl,?_⟩
      simp only [ha,hp] at hc
      by_cases he : slot mapping j = i
      · simp only [beq_iff_eq,he,↓reduceIte] at hc
        simp only [he,↓reduceIte]
        exact checkObservedSub_sound hc
      · simp only [beq_iff_eq,he,↓reduceIte,Bool.or_eq_true] at hc
        simp only [he,↓reduceIte]
        rcases hc with (hc | hc) | hc
        · exact .inl (PositiveCertificates.acceptedUsing hc)
        · right; left
          cases o with
          | boolean _ => simp [fieldRefinements] at hc
          | tag t q =>
            simp only [fieldRefinements, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨⟨k, f⟩, hk, rfl, hck⟩ := hc
            exact ⟨t, q, f, rfl, hk, PositiveCertificates.acceptedUsing hck⟩
        · right; right
          simp only [optionalRefinements, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨⟨_, hx⟩, ⟨k, f⟩, hk, rfl, hp⟩ := hc
          exact ⟨f, hk, hx, hp⟩

/-- A branch edge's environment, one level above the one it is used at: a
field slice needs the heap's contents at the field, which the world types one
level down. -/
theorem ObservedCovers.env [DecidableEq ι] {G : NormalGraph ι} {Γ Δ i o mapping fields optionals ρ n W h}
    (hc : ObservedCovers G Γ Δ i o mapping fields optionals) (he : EnvOk G Γ ρ (n+1) W)
    (ho : o.holds (ρ i)) (hh : HeapOk (n+1) W h)
    (hl : ∀ k f, (k, f) ∈ fields → ∃ flds c l, ρ k = .objAt flds c ∧ flds.lookup f = some l ∧
      h[l]? = some (ρ i))
    (hopt : ∀ k f, (k, f) ∈ optionals → ∃ flds c, ρ k = .objAt flds c ∧
      (flds.lookup f = none → ρ i = .undef) ∧ (∀ l, flds.lookup f = some l → h[l]? = some (ρ i))) :
    EnvOk G Δ (mapEnv mapping ρ) (n+1) W := by
  rcases hc with ⟨A, ha, himp⟩ | hc
  · exact (himp _ _ _ (he.2 _ A ha) ho).elim
  refine ⟨fun j => he.1 (slot mapping j), ?_⟩
  intro j B hj
  obtain ⟨A,ha,h⟩ := hc j B hj
  by_cases hij : slot mapping j = i
  · simp only [hij,↓reduceIte] at h
    change meaning G B (n+1) W (ρ (slot mapping j))
    rw [hij]
    exact h (n+1) W _ (by simpa [hij] using he.2 _ A ha) ho
  · simp only [hij,↓reduceIte] at h
    rcases h with h | ⟨t, q, f, rfl, hf, hs⟩ | ⟨f, hf, hx, hp⟩
    · exact h (n+1) W _ (he.2 _ A ha)
    · rcases List.mem_append.mp hf with hf | hf
      · obtain ⟨flds, c, l, hv, hfl, hu⟩ := hl _ f hf
        exact hs (n+1) W _ (fieldSlice_sound (he.2 _ A ha) hh hv hfl hu ho)
      -- Read through a key the object may lack: where it has it, the read
      -- gave the field's value; where it lacks it, no label the slice drops
      -- is the object's.
      · obtain ⟨flds, c, hv, _, hpresent⟩ := hopt _ f hf
        cases hfl : flds.lookup f with
        | none => exact hs (n+1) W _ (fieldSlice_absent (he.2 _ A ha) hv hfl)
        | some l => exact hs (n+1) W _ (fieldSlice_sound (he.2 _ A ha) hh hv hfl (hpresent l hfl) ho)
    · obtain ⟨flds, c, hv, hab, _⟩ := hopt _ f hf
      cases hfl : flds.lookup f with
      | none => exact absurd (hab hfl) (excludesUndef_sound hx ho)
      | some l =>
        refine promotes_sound hp (he.2 _ A ha) fun flds' c' he' hn => ?_
        have he'' : ρ (slot mapping j) = .objAt flds' c' := he'
        rw [hv] at he''
        cases he''
        rw [hfl] at hn
        cases hn

#print axioms fieldSlice_sound
#print axioms checkObservedSub_sound
#print axioms checkObserved_sound
#print axioms ObservedCovers.env
#print axioms realmArray_of_record
#print axioms arraySlice_sound
end Verification.Model.BranchRefinement
