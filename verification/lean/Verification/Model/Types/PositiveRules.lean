import Verification.Model.Types.PositiveGraphs

/-! Declarative subtyping for positive recursive graphs. Rules have only finite
syntactic premises; semantic soundness is a separate theorem. -/
namespace Verification.Model.PositiveRules
open PositiveNormalization PositiveGraphs ReferenceConjunctions Tower

abbrev Table (ι : Type) := List (List ι × List ι)
abbrev Rel (table : Table ι) (a b : List ι) : Prop := (a, b) ∈ table

/-- Fixed signatures `(receiver, parameters, result)`. -/
abbrev Ops (ι : Type) := List (List ι × List (List ι) × List ι)
/-- The clauses of a type's clause rows. -/
def clausesOf (G : NormalGraph ι) (S : List ι) : List (Clause (List ι)) := S.flatMap G

/-- A type's clauses, when every label is a clause row, and none otherwise. A
rule reading a type's clauses reads them here, so a type with a parameter or
scheme row has none to read: its members are not described by clauses. -/
def expand (G : NormalGraph ι) (S : List ι) : List (Clause (List ι)) :=
  if G.plainTy S then clausesOf G S else []

theorem expand_of_plain {G : NormalGraph ι} {S : List ι} (h : G.plainTy S = true) :
    expand G S = clausesOf G S := by simp [expand, h]

/-- A type with a clause to read is of clause rows. -/
theorem plain_of_mem_expand {G : NormalGraph ι} {S : List ι} {c}
    (h : c ∈ expand G S) : G.plainTy S = true := by
  unfold expand at h; split at h
  · assumption
  · simp at h

theorem expand_sub {G : NormalGraph ι} {S : List ι} {c} (h : c ∈ expand G S) :
    c ∈ clausesOf G S := by
  rwa [expand_of_plain (plain_of_mem_expand h)] at h

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
  (clausesOf G S).flatMap splitClause

def meaning (G : NormalGraph ι) (S : List ι) : Fam := setSem (normalDenote G) S

/-- Top has no shape; it can share a member with any clause. -/
def isTop : Clause α → Bool
  | .top => true
  | _ => false

/-- Two clauses can share a member: same shape, or top, which has none. -/
def overlaps (a b : Clause α) : Bool :=
  isTop a || isTop b || shape a == shape b

/-- A conservative compatibility check: two union labels can share a value
only if some pair of their clauses has the same outer shape. A parameter or
scheme row has no clauses to compare, so it may share a value with anything. -/
def compatible (G : NormalGraph ι) (i k : ι) : Bool :=
  !G.plain i || !G.plain k || (G i).any fun a => (G k).any fun b => overlaps a b

theorem normal_congr (G : NormalGraph ι) : LayerCongr (normalLayer G) := normalLayer_congr G

/-- A clause row means its clauses. -/
theorem unfold_normal (G : NormalGraph ι) (i : ι) (hi : G.plain i = true) (n W v) :
    normalDenote G i n W v ↔ semList (meaning G) (G i) n W v :=
  unfold_plain hi n W v

/-- Every clause of a type's labels is within the type's meaning. -/
theorem expand_sem_mpr {G : NormalGraph ι} {S : List ι} {n W v}
    (h : semList (meaning G) (clausesOf G S) n W v) : meaning G S n W v := by
  obtain ⟨c, hc, hv⟩ := h
  obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
  have hp : G.plain i = true := by
    cases hp : G.plain i
    · simp [NormalGraph.clauses, hp] at hc
    · rfl
  exact ⟨i, hi, (unfold_normal G i hp n W v).mpr ⟨c, hc, hv⟩⟩

/-- A member of a type is in one of its clauses, or in one of its parameter or
scheme rows. -/
theorem meaning_cases {G : NormalGraph ι} {S : List ι} {n W v} (h : meaning G S n W v) :
    semList (meaning G) (clausesOf G S) n W v ∨
      ∃ i ∈ S, G.plain i = false ∧ normalDenote G i n W v := by
  obtain ⟨i, hi, hv⟩ := h
  cases hp : G.plain i
  · exact .inr ⟨i, hi, hp, hv⟩
  · obtain ⟨c, hc, hv⟩ := (unfold_normal G i hp n W v).mp hv
    exact .inl ⟨c, List.mem_flatMap.mpr ⟨i, hi, hc⟩, hv⟩

/-- A type of clause rows means the union of its labels' clauses. -/
theorem expand_sem (G : NormalGraph ι) (S : List ι) (hS : G.plainTy S = true) (n W v) :
    meaning G S n W v ↔ semList (meaning G) (expand G S) n W v := by
  rw [expand_of_plain hS]
  have hp : ∀ i ∈ S, G.plain i = true := List.all_eq_true.mp hS
  constructor
  · rintro ⟨i, hi, hv⟩
    obtain ⟨c, hc, hv⟩ := (unfold_normal G i (hp i hi) n W v).mp hv
    exact ⟨c, List.mem_flatMap.mpr ⟨i, hi, hc⟩, hv⟩
  · rintro ⟨c, hc, hv⟩
    obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
    exact ⟨i, hi, (unfold_normal G i (hp i hi) n W v).mpr ⟨c, hc, hv⟩⟩

/-- The split is meaning preserving, in the same style as `meet_sound` and
`normalize_sound`: the union of the parts denotes exactly the original clause. -/
theorem splitClause_sem (X : α → Fam) (c : Clause α) (n W v) :
    semList X (splitClause c) n W v ↔ sem X c n W v := by
  cases c
  all_goals simp [splitClause, semList, setSem, sem, boolT]

theorem source_sem (G : NormalGraph ι) (S : List ι) (hS : G.plainTy S = true) (n W v) :
    meaning G S n W v ↔ semList (meaning G) (sourceClauses G S) n W v := by
  rw [expand_sem G S hS n W v, expand_of_plain hS]
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
  cases hpi : G.plain i
  · simp [compatible, hpi]
  cases hpk : G.plain k
  · simp [compatible, hpk]
  simp only [compatible, hpi, hpk, Bool.not_true, Bool.false_or]
  obtain ⟨a, ha, hva⟩ := (unfold_normal G i hpi n W v).mp hi
  obtain ⟨b, hb, hvb⟩ := (unfold_normal G k hpk n U v).mp hk
  simp only [List.any_eq_true]
  refine ⟨a, ha, b, hb, ?_⟩
  by_cases hta : a = .top
  · subst hta; rfl
  by_cases htb : b = .top
  · subst htb; simp [overlaps, isTop]
  have hs := (sem_shape hta hva).symm.trans (sem_shape htb hvb)
  simp [overlaps, hs]

def FamLeAt (G : NormalGraph ι) (a b : List ι) (n : Nat) : Prop :=
  ∀ (W : WorldT n) (v : Val), meaning G a n W v → meaning G b n W v

/-- Pointwise domain inclusion requires the same number of actual arguments. -/
def Domains (R : List ι → List ι → Prop) : List (List ι) → List (List ι) → Prop
  | [], [] => True
  | a :: As, b :: Bs => R a b ∧ Domains R As Bs
  | _, _ => False

instance Domains.decidable {R : List ι → List ι → Prop} [∀ a b, Decidable (R a b)] :
    ∀ As Bs, Decidable (Domains R As Bs)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse id
  | _ :: _, [] => isFalse id
  | a :: As, b :: Bs =>
    if h : R a b then
      match Domains.decidable As Bs with
      | isTrue h' => isTrue ⟨h, h'⟩
      | isFalse h' => isFalse fun hd => h' hd.2
    else isFalse fun hd => h hd.1

theorem Domains.sound {G : NormalGraph ι} {R As Bs n}
    (hd : Domains R As Bs) (hr : ∀ a b, R a b → FamLeAt G a b n)
    {W args} (ha : ArgsT (As.map (meaning G)) n W args) :
    ArgsT (Bs.map (meaning G)) n W args := by
  induction As generalizing Bs args with
  | nil => cases Bs <;> simp_all [Domains]
  | cons A As ih =>
    cases Bs with
    | nil => exact False.elim hd
    | cons B Bs =>
      cases args with
      | nil => exact False.elim ha
      | cons a args => exact ⟨hr A B hd.1 W a ha.1, ih hd.2 ha.2⟩

/-- Domains pointwise below others at one budget admit, there, every list
the others admit. -/
theorem Domains.short {G : NormalGraph ι} {R : List ι → List ι → Prop} {j : Nat}
    (hr : ∀ a b, R a b → FamLeAt G a b j) {W : WorldT j} :
    ∀ {As Bs : List (List ι)} {args : List Tm}, Domains R As Bs →
      ArgsShort (As.map (meaning G)) j W args → ArgsShort (Bs.map (meaning G)) j W args
  | [], [], _, _, h => h
  | [], _ :: _, _, hd, _ | _ :: _, [], _, hd, _ => hd.elim
  | A :: As, B :: Bs, [], hd, h => by
    simp only [List.map_cons, ArgsShort_nil_args, List.mem_cons, forall_eq_or_imp] at h ⊢
    have := Domains.short hr (args := []) hd.2 (ArgsShort_nil_args.mpr h.2)
    exact ⟨hr A B hd.1 W _ h.1, ArgsShort_nil_args.mp this⟩
  | A :: As, B :: Bs, a :: args, hd, h => by
    simp only [List.map_cons, ArgsShort_cons] at h ⊢
    exact ⟨hr A B hd.1 W a h.1, Domains.short hr hd.2 h.2⟩

/-- An empty position admits no list: no value is written there, and
`undefined` is not in it either. -/
theorem short_empty {G : NormalGraph ι} {j : Nat} {W : WorldT j} :
    ∀ {As : List (List ι)} {args : List Tm}, [] ∈ As →
      ¬ ArgsShort (As.map (meaning G)) j W args
  | [], _, he => by simp at he
  | A :: As, args, he => by
    intro h
    have hnone : ∀ u, ¬ meaning G [] j W u := by
      intro u ⟨i, hi, _⟩; simp at hi
    cases args with
    | nil =>
      simp only [List.map_cons, ArgsShort_nil_args, List.mem_cons, forall_eq_or_imp] at h
      rcases List.mem_cons.mp he with rfl | he
      · exact hnone _ h.1
      · exact short_empty he (ArgsShort_nil_args.mpr h.2)
    | cons a args =>
      simp only [List.map_cons, ArgsShort_cons] at h
      rcases List.mem_cons.mp he with rfl | he
      · exact hnone _ h.1
      · exact short_empty he h.2

/-- A union at any position splits the admitted lists without reordering. -/
theorem short_union {G : NormalGraph ι} (a b : List ι) (suffix : List (List ι)) {j : Nat}
    {W : WorldT j} : ∀ (pre : List (List ι)) {args : List Tm},
      ArgsShort ((pre ++ (a ++ b) :: suffix).map (meaning G)) j W args →
      ArgsShort ((pre ++ a :: suffix).map (meaning G)) j W args ∨
        ArgsShort ((pre ++ b :: suffix).map (meaning G)) j W args
  | [], [], h => by
    simp only [List.nil_append, List.map_cons, ArgsShort_nil_args, List.mem_cons,
      forall_eq_or_imp] at h ⊢
    obtain ⟨⟨i, hi, hv⟩, hs⟩ := h
    rcases List.mem_append.mp hi with hi | hi
    · exact Or.inl ⟨⟨i, hi, hv⟩, hs⟩
    · exact Or.inr ⟨⟨i, hi, hv⟩, hs⟩
  | [], x :: args, h => by
    simp only [List.nil_append, List.map_cons, ArgsShort_cons] at h ⊢
    obtain ⟨⟨i, hi, hv⟩, hs⟩ := h
    rcases List.mem_append.mp hi with hi | hi
    · exact Or.inl ⟨⟨i, hi, hv⟩, hs⟩
    · exact Or.inr ⟨⟨i, hi, hv⟩, hs⟩
  | P :: pre, [], h => by
    simp only [List.cons_append, List.map_cons, ArgsShort_nil_args, List.mem_cons,
      forall_eq_or_imp] at h ⊢
    rcases short_union a b suffix pre (args := []) (ArgsShort_nil_args.mpr h.2) with h' | h'
    · exact Or.inl ⟨h.1, ArgsShort_nil_args.mp h'⟩
    · exact Or.inr ⟨h.1, ArgsShort_nil_args.mp h'⟩
  | P :: pre, x :: args, h => by
    simp only [List.cons_append, List.map_cons, ArgsShort_cons] at h ⊢
    rcases short_union a b suffix pre h.2 with h' | h'
    · exact Or.inl ⟨h.1, h'⟩
    · exact Or.inr ⟨h.1, h'⟩

/-- A variadic signature admits, at one budget, every list a fixed one admits
when its fixed parameters come first, pointwise wider, and the fixed one's
further positions are within its element contract. -/
theorem rest_short {G : NormalGraph ι} {R : List ι → List ι → Prop} {j : Nat}
    (hr : ∀ a b, R a b → FamLeAt G a b j) {W : WorldT j} {E : List ι} :
    ∀ {Ps As : List (List ι)} {args : List Tm}, Domains R (As.take Ps.length) Ps →
      (∀ A ∈ As.drop Ps.length, R A E) →
      ArgsShort (As.map (meaning G)) j W args →
      ArgsRest (Ps.map (meaning G)) (meaning G E) j W args
  | [], As, args, _, hel, h => by
    rw [List.map_nil, ArgsRest_nil_params]
    obtain ⟨-, ht, -⟩ := h
    refine ArgsT_all_le (E := meaning G E) (fun A hA u hu => ?_) ht
    rw [← List.map_take] at hA
    obtain ⟨A0, hA0, rfl⟩ := List.mem_map.mp hA
    exact hr A0 E (hel A0 (by simpa using List.mem_of_mem_take hA0)) W u hu
  | _ :: _, [], _, hd, _, _ => hd.elim
  | P :: Ps, A :: As, [], hd, hel, h => by
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons] at hd hel
    simp only [List.map_cons, ArgsShort_nil_args, ArgsRest_nil_args, List.mem_cons,
      forall_eq_or_imp] at h ⊢
    have := rest_short hr (args := []) hd.2 hel (ArgsShort_nil_args.mpr h.2)
    exact ⟨hr A P hd.1 W _ h.1, ArgsRest_nil_args.mp this⟩
  | P :: Ps, A :: As, a :: args, hd, hel, h => by
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons] at hd hel
    simp only [List.map_cons, ArgsShort_cons, ArgsRest_cons] at h ⊢
    exact ⟨hr A P hd.1 W a h.1, rest_short hr hd.2 hel h.2⟩

/-- A variadic signature admits, at one budget, every list a narrower variadic
signature admits. -/
theorem rest_rest {G : NormalGraph ι} {R : List ι → List ι → Prop} {j : Nat}
    (hr : ∀ a b, R a b → FamLeAt G a b j) {W : WorldT j} {E F : List ι} (hfe : R F E) :
    ∀ {Ps Qs : List (List ι)} {args : List Tm}, Domains R (Qs.take Ps.length) Ps →
      (∀ Q ∈ Qs.drop Ps.length, R Q E) →
      ArgsRest (Qs.map (meaning G)) (meaning G F) j W args →
      ArgsRest (Ps.map (meaning G)) (meaning G E) j W args
  | [], Qs, args, _, hel, h => by
    rw [List.map_nil, ArgsRest_nil_params]
    have hle : ∀ A ∈ Qs.map (meaning G), ∀ u, A j W u → meaning G E j W u := by
      intro A hA u hu
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hA
      exact hr Q E (hel Q (by simpa using hQ)) W u hu
    rcases h with ⟨-, ht, -⟩ | ⟨-, ht, hx⟩
    · exact ArgsT_all_le (E := meaning G E) (fun A hA u hu => hle A (List.mem_of_mem_take hA) u hu) ht
    · intro e he
      rw [← List.take_append_drop (Qs.map (meaning G)).length args] at he
      rcases List.mem_append.mp he with he | he
      · exact ArgsT_all_le hle ht e he
      · exact hr F E hfe W e (hx e he)
  | _ :: _, [], _, hd, _, _ => hd.elim
  | P :: Ps, Q :: Qs, [], hd, hel, h => by
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons] at hd hel
    simp only [List.map_cons, ArgsRest_nil_args, List.mem_cons, forall_eq_or_imp] at h ⊢
    have := rest_rest hr hfe (args := []) hd.2 hel (ArgsRest_nil_args.mpr h.2)
    exact ⟨hr Q P hd.1 W _ h.1, ArgsRest_nil_args.mp this⟩
  | P :: Ps, Q :: Qs, a :: args, hd, hel, h => by
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons] at hd hel
    simp only [List.map_cons, ArgsRest_cons] at h ⊢
    exact ⟨hr Q P hd.1 W a h.1, rest_rest hr hfe hd.2 hel h.2⟩

/-- A variadic signature `(receiver, fixed, element, result)` covers a fixed
target `(Rt, As, d)` when the target's receiver is within its receiver, the
target's first positions are within its fixed parameters, its further
positions within its element contract, and its result within the target's. -/
def RestFixed (R : List ι → List ι → Prop) (s : List ι × List (List ι) × List ι × List ι)
    (Rt : List ι) (As : List (List ι)) (d : List ι) : Prop :=
  R Rt s.1 ∧ Domains R (As.take s.2.1.length) s.2.1 ∧
    (∀ A ∈ As.drop s.2.1.length, R A s.2.2.1) ∧ (s.2.2.2 = [] ∨ R s.2.2.2 d)

/-- One variadic signature covers another: the target's receiver is within the
source's; the target's fixed parameters are within the source's, then within
its element contract; the target's element contract is within the source's;
results are covariant. -/
def RestCovers (R : List ι → List ι → Prop)
    (p q : List ι × List (List ι) × List ι × List ι) : Prop :=
  R q.1 p.1 ∧ Domains R (q.2.1.take p.2.1.length) p.2.1 ∧
    (∀ A ∈ q.2.1.drop p.2.1.length, R A p.2.2.1) ∧ R q.2.2.1 p.2.2.1 ∧ R p.2.2.2 q.2.2.2

/-- Declarative overload coverage for native signatures with receivers. A
target `(Rt, As, d)` is covered by a fixed source signature, by a variadic
one, by splitting a union at the receiver or at a parameter position, or by
combining two coverings. The receiver is contravariant, like a parameter. -/
inductive CallArrow (compat : ι → ι → Bool) (R : List ι → List ι → Prop)
    (L : List (List ι × List (List ι) × List ι))
    (S : List (List ι × List (List ι) × List ι × List ι)) :
    List ι → List (List ι) → List ι → Prop where
  | emptyRecv : CallArrow compat R L S [] As d
  | empty : [] ∈ As → CallArrow compat R L S Rt As d
  | source : p ∈ L → R Rt p.1 → Domains R As p.2.1 → (p.2.2 = [] ∨ R p.2.2 d) →
      CallArrow compat R L S Rt As d
  | rest : s ∈ S → RestFixed R s Rt As d → CallArrow compat R L S Rt As d
  | union : CallArrow compat R L S Rt (pre ++ a :: suffix) d →
      CallArrow compat R L S Rt (pre ++ b :: suffix) d →
      CallArrow compat R L S Rt (pre ++ (a ++ b) :: suffix) d
  | recvUnion : CallArrow compat R L S a As d → CallArrow compat R L S b As d →
      CallArrow compat R L S (a ++ b) As d
  | combine : CallArrow compat R L S Rt As b → CallArrow compat R L S Rt As b' →
      (∀ i ∈ b, ∀ k ∈ b', compat i k = true → R [i] d) → CallArrow compat R L S Rt As d

/-- An arrow's source result within the target's, or empty. -/
theorem arrow_result {G : NormalGraph ι} {R : List ι → List ι → Prop} {n : Nat} {r d : List ι}
    (hr : ∀ j, j < n → ∀ a b, R a b → FamLeAt G a b j) (hc : r = [] ∨ R r d) :
    ∀ m, m < n → ∀ (V : WorldT m) u, meaning G r m V u → meaning G d m V u := by
  intro m hm V u hu
  rcases hc with he | he
  · obtain ⟨i, hi, _⟩ := hu; simp [he] at hi
  · exact hr m hm _ _ he V u hu

theorem CallArrow.sound {G : NormalGraph ι} {R L S Rt As d}
    (hc : CallArrow (compatible G) R L S Rt As d) (n : Nat)
    (hr : ∀ j, j < n → ∀ a b, R a b → FamLeAt G a b j)
    (W : WorldT n) (v : Val)
    (hv : callsT (L.map fun p => (meaning G p.1, p.2.1.map (meaning G), meaning G p.2.2)) n W v ∧
      restsT (S.map fun s => (meaning G s.1, s.2.1.map (meaning G), meaning G s.2.2.1,
        meaning G s.2.2.2)) n W v) :
    Promise (ArgsShort (As.map (meaning G))) (meaning G Rt) (meaning G d) n W v := by
  induction hc with
  | emptyRecv =>
    intro j hj U hx hu heap hh r hrv hrm
    obtain ⟨i, hi, _⟩ := hrm
    simp at hi
  | empty he =>
    intro j hj U hx hu heap hh r hrv hrm args hvals ha
    exact False.elim (short_empty he ha)
  | source hm hrecv hd hres =>
    exact (hv.1.2 _ (List.mem_map_of_mem hm)).weaken
      (fun j hj U r hrm => hr j hj _ _ hrecv U r hrm)
      (fun j hj U args ha => Domains.short (hr j hj) hd ha) (arrow_result hr hres)
  | rest hs hrf =>
    exact (hv.2.2 _ (List.mem_map_of_mem hs)).weaken
      (fun j hj U r hrm => hr j hj _ _ hrf.1 U r hrm)
      (fun j hj U args ha => rest_short (hr j hj) (by simpa using hrf.2.1)
        (by simpa using hrf.2.2.1) ha) (arrow_result hr hrf.2.2.2)
  | union _ _ hl hh =>
    intro j hj U hx hu heap hok r hrv hrm args hvals ha
    rcases short_union _ _ _ _ ha with ha | ha
    · exact hl j hj U hx hu heap hok r hrv hrm args hvals ha
    · exact hh j hj U hx hu heap hok r hrv hrm args hvals ha
  | recvUnion _ _ hl hh =>
    intro j hj U hx hu heap hok r hrv hrm args hvals ha
    obtain ⟨i, hi, hvi⟩ := hrm
    rcases List.mem_append.mp hi with hi | hi
    · exact hl j hj U hx hu heap hok r hrv ⟨i, hi, hvi⟩ args hvals ha
    · exact hh j hj U hx hu heap hok r hrv ⟨i, hi, hvi⟩ args hvals ha
  | combine _ _ hg hl hh =>
    intro j hj U hx hu heap hok r hrv hrm args hvals ha
    obtain ⟨r1, hi1, hs1⟩ := hl j hj U hx hu heap hok r hrv hrm args hvals ha
    obtain ⟨r2, hi2, hs2⟩ := hh j hj U hx hu heap hok r hrv hrm args hvals ha
    cases CallArguments.invoke_deterministic hi1 hi2
    refine ⟨r1, hi1, safe_cross_upto j ?_ U U heap _ hok hok hs1 hs2⟩
    rintro r hb V V' heap h1 h2 u ⟨i, hi, hv1⟩ ⟨k, hk, hv2⟩
    exact hr r (by omega) _ _ (hg i hi k hk (compatible_sound hv1 hv2)) V u
      ⟨i, by simp, hv1⟩

theorem rest_covers_sound {G : NormalGraph ι} {R : List ι → List ι → Prop}
    {p q : List ι × List (List ι) × List ι × List ι} (hc : RestCovers R p q) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j) (W : WorldT n) (v : Val)
    (hv : Promise (ArgsRest (p.2.1.map (meaning G)) (meaning G p.2.2.1)) (meaning G p.1)
      (meaning G p.2.2.2) n W v) :
    Promise (ArgsRest (q.2.1.map (meaning G)) (meaning G q.2.2.1)) (meaning G q.1)
      (meaning G q.2.2.2) n W v := by
  obtain ⟨hrecv, hd, hel, he, hres⟩ := hc
  exact hv.weaken (fun j hj U r hrm => hr j hj _ _ hrecv U r hrm)
    (fun j hj U args ha => rest_rest (hr j hj) he (by simpa using hd)
    (by simpa using hel) ha) (fun m hm U u hu => hr m hm _ _ hres U u hu)

/-- One record conjunction covers another when every field any target operand
names is named by some source operand, with contracts that imply each other.
Fields the target does not name are not compared: a record type is open, so
covering never requires the source to forget a field. -/
abbrev CoversFields (R : List ι → List ι → Prop)
    (source target : List (List (PropKey × List ι))) : Prop :=
  ∀ b ∈ target, ∀ q ∈ b, ∃ p ∈ source.flatten, p.1 = q.1 ∧ R p.2 q.2 ∧ R q.2 p.2

/-- A view field is covered by a source field of the same name whose contract
implies it: an invariant field or a view, either way a sound upper bound. -/
abbrev CoversViews (R : List ι → List ι → Prop)
    (source : List (List (PropKey × List ι))) (views target : List (PropKey × List ι)) : Prop :=
  ∀ q ∈ target, ∃ p ∈ source.flatten ++ views, p.1 = q.1 ∧ R p.2 q.2

/-- An optional field is covered by a source field of the same key, required
or optional, whose contract is equivalent to it: where the object has the key,
its location has that contract. Neither a view nor an optional source field
covers a required target field, since neither says the key is present. -/
abbrev CoversOptional (R : List ι → List ι → Prop)
    (source : List (List (PropKey × List ι))) (optional target : List (PropKey × List ι)) : Prop :=
  ∀ q ∈ target, ∃ p ∈ source.flatten ++ optional, p.1 = q.1 ∧ R p.2 q.2 ∧ R q.2 p.2

/-- Two rest contracts agree: both absent, or both present and equivalent. -/
def CoversRest (R : List ι → List ι → Prop) (readonly : Bool) : Option (List ι) → Option (List ι) → Prop
  | none, none => True
  | some x, some y => R x y ∧ (readonly = false → R y x)
  | _, _ => False

/-- Same-shape tuple contracts compare element read types covariantly for a
readonly target. A writable target needs a writable source and equivalent
element contracts; no location is retyped. -/
def CoversTuple (R : List ι → List ι → Prop) (p q : Tuple (List ι)) : Prop :=
  p.required.length = q.required.length ∧ p.optional.length = q.optional.length ∧
  (∀ x ∈ p.required.zip q.required, R x.1 x.2 ∧ (q.readonly = false → R x.2 x.1)) ∧
  (∀ x ∈ p.optional.zip q.optional, R x.1 x.2 ∧ (q.readonly = false → R x.2 x.1)) ∧
  CoversRest R q.readonly p.rest q.rest ∧ (q.readonly = false → p.readonly = false)

def Covers (G : NormalGraph ι) (R : List ι → List ι → Prop) :
    Clause (List ι) → Clause (List ι) → Prop
  | _, .top => True
  | .list a bs, .list c ds => ∀ q ∈ c :: ds, ∃ p ∈ a :: bs, CoversTuple R p q
  | .nul, .nul => True
  | .undef, .undef => True
  | .bool, .bool => True
  | .boolLit _, .bool => True
  | .boolLit a, .boolLit b => a = b
  | .num, .num => True
  | .numLit _, .num => True
  | .numLit a, .numLit b => a = b
  | .str, .str => True
  | .strLit _, .str => True
  | .strLit a, .strLit b => a = b
  | .refs a bs vs os, .refs c ds ws ps => CoversFields R (a :: bs) (c :: ds) ∧
      CoversViews R (a :: bs) vs ws ∧ CoversOptional R (a :: bs) os ps
  | .dict a bs vs ix os, .dict c ds ws iy ps =>
      CoversFields R (a :: bs) (c :: ds) ∧ CoversViews R (a :: bs) vs ws ∧
      (∀ y ∈ iy, ∃ x ∈ ix, R x y) ∧ CoversOptional R (a :: bs) os ps
  | .arrs L S, .arrs M T | .callable _ _ L S, .arrs M T =>
      (∀ p ∈ M, CallArrow (compatible G) R L S p.1 p.2.1 p.2.2) ∧ ∀ t ∈ T, ∃ s ∈ S, RestCovers R s t
  | .callable a bs L S, .callable c ds M T =>
      CoversFields R (a :: bs) (c :: ds) ∧
      (∀ p ∈ M, CallArrow (compatible G) R L S p.1 p.2.1 p.2.2) ∧ ∀ t ∈ T, ∃ s ∈ S, RestCovers R s t
  -- A construct signature is covered by one taking as many parameters, each
  -- at least as wide, with a result at most as wide.
  | .ctors L, .ctors M => ∀ q ∈ M, ∃ p ∈ L, Domains R q.1 p.1 ∧ R p.2 q.2
  | _, _ => False

/-- Covering field by field is enough: the operands all constrain the same
object, so a field the target names is found at the location the source already
fixed, under a contract the two relations identify. -/
theorem covers_recs {G : NormalGraph ι} {R : List ι → List ι → Prop}
    {a c : List (PropKey × List ι)} {bs ds : List (List (PropKey × List ι))}
    (hc : CoversFields R (a :: bs) (c :: ds)) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j)
    (W : WorldT n) (flds : List (PropKey × Nat))
    (hsrc : ∀ x ∈ a :: bs, recT (famsOf (meaning G) x) n W (.objAt flds .absent)) :
    ∀ b ∈ c :: ds, recT (famsOf (meaning G) b) n W (.objAt flds .absent) := by
  intro b hb
  refine ⟨flds, rfl, ?_⟩
  intro f T hm
  obtain ⟨y, hy, rfl⟩ := mem_famsOf.mp hm
  obtain ⟨⟨pf, pl⟩, hp, hpf, hpy, hyp⟩ := hc b hb (f, y) hy
  simp only at hpf
  subst hpf
  obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
  obtain ⟨flds', l, c0, he', hf, hl, hag⟩ :=
    recT_at (mem_famsOf.mpr ⟨pl, hpL, rfl⟩) (hsrc L hL)
  cases he'
  exact ⟨l, c0, hf, hl, fun j hj W' u =>
    (hag j hj W' u).trans ⟨hr j hj pl y hpy W' u, hr j hj y pl hyp W' u⟩⟩

theorem covers_fields_sound {G : NormalGraph ι} {R : List ι → List ι → Prop}
    {a c : List (PropKey × List ι)} {bs ds : List (List (PropKey × List ι))}
    (hc : CoversFields R (a :: bs) (c :: ds)) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j)
    (W : WorldT n) (v : Val)
    (hv : refsT (famsOf (meaning G) a) (bs.map (famsOf (meaning G))) n W v) :
    refsT (famsOf (meaning G) c) (ds.map (famsOf (meaning G))) n W v := by
  obtain ⟨flds, he, -⟩ := hv.1
  subst he
  have hsrc : ∀ x ∈ a :: bs, recT (famsOf (meaning G) x) n W (.objAt flds .absent) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv.1
    · exact hv.2 _ (List.mem_map_of_mem hx)
  have key := covers_recs hc n hr W flds hsrc
  exact ⟨key c (by simp), fun B hB => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
    exact key b (List.mem_cons_of_mem c hb)⟩

/-- A covered view field reads a location whose contract implies its family,
whether the source states that location invariantly or as a view. -/
theorem covers_views_sound {G : NormalGraph ι} {R : List ι → List ι → Prop}
    {a : List (PropKey × List ι)} {bs : List (List (PropKey × List ι))}
    {vs ws : List (PropKey × List ι)}
    (hc : CoversViews R (a :: bs) vs ws) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j)
    (W : WorldT n) (v : Val)
    (hv : refsT (famsOf (meaning G) a) (bs.map (famsOf (meaning G))) n W v ∧
      viewT (famsOf (meaning G) vs) n W v) :
    viewT (famsOf (meaning G) ws) n W v := by
  intro f T hm
  obtain ⟨y, hy, rfl⟩ := mem_famsOf.mp hm
  obtain ⟨⟨pf, pl⟩, hp, hpf, hpy⟩ := hc (f, y) hy
  simp only at hpf
  subst hpf
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
    have hsrc : recT (famsOf (meaning G) L) n W v := by
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hv.1.1
      · exact hv.1.2 _ (List.mem_map_of_mem hL)
    obtain ⟨flds, l, c0, he, hf, hl, hag⟩ := recT_at (mem_famsOf.mpr ⟨pl, hpL, rfl⟩) hsrc
    exact ⟨flds, l, c0, he, hf, hl, fun j hj W' u hu => hr j hj pl y hpy W' u ((hag j hj W' u).mp hu)⟩
  · obtain ⟨flds, l, c0, he, hf, hl, hag⟩ := viewT_at (mem_famsOf.mpr ⟨pl, hp, rfl⟩) hv.2
    exact ⟨flds, l, c0, he, hf, hl, fun j hj W' u hu => hr j hj pl y hpy W' u (hag j hj W' u hu)⟩

/-- A covered optional field: where the key is present, the location is the
one a source field of that key names, whose contract both relations identify
with the target's. -/
theorem covers_optional_sound {G : NormalGraph ι} {R : List ι → List ι → Prop}
    {a : List (PropKey × List ι)} {bs : List (List (PropKey × List ι))}
    {os ps : List (PropKey × List ι)}
    (hc : CoversOptional R (a :: bs) os ps) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j)
    (W : WorldT n) (v : Val)
    (hv : refsT (famsOf (meaning G) a) (bs.map (famsOf (meaning G))) n W v ∧
      optT (famsOf (meaning G) os) n W v) :
    optT (famsOf (meaning G) ps) n W v := by
  obtain ⟨flds, he, -⟩ := hv.1.1
  subst he
  refine ⟨flds, rfl, ?_⟩
  intro f T hm l hl
  obtain ⟨y, hy, rfl⟩ := mem_famsOf.mp hm
  obtain ⟨⟨pf, pl⟩, hp, hpf, hpy, hyp⟩ := hc (f, y) hy
  simp only at hpf
  subst hpf
  have both : ∀ (c0 : Ctr n), (∀ j (hj : j < n) (W' : WorldT j) u, c0 j hj W' u ↔ meaning G pl j W' u) →
      ∀ j (hj : j < n) (W' : WorldT j) u, c0 j hj W' u ↔ meaning G y j W' u :=
    fun c0 hag j hj W' u => (hag j hj W' u).trans ⟨hr j hj pl y hpy W' u, hr j hj y pl hyp W' u⟩
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
    have hsrc : recT (famsOf (meaning G) L) n W (.objAt flds .absent) := by
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hv.1.1
      · exact hv.1.2 _ (List.mem_map_of_mem hL)
    obtain ⟨flds', l', c0, he', hf, hw, hag⟩ := recT_at (mem_famsOf.mpr ⟨pl, hpL, rfl⟩) hsrc
    cases he'
    rw [hl] at hf
    cases hf
    exact ⟨c0, hw, both c0 hag⟩
  · obtain ⟨c0, hw, hag⟩ := optT_present (mem_famsOf.mpr ⟨pl, hp, rfl⟩) hv.2 hl
    exact ⟨c0, hw, both c0 hag⟩

/-- The same argument for a callable object's property bag, which forgets the
call slot but names the same locations. -/
theorem covers_bags_sound {G : NormalGraph ι} {R : List ι → List ι → Prop}
    {a c : List (PropKey × List ι)} {bs ds : List (List (PropKey × List ι))}
    (hc : CoversFields R (a :: bs) (c :: ds)) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j)
    (W : WorldT n) (v : Val)
    (hv : CallableConjunctions.propsT (famsOf (meaning G) a)
      (bs.map (famsOf (meaning G))) n W v) :
    CallableConjunctions.propsT (famsOf (meaning G) c)
      (ds.map (famsOf (meaning G))) n W v := by
  obtain ⟨flds, code, he, hval, hbag⟩ := hv.1
  subst he
  have hsrc : ∀ x ∈ a :: bs, recT (famsOf (meaning G) x) n W (.objAt flds .absent) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hbag
    · obtain ⟨flds', code', he', -, hbag'⟩ := hv.2 _ (List.mem_map_of_mem hx)
      cases he'
      exact hbag'
  have key := covers_recs hc n hr W flds hsrc
  exact ⟨⟨flds, code, rfl, hval, key c (by simp)⟩, fun B hB => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
    exact ⟨flds, code, rfl, hval, key b (List.mem_cons_of_mem c hb)⟩⟩

/-- A covered tuple contract holds of the same store: every position's location
carries a contract both families identify. -/
theorem covers_tuple_sound {G : NormalGraph ι} {R : List ι → List ι → Prop}
    {p q : Tuple (List ι)} (hc : CoversTuple R p q) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j)
    (W : WorldT n) (v : Val) (hv : listT (tupleFams (meaning G) p) n W v) :
    listT (tupleFams (meaning G) q) n W v := by
  obtain ⟨hreqLen, hoptLen, hreqR, hoptR, hrestR, hmode⟩ := hc
  obtain ⟨ls, rfl, hlen, hbound, hreq, hopt, hrest⟩ := hv
  simp only [listT, tupleFams, List.length_map, List.getElem?_map, Option.map_eq_none_iff,
    Option.map_eq_some_iff] at hlen hbound hreq hopt hrest ⊢
  refine ⟨ls, rfl, hreqLen ▸ hlen, ?_, ?_, ?_, ?_⟩
  · intro hn
    have hpn : p.rest = none := by
      cases hp : p.rest <;> cases hq : q.rest <;> simp_all [CoversRest]
    have := hbound hpn
    omega
  · rintro i A ⟨y, hy, rfl⟩
    have hi : i < q.required.length := (List.getElem?_eq_some_iff.mp hy).1
    obtain ⟨x, hx⟩ : ∃ x, p.required[i]? = some x :=
      List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩ |> fun h => ⟨_, h⟩
    obtain ⟨l, c, hl, hw, hag⟩ := hreq i (meaning G x) ⟨x, hx, rfl⟩
    have hxy := hreqR (x, y) (List.getElem?_zip_eq_some.mpr ⟨hx, hy⟩ |> List.mem_of_getElem?)
    exact ⟨l, c, hl, hw, fun j hj W' u =>
      (hag j hj W' u).weaken hmode (hr j hj _ _ hxy.1 W' u) (fun hro => hr j hj _ _ (hxy.2 hro) W' u)⟩
  · rintro i A l ⟨y, hy, rfl⟩ hl
    have hi : i < q.optional.length := (List.getElem?_eq_some_iff.mp hy).1
    obtain ⟨x, hx⟩ : ∃ x, p.optional[i]? = some x :=
      List.getElem?_eq_some_iff.mpr ⟨by omega, rfl⟩ |> fun h => ⟨_, h⟩
    obtain ⟨c, hw, hag⟩ := hopt i (meaning G x) l ⟨x, hx, rfl⟩ (hreqLen ▸ hl)
    have hxy := hoptR (x, y) (List.getElem?_zip_eq_some.mpr ⟨hx, hy⟩ |> List.mem_of_getElem?)
    exact ⟨c, hw, fun j hj W' u =>
      (hag j hj W' u).weaken hmode (hr j hj _ _ hxy.1 W' u) (fun hro => hr j hj _ _ (hxy.2 hro) W' u)⟩
  · intro i l hi hl
    obtain ⟨E, c, ⟨e, he, rfl⟩, hw, hag⟩ := hrest i l (by omega) hl
    cases hq : q.rest with
    | none => simp [he, hq, CoversRest] at hrestR
    | some y =>
      have hx : R e y ∧ (q.readonly = false → R y e) := by simpa [he, hq, CoversRest] using hrestR
      exact ⟨meaning G y, c, ⟨y, rfl, rfl⟩, hw,
        fun j hj W' u => (hag j hj W' u).weaken hmode (hr j hj _ _ hx.1 W' u) (fun hro => hr j hj _ _ (hx.2 hro) W' u)⟩

theorem covers_lists_sound {G : NormalGraph ι} {R : List ι → List ι → Prop}
    {a c : Tuple (List ι)} {bs ds : List (Tuple (List ι))}
    (hc : ∀ q ∈ c :: ds, ∃ p ∈ a :: bs, CoversTuple R p q) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j)
    (W : WorldT n) (v : Val)
    (hv : listT (tupleFams (meaning G) a) n W v ∧ ∀ b ∈ bs, listT (tupleFams (meaning G) b) n W v) :
    listT (tupleFams (meaning G) c) n W v ∧ ∀ b ∈ ds, listT (tupleFams (meaning G) b) n W v := by
  have each : ∀ q ∈ c :: ds, listT (tupleFams (meaning G) q) n W v := by
    intro q hq
    obtain ⟨p, hp, hpq⟩ := hc q hq
    have hpv : listT (tupleFams (meaning G) p) n W v := by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hv.1
      · exact hv.2 p hp
    exact covers_tuple_sound hpq n hr W v hpv
  exact ⟨each c (by simp), fun b hb => each b (List.mem_cons_of_mem c hb)⟩

theorem Covers.sound {G : NormalGraph ι} {R a b} (hc : Covers G R a b) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j)
    (W : WorldT n) (v : Val) : sem (meaning G) a n W v → sem (meaning G) b n W v := by
  by_cases hb : b = .top
  · subst hb; exact fun hv => sem_value hv
  cases a <;> cases b <;> simp only [Covers] at hc
  all_goals try contradiction
  all_goals try exact absurd rfl hb
  case ctors.ctors L M =>
    intro hv
    refine ⟨hv.1, fun q hq => ?_⟩
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    obtain ⟨p, hp, hd, hres⟩ := hc q0 hq0
    intro j hj U hx hu heap hh args hvals ha
    obtain ⟨result, hcon, hsafe⟩ := hv.2 _ (List.mem_map_of_mem hp) j hj U hx hu heap hh args hvals
      (Domains.sound hd (fun a b hab => hr j hj a b hab) ha)
    exact ⟨result, hcon, Safe_mono j (fun m hm V u hu => hr m (by omega) _ _ hres V u hu) U heap _ hsafe⟩
  · exact id
  · exact id
  · rename_i a bs vs os c ds ws ps
    intro hv
    exact ⟨covers_fields_sound hc.1 n hr W v hv.1, covers_views_sound hc.2.1 n hr W v ⟨hv.1, hv.2.1⟩,
      covers_optional_sound hc.2.2 n hr W v ⟨hv.1, hv.2.2⟩⟩
  · rename_i a bs vs ix os c ds ws iy ps
    intro hv
    refine ⟨covers_fields_sound hc.1 n hr W v hv.1,
      covers_views_sound hc.2.1 n hr W v ⟨hv.1, hv.2.1⟩, ?_,
      covers_optional_sound hc.2.2.2 n hr W v ⟨hv.1, hv.2.2.2⟩⟩
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hc.2.2.1 y hy
    obtain ⟨flds, he, hfs⟩ := hv.2.2.1 x hx
    refine ⟨flds, he, ?_⟩
    intro f l hl
    obtain ⟨c, hw, hag⟩ := hfs f l hl
    exact ⟨c, hw, fun j hj W' u hu => hr j hj x y hxy W' u (hag j hj W' u hu)⟩
  · intro hv
    refine ⟨⟨hv.1.1, fun p hp => ?_⟩, ⟨hv.1.1, fun t ht => ?_⟩⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact CallArrow.sound (hc.1 q hq) n hr W v hv
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      obtain ⟨s, hs, hst⟩ := hc.2 t0 ht0
      exact rest_covers_sound hst n hr W v (hv.2.2 _ (List.mem_map_of_mem hs))
  · rename_i b
    cases b <;> intro hv <;> cases hv
    · exact Or.inr rfl
    · exact Or.inl rfl
  · cases hc; exact id
  · -- num ≤ num
    exact id
  · -- numLit ≤ num: the singleton inhabits the family
    rename_i b
    intro hv; cases hv; exact ⟨b, rfl⟩
  · -- numLit ≤ numLit at equal spellings
    cases hc; exact id
  · exact id
  · intro hv
    refine ⟨⟨hv.1.2.1, fun p hp => ?_⟩, ⟨hv.1.2.1, fun t ht => ?_⟩⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact CallArrow.sound (hc.1 q hq) n hr W v ⟨hv.1.2, hv.2⟩
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      obtain ⟨s, hs, hst⟩ := hc.2 t0 ht0
      exact rest_covers_sound hst n hr W v (hv.2.2 _ (List.mem_map_of_mem hs))
  · rename_i a bs L S c ds M T
    intro hv
    refine ⟨⟨covers_bags_sound hc.1 n hr W v hv.1.1, hv.1.2.1, fun p hp => ?_⟩,
      ⟨hv.1.2.1, fun t ht => ?_⟩⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact CallArrow.sound (hc.2.1 q hq) n hr W v ⟨hv.1.2, hv.2⟩
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      obtain ⟨s, hs, hst⟩ := hc.2.2 t0 ht0
      exact rest_covers_sound hst n hr W v (hv.2.2 _ (List.mem_map_of_mem hs))
  · -- str ≤ str
    exact id
  · -- strLit ≤ str: the singleton inhabits the family
    rename_i s
    intro hv; cases hv; exact ⟨s, rfl⟩
  · -- strLit ≤ strLit at equal strings
    cases hc; exact id
  · rename_i a bs c ds
    intro hv
    exact covers_lists_sound hc n hr W v hv

/-- A parameter or scheme row of the source is in the target, or the target
admits every value: the row has no clauses for a target clause to cover. -/
def Opaque (G : NormalGraph ι) (S T : List ι) : Prop :=
  ∀ i ∈ S, G.plain i = true ∨ i ∈ T ∨ .top ∈ clausesOf G T

instance [DecidableEq ι] {G : NormalGraph ι} {S T : List ι} : Decidable (Opaque G S T) :=
  inferInstanceAs (Decidable (∀ i ∈ S, G.plain i = true ∨ i ∈ T ∨ .top ∈ clausesOf G T))

/-- Each split part of each source clause must be covered by some single target
clause. A `bool` source is therefore discharged by the pair of Boolean singleton
clauses, or by a single `bool` clause, or by any target containing both. -/
def Valid (G : NormalGraph ι) (table : Table ι) : Prop :=
  ∀ p ∈ table, Opaque G p.1 p.2 ∧
    ∀ a ∈ sourceClauses G p.1, ∃ b ∈ clausesOf G p.2, Covers G (Rel table) a b

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
      rcases meaning_cases hv with ⟨c, hcm, hv⟩ | ⟨i, hi, hp, hv⟩
      · obtain ⟨a, ha, hv⟩ := (splitClause_sem (meaning G) c n W v).mpr hv
        obtain ⟨b, hb, hcover⟩ := (hc (A, B) hab).2 a (List.mem_flatMap.mpr ⟨c, hcm, ha⟩)
        exact expand_sem_mpr ⟨b, hb, Covers.sound hcover n (fun j hj => ih j hj) W v hv⟩
      · rcases ((hc (A, B) hab).1 i hi).resolve_left (by simp [hp]) with hB | htop
        · exact ⟨i, hB, hv⟩
        · exact expand_sem_mpr ⟨.top, htop, normalDenote_value hv⟩
  exact fun n => hs n S T hm

/-! ## Instances of a scheme row

An instance of a scheme row is named by an instance map `θ`, sending each row a
signature reaches to a type of the graph: a binder to the type it is
instantiated at, a clause row to a clause row whose clauses are its own with
every operand mapped (the substituted copy the graph already holds, such as
`PromiseLike<boolean>` for `PromiseLike<R1>`), a scheme row to a scheme row
with the same binders and its signatures mapped, and any row that does not
depend on a moved binder to itself. Dependence is by free parameter rows,
stated by a checked certificate (`FreeOk`): a row under a scheme binding a
parameter does not depend on it, so a receiver `Promise<number>`, whose `then`
mentions `then`'s own binders, is its own image. -/

/-- A type's meaning is a family of closed values. -/
theorem meaning_valueFam (G : NormalGraph ι) (S : List ι) : ValueFam (meaning G S) :=
  ⟨setSem_adm (normalDenote_adm G) S, fun _ _ _ ⟨_, _, h⟩ => normalDenote_value h⟩

abbrev InstMap (ι : Type) := List (ι × List ι)

/-- A row's image; a row the map does not name is its own. -/
def img [DecidableEq ι] (θ : InstMap ι) (i : ι) : List ι := (θ.lookup i).getD [i]

def imgTy [DecidableEq ι] (θ : InstMap ι) (S : List ι) : List ι := S.flatMap (img θ)

/-- A signature's image. -/
def instSig [DecidableEq ι] (θ : InstMap ι) (p : List ι × List (List ι) × List ι) :
    List ι × List (List ι) × List ι :=
  (imgTy θ p.1, p.2.1.map (imgTy θ), imgTy θ p.2.2)

/-- Every row of a signature is in `D`. -/
def SigIn [DecidableEq ι] (D : List ι) (p : List ι × List (List ι) × List ι) : Bool :=
  (p.1 :: p.2.2 :: p.2.1).all fun S => S.all (· ∈ D)

/-- A clause reads its operands only: families agreeing on the rows of `D`
give it one meaning, when its operands are within `D`. -/
theorem sem_congr_on [DecidableEq ι] {D : List ι} {c : Clause (List ι)}
    (hops : ∀ S ∈ c.operands, ∀ l ∈ S, l ∈ D) (X Y : ι → Fam) (n : Nat)
    (h : ∀ l ∈ D, Agree (X l) (Y l) n) (W : WorldT n) (v : Val) :
    sem (setSem X) c n W v ↔ sem (setSem Y) c n W v := by
  let r : List ι → List ι := fun S => S.filter fun l => decide (l ∈ D)
  have hcr : c.map r = c := map_of_operands fun S hS =>
    List.filter_eq_self.mpr fun l hl => by simpa using hops S hS l hl
  rw [← hcr, sem_map, sem_map]
  apply sem_congr _ _ n (fun S => ?_) c W v
  intro m hm U u
  have hin : ∀ l ∈ r S, l ∈ D := fun l hl => by simpa using (List.mem_filter.mp hl).2
  constructor
  · rintro ⟨l, hl, hx⟩; exact ⟨l, hl, (h l (hin l hl) m hm U u).mp hx⟩
  · rintro ⟨l, hl, hy⟩; exact ⟨l, hl, (h l (hin l hl) m hm U u).mpr hy⟩

/-- The rows a row reads: a clause row its operands, a scheme row its
signatures' rows. -/
def reads (G : NormalGraph ι) (i : ι) : List ι :=
  match G.schemes i with
  | some s => s.signatures.flatMap fun p => p.1 ++ p.2.1.flatten ++ p.2.2
  | none => (G i).flatMap fun c => c.operands.flatten

/-! ### Free parameter rows -/

abbrev FreeMap (ι : Type) := List (ι × List ι)

/-- The parameter rows a row may depend on, as a certificate states them. -/
def fv [DecidableEq ι] (V : FreeMap ι) (i : ι) : List ι := (V.lookup i).getD []

/-- `V` over-approximates the free parameter rows of the rows of `D`, which is
closed under what its rows read: a parameter row is free in itself, and a row
reading another has that row's free parameters, except a scheme row's own
binders. -/
def FreeOk [DecidableEq ι] (G : NormalGraph ι) (D : List ι) (V : FreeMap ι) : Bool :=
  D.all fun i =>
    (!G.params i || (fv V i).contains i) &&
    (reads G i).all fun l => D.contains l &&
      (fv V l).all fun p => (fv V i).contains p ||
        (match G.schemes i with | some s => s.binders.contains p | none => false)

theorem freeOk_row [DecidableEq ι] {G : NormalGraph ι} {D : List ι} {V : FreeMap ι}
    (hF : FreeOk G D V = true) {i : ι} (hi : i ∈ D) :
    (G.params i = true → i ∈ fv V i) ∧ ∀ l ∈ reads G i, l ∈ D ∧ ∀ p ∈ fv V l,
      p ∈ fv V i ∨ (∃ s, G.schemes i = some s ∧ p ∈ s.binders) := by
  have h := List.all_eq_true.mp hF i hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.contains_iff_mem] at h
  refine ⟨fun hp => by simpa [hp] using h.1, fun l hl => ⟨by simpa using (h.2 l hl).1, fun p hp => ?_⟩⟩
  have := (h.2 l hl).2 p hp
  rcases this with h1 | h2
  · exact .inl (by simpa using h1)
  · right
    cases hs : G.schemes i with
    | none => simp [hs] at h2
    | some s => exact ⟨s, rfl, by simpa [hs] using h2⟩

/-- **Independence.** A row means the same at two assignments agreeing on its
free parameter rows. -/
theorem agree_free [DecidableEq ι] {G : NormalGraph ι} {D : List ι} {V : FreeMap ι}
    (hF : FreeOk G D V = true) :
    ∀ n, ∀ η η' : Assignment ι, ∀ i ∈ D, (∀ p ∈ fv V i, η.1 p = η'.1 p) →
      ∀ (W : WorldT n) v, qDenote G (η, i) n W v ↔ qDenote G (η', i) n W v := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro η η' i hi hag W v
  have ⟨hself, hreads⟩ := freeOk_row hF hi
  rw [qDenote_unfold, qDenote_unfold]
  unfold qLayer
  cases hp : G.params i
  · simp only [Bool.false_eq_true, if_false]
    cases hq : G.schemes i with
    | some s =>
      refine and_congr Iff.rfl (forall_congr' fun As => forall_congr' fun hl => ?_)
      have hrow : ∀ S, (∀ l ∈ S, l ∈ reads G i) → Agree
          (setSem (fun l => qDenote G (assign η s.binders As, l)) S)
          (setSem (fun l => qDenote G (assign η' s.binders As, l)) S) n := by
        intro S hS m hm U u
        have hl' : ∀ l ∈ S, ∀ p ∈ fv V l,
            (assign η s.binders As).1 p = (assign η' s.binders As).1 p := by
          intro l hlS p hpv
          by_cases hb : p ∈ s.binders
          · exact assign_mem_eq η η' s.binders As hb hl
          · rw [assign_nmem η s.binders As hb, assign_nmem η' s.binders As hb]
            rcases (hreads l (hS l hlS)).2 p hpv with h1 | ⟨s', hs', h2⟩
            · exact hag p h1
            · rw [hq] at hs'; cases hs'; exact absurd h2 hb
        constructor
        · rintro ⟨l, hlS, h⟩
          exact ⟨l, hlS, (ih m hm _ _ l (hreads l (hS l hlS)).1 (hl' l hlS) U u).mp h⟩
        · rintro ⟨l, hlS, h⟩
          exact ⟨l, hlS, (ih m hm _ _ l (hreads l (hS l hlS)).1 (hl' l hlS) U u).mpr h⟩
      have hargs : ∀ Ss : List (List ι), (∀ S ∈ Ss, ∀ l ∈ S, l ∈ reads G i) → ArgsAgree n
          (Ss.map (setSem fun l => qDenote G (assign η s.binders As, l)))
          (Ss.map (setSem fun l => qDenote G (assign η' s.binders As, l))) := by
        intro Ss hSs
        induction Ss with
        | nil => exact .nil
        | cons S Ss ihs =>
          exact .cons (hrow S (hSs S List.mem_cons_self))
            (ihs fun T hT => hSs T (List.mem_cons_of_mem _ hT))
      unfold instanceSigs
      exact callsT_congr s.signatures _ _ (fun p hps => by
        have hin : ∀ l ∈ p.1 ++ p.2.1.flatten ++ p.2.2, l ∈ reads G i := fun l hl => by
          simp only [reads, hq]
          exact List.mem_flatMap.mpr ⟨p, hps, hl⟩
        refine ⟨hrow _ fun l hl => hin l (by simp [hl]), hargs _ fun S hS l hl => hin l ?_,
          hrow _ fun l hl => hin l (by simp [hl])⟩
        simp only [List.mem_append, List.mem_flatten]
        exact .inl (.inr ⟨S, hS, hl⟩)) W v
    | none =>
      simp only [normalLayer, semList, setSem]
      have hag' : ∀ l ∈ reads G i, Agree (qDenote G (η, l)) (qDenote G (η', l)) n := by
        intro l hl m hm U u
        refine ih m hm η η' l (hreads l hl).1 (fun p hpv => ?_) U u
        rcases (hreads l hl).2 p hpv with h1 | ⟨s', hs', _⟩
        · exact hag p h1
        · rw [hq] at hs'; cases hs'
      have hops : ∀ c ∈ G i, ∀ S ∈ c.operands, ∀ l ∈ S, l ∈ reads G i := by
        intro c hc S hS l hl
        simp only [reads, hq]
        exact List.mem_flatMap.mpr ⟨c, hc, List.mem_flatten.mpr ⟨S, hS, hl⟩⟩
      constructor
      · rintro ⟨c, hc, h⟩
        exact ⟨c, hc, (sem_congr_on (hops c hc) _ _ n hag' W v).mp h⟩
      · rintro ⟨c, hc, h⟩
        exact ⟨c, hc, (sem_congr_on (hops c hc) _ _ n hag' W v).mpr h⟩
  · simp only [if_true]
    rw [hag i (hself hp)]

/-! ### Instance maps -/

/-- The binders an instance may move: the instantiated scheme's, and every
scheme row's in the domain. -/
def movedBinders [DecidableEq ι] (G : NormalGraph ι) (bs D : List ι) : List ι :=
  bs ++ D.flatMap fun i => match G.schemes i with
    | some s => s.binders
    | none => []

/-- One row of an instance map. A binder is a parameter row; any other
parameter row is its own image; a row with no moved free parameter may be its
own image; a clause row's image is one clause row holding its clauses mapped;
and a scheme row's image is one scheme row with the same binders, none of them
instantiated, and its signatures mapped. -/
def rowInst [DecidableEq ι] (G : NormalGraph ι) (bs : List ι) (θ : InstMap ι) (V : FreeMap ι)
    (moved : List ι) (i : ι) : Bool :=
  if bs.contains i then G.params i
  else if G.params i then img θ i == [i]
  else if img θ i == [i] && (fv V i).all (fun p => !moved.contains p) then true
  else match G.schemes i, img θ i with
    | some s, [j] => !G.params j && G.schemes j == some ⟨s.binders, s.signatures.map (instSig θ)⟩ &&
        s.binders.all (fun p => !bs.contains p)
    | none, [j] => G.plain i && G.plain j && G j == (G i).map (Clause.map (imgTy θ))
    | _, _ => false

/-- A checked instance map on a domain `D` with free parameters `V`: `V` is
sound on `D`, every row of `D` is mapped by `rowInst`, and each binder's image
lies in `D` with no moved free parameter. -/
def InstOk [DecidableEq ι] (G : NormalGraph ι) (bs : List ι) (θ : InstMap ι) (D : List ι)
    (V : FreeMap ι) : Bool :=
  FreeOk G D V && D.all (rowInst G bs θ V (movedBinders G bs D)) &&
    bs.all fun p => (img θ p).all fun l => D.contains l &&
      (fv V l).all fun q => !(movedBinders G bs D).contains q

/-- What each binder is instantiated at. -/
noncomputable def instArgs [DecidableEq ι] (G : NormalGraph ι) (bs : List ι) (θ : InstMap ι) :
    List ValueFamily :=
  bs.map fun p => ⟨meaning G (img θ p), meaning_valueFam G _⟩

/-- The assignment giving each binder its image's meaning. -/
noncomputable def instEnv [DecidableEq ι] (G : NormalGraph ι) (bs : List ι) (θ : InstMap ι) :
    Assignment ι :=
  assign G.env bs (instArgs G bs θ)

theorem inst_row [DecidableEq ι] {G : NormalGraph ι} {bs θ D V}
    (hok : InstOk G bs θ D V = true) :
    ∀ n, ∀ η : Assignment ι, (∀ p, p ∉ movedBinders G bs D → η.1 p = G.env.1 p) →
      ∀ i ∈ D, ∀ (W : WorldT n) v,
        qDenote G (assign η bs (instArgs G bs θ), i) n W v ↔ qMeaning G η (img θ i) n W v := by
  simp only [InstOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hF, hrows⟩, hargs⟩ := hok
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro η hη i hi W v
  have ⟨_, hreads⟩ := freeOk_row hF hi
  have hrow := hrows i hi
  simp only [rowInst] at hrow
  -- A type in the domain free of moved binders means the same at `η` as at the
  -- graph's own assignment.
  have hfix : ∀ S, (∀ l ∈ S, l ∈ D ∧ ∀ q ∈ fv V l, q ∉ movedBinders G bs D) →
      (qMeaning G η S n W v ↔ meaning G S n W v) := by
    intro S hS
    constructor
    · rintro ⟨l, hl, h⟩
      exact ⟨l, hl, (agree_free hF n η G.env l (hS l hl).1
        (fun q hq => hη q ((hS l hl).2 q hq)) W v).mp h⟩
    · rintro ⟨l, hl, h⟩
      exact ⟨l, hl, (agree_free hF n η G.env l (hS l hl).1
        (fun q hq => hη q ((hS l hl).2 q hq)) W v).mpr h⟩
  by_cases hb : i ∈ bs
  · -- a binder
    have hpar : G.params i = true := by simpa [hb] using hrow
    rw [qDenote_unfold]
    simp only [qLayer, hpar, if_true]
    rw [instArgs, assign_map_mem _ _ _ hb]
    refine (hfix _ fun l hl => ?_).symm
    have := hargs i hb l hl
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.contains_iff_mem,
      decide_eq_false_iff_not] at this
    exact ⟨by simpa using this.1, fun q hq => by simpa using this.2 q hq⟩
  have hbF : bs.contains i = false := by simpa using hb
  simp only [hbF, Bool.false_eq_true, if_false] at hrow
  cases hpar : G.params i
  · simp only [hpar, Bool.false_eq_true, if_false] at hrow
    by_cases hrig : (img θ i == [i] && (fv V i).all (fun p => !(movedBinders G bs D).contains p)) = true
    · -- its own image, free of moved binders
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true',
        List.contains_iff_mem] at hrig
      rw [hrig.1]
      have : qDenote G (assign η bs (instArgs G bs θ), i) n W v ↔ qDenote G (η, i) n W v :=
        agree_free hF n _ η i hi (fun p hp => assign_nmem η bs _ (fun hpb => by
          have := hrig.2 p hp
          simp [movedBinders, hpb] at this)) W v
      rw [this]
      exact ⟨fun h => ⟨i, List.mem_singleton_self i, h⟩,
        fun ⟨_, hm, h⟩ => by cases List.mem_singleton.mp hm; exact h⟩
    · have hrigF : (img θ i == [i] && (fv V i).all
          (fun p => !(movedBinders G bs D).contains p)) = false := by simpa using hrig
      simp only [hrigF, Bool.false_eq_true, if_false] at hrow
      cases hsch : G.schemes i with
      | some s =>
        cases himg : img θ i with
        | nil => simp [hsch, himg] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hsch, himg] at hrow
          | nil =>
            -- a scheme row, mapped to a scheme row
            have hs := hsch
            have hj := himg
            simp only [hsch, himg, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
              List.all_eq_true] at hrow
            obtain ⟨⟨hjp, hjs⟩, hdisj⟩ := hrow
            have hRHS : qMeaning G η [j] n W v ↔ qDenote G (η, j) n W v :=
              ⟨fun ⟨_, hm, h⟩ => by cases List.mem_singleton.mp hm; exact h,
               fun h => ⟨j, List.mem_singleton_self j, h⟩⟩
            rw [hRHS, qDenote_unfold, qDenote_unfold]
            simp only [qLayer, hpar, hjp, hs, hjs, Bool.false_eq_true, if_false]
            refine and_congr Iff.rfl (forall_congr' fun As => forall_congr' fun hl => ?_)
            have hd : ∀ p ∈ bs, p ∉ s.binders := fun p hp hps => by
              have := hdisj p hps; simp [hp] at this
            have hcomm := assign_comm η (bs := bs) (cs := s.binders) (instArgs G bs θ) As hd
            have hmoved : ∀ p, p ∉ movedBinders G bs D →
                (assign η s.binders As).1 p = G.env.1 p := by
              intro p hp
              have hpb : p ∉ s.binders := fun hps => hp (by
                simp only [movedBinders, List.mem_append, List.mem_flatMap]
                exact .inr ⟨i, hi, by simp [hs, hps]⟩)
              rw [assign_nmem η s.binders As hpb]; exact hη p hp
            have hsets : ∀ S, (∀ l ∈ S, l ∈ reads G i) → Agree
                (setSem (fun l => qDenote G (assign (assign η bs (instArgs G bs θ)) s.binders As, l)) S)
                (setSem (fun l => qDenote G (assign η s.binders As, l)) (imgTy θ S)) n := by
              intro S hS m hm U u
              rw [hcomm]
              constructor
              · rintro ⟨l, hl, h⟩
                obtain ⟨l', hl', h'⟩ := (ih m hm _ hmoved l (hreads l (hS l hl)).1 U u).mp h
                exact ⟨l', List.mem_flatMap.mpr ⟨l, hl, hl'⟩, h'⟩
              · rintro ⟨l', hl', h'⟩
                obtain ⟨l, hl, hl'⟩ := List.mem_flatMap.mp hl'
                exact ⟨l, hl, (ih m hm _ hmoved l (hreads l (hS l hl)).1 U u).mpr ⟨l', hl', h'⟩⟩
            have hargsA : ∀ Ss : List (List ι), (∀ S ∈ Ss, ∀ l ∈ S, l ∈ reads G i) → ArgsAgree n
                (Ss.map (setSem fun l => qDenote G (assign (assign η bs (instArgs G bs θ)) s.binders As, l)))
                ((Ss.map (imgTy θ)).map (setSem fun l => qDenote G (assign η s.binders As, l))) := by
              intro Ss hSs
              induction Ss with
              | nil => exact .nil
              | cons S Ss ihs =>
                exact .cons (hsets S (hSs S List.mem_cons_self))
                  (ihs fun T hT => hSs T (List.mem_cons_of_mem _ hT))
            unfold instanceSigs
            simp only [List.map_map]
            exact callsT_congr s.signatures _ _ (fun p hps => by
              have hin : ∀ l ∈ p.1 ++ p.2.1.flatten ++ p.2.2, l ∈ reads G i := fun l hl => by
                simp only [reads, hs]
                exact List.mem_flatMap.mpr ⟨p, hps, hl⟩
              refine ⟨hsets _ fun l hl => hin l (by simp [hl]),
                by simpa [instSig] using hargsA _ fun S hS l hl => hin l (by
                  simp only [List.mem_append, List.mem_flatten]
                  exact .inl (.inr ⟨S, hS, hl⟩)),
                hsets _ fun l hl => hin l (by simp [hl])⟩) W v

      | none =>
        cases himg : img θ i with
        | nil => simp [hsch, himg] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hsch, himg] at hrow
          | nil =>
            -- a clause row, mapped to a clause row
            have hs := hsch
            have hj := himg
            simp only [hsch, himg, Bool.and_eq_true, beq_iff_eq] at hrow
            obtain ⟨⟨hip, hjp⟩, hG⟩ := hrow
            have hl : qDenote G (assign η bs (instArgs G bs θ), i) n W v ↔
                semList (setSem fun l => qDenote G (assign η bs (instArgs G bs θ), l)) (G i) n W v :=
              unfold_plain (G := { G with env := assign η bs (instArgs G bs θ) }) hip n W v
            have hr : qMeaning G η [j] n W v ↔ semList (qMeaning G η) (G j) n W v := by
              constructor
              · rintro ⟨_, hm, h⟩
                cases List.mem_singleton.mp hm
                exact (unfold_plain (G := { G with env := η }) hjp n W v).mp h
              · intro h
                exact ⟨j, List.mem_singleton_self j,
                  (unfold_plain (G := { G with env := η }) hjp n W v).mpr h⟩
            have clause_inst : ∀ c ∈ G i,
                sem (setSem fun l => qDenote G (assign η bs (instArgs G bs θ), l)) c n W v ↔
                  sem (qMeaning G η) (c.map (imgTy θ)) n W v := by
              intro c hc
              have hD : ∀ S ∈ c.operands, ∀ l ∈ S, l ∈ D := by
                intro S hS l hl
                refine (hreads l ?_).1
                simp only [reads, hs]
                exact List.mem_flatMap.mpr ⟨c, hc, List.mem_flatten.mpr ⟨S, hS, hl⟩⟩
              let r : List ι → List ι := fun S => S.filter fun l => decide (l ∈ D)
              have hcr : c.map r = c := map_of_operands fun S hS =>
                List.filter_eq_self.mpr fun l hl => by simpa using hD S hS l hl
              rw [sem_map, ← hcr, sem_map, sem_map]
              apply sem_congr _ _ n (fun S => ?_) c W v
              intro m hm U u
              have hin : ∀ l ∈ r S, l ∈ D := fun l hl => by
                simpa using (List.mem_filter.mp hl).2
              constructor
              · rintro ⟨l, hl, h⟩
                obtain ⟨l', hl', h'⟩ := (ih m hm η hη l (hin l hl) U u).mp h
                exact ⟨l', List.mem_flatMap.mpr ⟨l, hl, hl'⟩, h'⟩
              · rintro ⟨l', hl', h'⟩
                obtain ⟨l, hl, hl'⟩ := List.mem_flatMap.mp hl'
                exact ⟨l, hl, (ih m hm η hη l (hin l hl) U u).mpr ⟨l', hl', h'⟩⟩
            rw [hl, hr, hG]
            simp only [semList, setSem, List.mem_map]
            constructor
            · rintro ⟨c, hc, h⟩
              exact ⟨_, ⟨c, hc, rfl⟩, (clause_inst c hc).mp h⟩
            · rintro ⟨_, ⟨c, hc, rfl⟩, h⟩
              exact ⟨c, hc, (clause_inst c hc).mpr h⟩

  · -- a parameter row other than a binder, its own image
    simp only [hpar, if_true, beq_iff_eq] at hrow
    rw [hrow, qDenote_unfold]
    simp only [qLayer, hpar, if_true]
    rw [instArgs, assign_map_nmem _ _ _ hb]
    constructor
    · intro h
      refine ⟨i, List.mem_singleton_self i, ?_⟩
      show qDenote G (η, i) n W v
      rw [qDenote_unfold]; simpa [qLayer, hpar] using h
    · rintro ⟨_, hm, h⟩
      cases List.mem_singleton.mp hm
      change qDenote G (η, i) n W v at h
      rw [qDenote_unfold] at h; simpa [qLayer, hpar] using h

/-- **Instances.** Read at the instance's assignment, a type within the domain
means exactly its image. -/
theorem inst_type [DecidableEq ι] {G : NormalGraph ι} {bs θ D V}
    (hok : InstOk G bs θ D V = true) {S : List ι} (hS : ∀ l ∈ S, l ∈ D) :
    setSem (fun l => qDenote G (instEnv G bs θ, l)) S = meaning G (imgTy θ S) := by
  funext n W v
  apply propext
  have row := fun l hl => inst_row hok n G.env (fun _ _ => rfl) l (hS l hl) W v
  constructor
  · rintro ⟨l, hl, h⟩
    obtain ⟨l', hl', h'⟩ := (row l hl).mp h
    exact ⟨l', List.mem_flatMap.mpr ⟨l, hl, hl'⟩, h'⟩
  · rintro ⟨l', hl', h'⟩
    obtain ⟨l, hl, hl'⟩ := List.mem_flatMap.mp hl'
    exact ⟨l, hl, (row l hl).mpr ⟨l', hl', h'⟩⟩

theorem sigIn_mem [DecidableEq ι] {D : List ι} {p : List ι × List (List ι) × List ι}
    (h : SigIn D p = true) :
    (∀ l ∈ p.1, l ∈ D) ∧ (∀ l ∈ p.2.2, l ∈ D) ∧ ∀ S ∈ p.2.1, ∀ l ∈ S, l ∈ D := by
  simp only [SigIn, List.all_cons, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- A member of a scheme row meets each checked instance of its signatures. -/
theorem inst_sound [DecidableEq ι] {G : NormalGraph ι} {T : List ι} {i : ι} {s : SchemeRow ι}
    {θ : InstMap ι} {D : List ι} {V : FreeMap ι} {L : Ops ι}
    (hp : G.params i = false) (hq : G.schemes i = some s) (hok : InstOk G s.binders θ D V = true)
    (hL : ∀ q ∈ L, ∃ p ∈ s.signatures, SigIn D p = true ∧ q = instSig θ p)
    (hT : expand G T = [.arrs L []]) : FamLe (meaning G [i]) (meaning G T) := by
  intro n W v hv
  obtain ⟨_, hm, hv⟩ := hv
  cases List.mem_singleton.mp hm
  have hs := (qDenote_unfold G (G.env, i) n W v).mp hv
  simp only [qLayer, hp, hq, Bool.false_eq_true, if_false] at hs
  obtain ⟨hinv, hall⟩ := hs
  have hc := (hall (instArgs G s.binders θ) (by simp [instArgs])).2
  have hTp := plain_of_mem_expand (G := G) (S := T) (c := .arrs L []) (by simp [hT])
  refine (expand_sem G T hTp n W v).mpr ⟨.arrs L [], by simp [hT], ?_⟩
  refine ⟨⟨hinv, fun q' hq' => ?_⟩, ⟨hinv, by simp⟩⟩
  obtain ⟨q, hqL, rfl⟩ := List.mem_map.mp hq'
  obtain ⟨p, hps, hin, rfl⟩ := hL q hqL
  have hpr := hc _ (List.mem_map_of_mem (f := fun p =>
    (setSem (fun l => qDenote G (instEnv G s.binders θ, l)) p.1,
     p.2.1.map (setSem fun l => qDenote G (instEnv G s.binders θ, l)),
     setSem (fun l => qDenote G (instEnv G s.binders θ, l)) p.2.2)) hps)
  obtain ⟨h1, h3, h2⟩ := sigIn_mem hin
  have hargs : p.2.1.map (setSem fun l => qDenote G (instEnv G s.binders θ, l)) =
      (p.2.1.map (imgTy θ)).map (meaning G) := by
    rw [List.map_map]
    exact List.map_congr_left fun S hS => inst_type hok (h2 S hS)
  simp only [instSig]
  rw [inst_type hok h1, inst_type hok h3, hargs] at hpr
  exact hpr

/-- Structural rules compose completed proofs. They cannot bypass the guarded
coverage obligation for any row of a recursive table. -/
inductive Sub (G : NormalGraph ι) : List ι → List ι → Prop where
  | core : Core G S T → Sub G S T
  | subset : (∀ i ∈ S, i ∈ T) → Sub G S T
  | trans : Sub G S U → Sub G U T → Sub G S T
  /-- **Instantiation.** A scheme row is below an arrow type whose signatures
  are images of its own under one checked instance map. -/
  | inst [DecidableEq ι] {i : ι} {s : SchemeRow ι} {θ : InstMap ι} {D : List ι} {V : FreeMap ι}
      {L : Ops ι} :
      G.params i = false → G.schemes i = some s → InstOk G s.binders θ D V = true →
      (∀ q ∈ L, ∃ p ∈ s.signatures, SigIn D p = true ∧ q = instSig θ p) →
      expand G T = [.arrs L []] → Sub G [i] T
  /-- **Generalization.** A type below a scheme's signatures, with its binders
  opaque, is below the scheme: it is so at every instantiation, since none of
  its free parameter rows is a binder (`agree_free`). -/
  | gen [DecidableEq ι] {j : ι} {s : SchemeRow ι} {D U : List ι} {V : FreeMap ι} :
      G.params j = false → G.schemes j = some s →
      expand G U = [.arrs s.signatures []] →
      FreeOk G D V = true → (∀ l ∈ S, l ∈ D ∧ ∀ p ∈ fv V l, p ∉ s.binders) →
      Sub G S U → Sub G S [j]

/-- The graph whose parameter rows mean `η`. No check reads the assignment, so
every derivation over `G` is one over each reassignment. -/
def reassign (G : NormalGraph ι) (η : Assignment ι) : NormalGraph ι := { G with env := η }

/-- Subtyping holds at every assignment: the derivation reads no assignment. -/
theorem Sub.sound_at {G : NormalGraph ι} {S T} (h : Sub G S T) :
    ∀ η, FamLe (meaning (reassign G η) S) (meaning (reassign G η) T) := by
  induction h with
  | core h => exact fun η => Core.sound (G := reassign G η) h
  | subset h => exact fun _ => by rintro n W v ⟨i, hi, hv⟩; exact ⟨i, h i hi, hv⟩
  | trans _ _ ih ih' => exact fun η n W v hv => ih' η n W v (ih η n W v hv)
  | inst hp hq hok hL hT => exact fun η => inst_sound (G := reassign G η) hp hq hok hL hT
  | @gen S _ j s D U V hp hq hU hF hS _ ih =>
    intro η n W v hv
    refine ⟨j, List.mem_singleton_self j, ?_⟩
    change qDenote G (η, j) n W v
    rw [qDenote_unfold]
    simp only [qLayer, hp, hq, Bool.false_eq_true, if_false]
    have hat : ∀ As : List ValueFamily,
        meaning (reassign G (assign η s.binders As)) U n W v := by
      intro As
      apply ih (assign η s.binders As) n W v
      obtain ⟨l, hl, h⟩ := hv
      refine ⟨l, hl, ?_⟩
      change qDenote G (assign η s.binders As, l) n W v
      refine (agree_free hF n η _ l (hS l hl).1 (fun p hp => ?_) W v).mp h
      exact (assign_nmem η s.binders As ((hS l hl).2 p hp)).symm
    have hUp := plain_of_mem_expand (G := G) (S := U) (c := .arrs s.signatures []) (by simp [hU])
    have hsig : ∀ As : List ValueFamily, callsT (instanceSigs
        (fun η' S => setSem (fun l => qDenote G (η', l)) S) η s As) n W v := by
      intro As
      obtain ⟨c, hc, hcv⟩ := (expand_sem (reassign G (assign η s.binders As)) U hUp n W v).mp (hat As)
      have : c = .arrs s.signatures [] := by
        have : expand (reassign G (assign η s.binders As)) U = [.arrs s.signatures []] := hU
        rw [this] at hc; simpa using hc
      subst this
      exact hcv.1
    exact ⟨(hsig []).1, fun As _ => hsig As⟩

theorem Sub.sound {G : NormalGraph ι} {S T} (h : Sub G S T) :
    FamLe (meaning G S) (meaning G T) :=
  h.sound_at G.env

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

#print axioms Domains.sound
#print axioms CallArrow.sound
#print axioms Sub.sound
end Verification.Model.PositiveRules
