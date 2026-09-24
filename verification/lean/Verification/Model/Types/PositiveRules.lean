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

/-- A position covered by another: a present source position needs a target
position whose operand it is within. -/
def PositionCovers (R : List ι → List ι → Prop) : Option (List ι) → Option (List ι) → Prop
  | some a, some b => R a b
  | some _, none => False
  | none, _ => True

instance PositionCovers.decidable {R : List ι → List ι → Prop} [∀ a b, Decidable (R a b)] :
    ∀ x y, Decidable (PositionCovers R x y)
  | some a, some b => inferInstanceAs (Decidable (R a b))
  | some _, none => isFalse id
  | none, _ => isTrue trivial

/-- One pack contract within another: every argument list the source admits,
the target admits. The source requires at least as many positions; a target
without a rest bounds the source's length; and each position's operand is
within the target's, covariantly, since a pack holds values rather than
locations. Past both contracts' fixed positions every index has the rests, so
checking the positions up to that bound checks all. -/
def CoversPack (R : List ι → List ι → Prop) (p q : Tuple (List ι)) : Prop :=
  q.required.length ≤ p.required.length ∧
  (q.rest = none → p.rest = none ∧
    p.required.length + p.optional.length ≤ q.required.length + q.optional.length) ∧
  ∀ i ∈ List.range (max (p.required.length + p.optional.length)
      (q.required.length + q.optional.length) + 1),
    PositionCovers R (p.position i) (q.position i)

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
  -- Every target contract has a source contract within it.
  | .pack a bs, .pack c ds => ∀ q ∈ c :: ds, ∃ p ∈ a :: bs, CoversPack R p q
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

/-- A covered pack contract holds of the same argument list. -/
theorem covers_pack_sound {G : NormalGraph ι} {R : List ι → List ι → Prop}
    {p q : Tuple (List ι)} (hc : CoversPack R p q) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j)
    (W : WorldT n) (vs : List Tm) (hv : PackFits (tupleFams (meaning G) p) n W vs) :
    PackFits (tupleFams (meaning G) q) n W vs := by
  obtain ⟨hreq, hrest, hpos⟩ := hc
  obtain ⟨hlen, hbound, hel⟩ := hv
  have hlen' : p.required.length ≤ vs.length := by simpa [tupleFams] using hlen
  have hbound' : p.rest = none → vs.length ≤ p.required.length + p.optional.length := by
    simpa [tupleFams] using hbound
  refine ⟨?_, ?_, ?_⟩
  · simp only [tupleFams, List.length_map]; omega
  · simp only [tupleFams, List.length_map, Option.map_eq_none_iff]
    intro hn
    obtain ⟨hp, hle⟩ := hrest hn
    have := hbound' hp
    omega
  · intro i u B hu hB j hj U hx
    rw [positionFam_tupleFams] at hB
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hB
    have hi : i < vs.length := (List.getElem?_eq_some_iff.mp hu).1
    cases ha : p.position i with
    | none =>
      obtain ⟨h1, h2⟩ := Tuple.position_none ha
      have := hbound' h2
      omega
    | some a =>
      have hcov : PositionCovers R (p.position i) (q.position i) := by
        by_cases hiN : i ≤ max (p.required.length + p.optional.length)
            (q.required.length + q.optional.length)
        · exact hpos i (List.mem_range.mpr (by omega))
        · have h := hpos _ (List.mem_range.mpr (Nat.lt_succ_self _))
          have e1 : p.position i = p.position (max (p.required.length + p.optional.length)
              (q.required.length + q.optional.length)) := by
            rw [Tuple.position_beyond (by omega), Tuple.position_beyond (by omega)]
          have e2 : q.position i = q.position (max (p.required.length + p.optional.length)
              (q.required.length + q.optional.length)) := by
            rw [Tuple.position_beyond (by omega), Tuple.position_beyond (by omega)]
          rwa [e1, e2]
      rw [ha, hb] at hcov
      exact hr j hj a b hcov U u
        (hel i u (meaning G a) hu (by rw [positionFam_tupleFams, ha]; rfl) j hj U hx)

theorem Covers.sound {G : NormalGraph ι} {R a b} (hc : Covers G R a b) (n : Nat)
    (hr : ∀ j, j < n → ∀ S T, R S T → FamLeAt G S T j)
    (W : WorldT n) (v : Val) : sem (meaning G) a n W v → sem (meaning G) b n W v := by
  by_cases hb : b = .top
  · subst hb; exact fun hv => sem_value hv
  cases a <;> cases b <;> simp only [Covers] at hc
  all_goals try contradiction
  all_goals try exact absurd rfl hb
  case pack.pack a bs c ds =>
    rintro ⟨vs, rfl, hs, hf⟩
    have src : ∀ p ∈ a :: bs, PackFits (tupleFams (meaning G) p) n W vs := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hf _ List.mem_cons_self
      · exact hf _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hp))
    have tgt : ∀ q ∈ c :: ds, PackFits (tupleFams (meaning G) q) n W vs := by
      intro q hq
      obtain ⟨p, hp, hpq⟩ := hc q hq
      exact covers_pack_sound hpq n hr W vs (src p hp)
    refine ⟨vs, rfl, hs, fun T hT => ?_⟩
    rcases List.mem_cons.mp hT with rfl | hT
    · exact tgt c List.mem_cons_self
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hT
      exact tgt q (List.mem_cons_of_mem _ hq)
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
  | some s => s.signatures.flatMap (fun p => p.1 ++ p.2.1.flatten ++ p.2.2) ++
      s.bounds.flatMap (·.2)
  | none => (G i).flatMap fun c => c.operands.flatten

/-- A scheme row's bound types: read at its own assignment, not under its
binders. -/
def boundReads (G : NormalGraph ι) (i : ι) : List ι :=
  match G.schemes i with
  | some s => s.bounds.flatMap (·.2)
  | none => []

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
    (reads G i).all (fun l => D.contains l &&
      (fv V l).all fun p => (fv V i).contains p ||
        (match G.schemes i with | some s => s.binders.contains p | none => false)) &&
    (boundReads G i).all fun l => (fv V l).all fun p => (fv V i).contains p

theorem freeOk_row [DecidableEq ι] {G : NormalGraph ι} {D : List ι} {V : FreeMap ι}
    (hF : FreeOk G D V = true) {i : ι} (hi : i ∈ D) :
    (G.params i = true → i ∈ fv V i) ∧ (∀ l ∈ reads G i, l ∈ D ∧ ∀ p ∈ fv V l,
      p ∈ fv V i ∨ (∃ s, G.schemes i = some s ∧ p ∈ s.binders)) ∧
    ∀ l ∈ boundReads G i, ∀ p ∈ fv V l, p ∈ fv V i := by
  have h := List.all_eq_true.mp hF i hi
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true,
    List.contains_iff_mem] at h
  refine ⟨fun hp => by simpa [hp] using h.1.1, fun l hl => ⟨by simpa using (h.1.2 l hl).1, fun p hp => ?_⟩,
    fun l hl p hp => by simpa using h.2 l hl p hp⟩
  have := (h.1.2 l hl).2 p hp
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
  have ⟨hself, hreads, hbounds⟩ := freeOk_row hF hi
  rw [qDenote_unfold, qDenote_unfold]
  unfold qLayer
  cases hp : G.params i
  · simp only [Bool.false_eq_true, if_false]
    cases hq : G.schemes i with
    | some s =>
      refine and_congr Iff.rfl (forall_congr' fun As => forall_congr' fun hl => imp_congr ?_ ?_)
      · -- The bounds are read at the scheme's own assignment.
        have hbr : ∀ b ∈ s.bounds, ∀ l ∈ b.2, l ∈ reads G i ∧ l ∈ boundReads G i := by
          intro b hb l hl'
          refine ⟨?_, ?_⟩
          · simp only [reads, hq]
            exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, hl'⟩)
          · simp only [boundReads, hq]
            exact List.mem_flatMap.mpr ⟨b, hb, hl'⟩
        unfold Bounded
        refine forall_congr' fun b => forall_congr' fun hbm => forall_congr' fun hbin =>
          forall_congr' fun j => forall_congr' fun hj => forall_congr' fun U =>
          forall_congr' fun u => ?_
        rw [assign_mem_eq η η' s.binders As hbin hl]
        refine imp_congr Iff.rfl ⟨fun ⟨l, hl', h⟩ => ⟨l, hl', ?_⟩, fun ⟨l, hl', h⟩ => ⟨l, hl', ?_⟩⟩
        · exact (ih j hj η η' l (hreads l (hbr b hbm l hl').1).1
            (fun p hp => hag p (hbounds l (hbr b hbm l hl').2 p hp)) U u).mp h
        · exact (ih j hj η η' l (hreads l (hbr b hbm l hl').1).1
            (fun p hp => hag p (hbounds l (hbr b hbm l hl').2 p hp)) U u).mpr h
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
          exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hps, hl⟩)
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

/-! ### Instance tables

An instance is checked by a finite table of entries `(row, context, image)`.
The context says what each binder in scope stands for: an instance type, or,
under a scheme the instance maps to another, that scheme's binder. Under its
context an entry's row means its image. Binder rows shared between scopes, as
the colouring of generic methods makes them, are told apart by the context. -/

/-- What the binders in scope stand for. -/
abbrev Ctx (ι : Type) := List (ι × List ι)

/-- Entries `(row, context, image)`. -/
abbrev InstTable (ι : Type) := List (ι × Ctx ι × List ι)

def entryImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (l : ι) : Option (List ι) :=
  (tbl.find? fun e => e.1 == l && e.2.1 == κ).map (·.2.2)

/-- A type's image: its rows' images, each an entry. -/
def tyImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (S : List ι) : Option (List ι) :=
  (S.mapM (entryImg tbl κ)).map List.flatten

def sigImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι)
    (p : List ι × List (List ι) × List ι) : Option (List ι × List (List ι) × List ι) := do
  return (← tyImg tbl κ p.1, ← p.2.1.mapM (tyImg tbl κ), ← tyImg tbl κ p.2.2)

/-- Entering a scheme mapped to another: its binders stand for the other's. -/
def enter [DecidableEq ι] (κ : Ctx ι) (src tgt : List ι) : Ctx ι :=
  src.zip (tgt.map ([·])) ++ κ.filter fun e => !src.contains e.1

/-- A clause with every operand replaced by its image. -/
def clauseImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (c : Clause (List ι)) :
    Clause (List ι) :=
  c.map fun S => (tyImg tbl κ S).getD []

/-- A bound's image: the target binder at the bound binder's position, and the
bound type's image under the outer context (a bound is read at the scheme's
own assignment, not under its binders). -/
def boundImg [DecidableEq ι] (tbl : InstTable ι) (κ : Ctx ι) (src tgt : List ι)
    (b : ι × List ι) : Option (ι × List ι) :=
  match (src.zip (tgt.map ([·]))).lookup b.1 with
  | some [q] => (tyImg tbl κ b.2).map (q, ·)
  | _ => none

/-- One entry. A parameter row's image is what the context gives it, or itself.
A row with no free row in the context's domain may be its own image. A clause
row's image is a clause row holding its clauses mapped. A scheme row's image is
a scheme row with as many binders, distinct parameter rows, whose signatures
are its own mapped with its binders standing for them, provided no free row of
the source, nor any row of a free row's image, is one of those binders. -/
def entryOk [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (V : FreeMap ι)
    (e : ι × Ctx ι × List ι) : Bool :=
  if G.params e.1 then e.2.2 == (e.2.1.lookup e.1).getD [e.1]
  else if e.2.2 == [e.1] && (fv V e.1).all (fun p => (e.2.1.lookup p).isNone) then true
  else match G.schemes e.1, e.2.2 with
    | some s, [j] =>
      match G.schemes j with
      | some s2 =>
        !G.params j && decide s2.binders.Nodup && s2.binders.length == s.binders.length &&
          s2.binders.all G.params &&
          (fv V e.1).all (fun p => match e.2.1.lookup p with
            | some U => U.all fun l => (fv V l).all fun q => !s2.binders.contains q
            | none => !s2.binders.contains p) &&
          s.signatures.mapM (sigImg tbl (enter e.2.1 s.binders s2.binders)) == some s2.signatures &&
          s.bounds.mapM (boundImg tbl e.2.1 s.binders s2.binders) == some s2.bounds
      | none => false
    | none, [j] =>
      G.plain e.1 && G.plain j &&
        (G e.1).all (fun c => c.operands.all fun S => (tyImg tbl e.2.1 S).isSome) &&
        G j == (G e.1).map (clauseImg tbl e.2.1)
    | _, _ => false

/-- The rows a table mentions. -/
def tableRows (tbl : InstTable ι) : List ι :=
  tbl.flatMap fun e => e.1 :: e.2.2 ++ e.2.1.flatMap (·.2)

/-- A checked table: its rows lie in a domain with a sound free-variable
certificate, and every entry is one of `entryOk`'s. -/
def TableOk [DecidableEq ι] (G : NormalGraph ι) (tbl : InstTable ι) (D : List ι)
    (V : FreeMap ι) : Bool :=
  FreeOk G D V && (tableRows tbl).all (D.contains ·) && tbl.all (entryOk G tbl V)

/-- Two assignments related by a context on a set of rows: a row the context
names means, on the left, its image's meaning on the right; any other row
means the same on both sides. -/
def RelK [DecidableEq ι] (G : NormalGraph ι) (κ : Ctx ι) (S : List ι) (ηL ηR : Assignment ι) :
    Prop :=
  ∀ p ∈ S, match κ.lookup p with
    | some U => ηL.1 p = qMeaning G ηR U
    | none => ηL.1 p = ηR.1 p

theorem entryImg_mem [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι} {l : ι} {T : List ι}
    (h : entryImg tbl κ l = some T) : (l, κ, T) ∈ tbl := by
  unfold entryImg at h
  cases hf : tbl.find? (fun e => e.1 == l && e.2.1 == κ) with
  | none => simp [hf] at h
  | some e =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨a, b, c⟩ := e
    simp only at hp h
    rw [← hp.1, ← hp.2, ← h]
    exact hm

/-- A union maps to the union of its rows' images. -/
theorem tyImg_iff [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι} {P Q : ι → Prop} :
    ∀ {S S' : List ι}, tyImg tbl κ S = some S' →
      (∀ l ∈ S, ∀ T, entryImg tbl κ l = some T → (P l ↔ ∃ l' ∈ T, Q l')) →
      ((∃ l ∈ S, P l) ↔ ∃ l' ∈ S', Q l')
  | [], S', h, _ => by
    have : S' = [] := by simpa [tyImg] using h.symm
    subst this; simp
  | l :: S, S', h, hper => by
    unfold tyImg at h
    cases hl : entryImg tbl κ l with
    | none => simp [List.mapM_cons, hl] at h
    | some T =>
      cases hs : S.mapM (entryImg tbl κ) with
      | none => simp [List.mapM_cons, hl, hs] at h
      | some Ts =>
        have hS' : S' = T ++ Ts.flatten := by
          simp [List.mapM_cons, hl, hs] at h; exact h.symm
        subst hS'
        have ih := tyImg_iff (S := S) (S' := Ts.flatten) (by simp [tyImg, hs])
          (fun l' hl' T' hT' => hper l' (List.mem_cons_of_mem _ hl') T' hT')
        have hh := hper l List.mem_cons_self T hl
        simp only [List.mem_cons, List.mem_append, exists_eq_or_imp] at ih ⊢
        constructor
        · rintro (h1 | h2)
          · obtain ⟨l', hl', q⟩ := hh.mp h1; exact ⟨l', .inl hl', q⟩
          · obtain ⟨l', hl', q⟩ := ih.mp h2; exact ⟨l', .inr hl', q⟩
        · rintro ⟨l', hl' | hl', q⟩
          · exact .inl (hh.mpr ⟨l', hl', q⟩)
          · exact .inr (ih.mpr ⟨l', hl', q⟩)

theorem mem_of_lookup [DecidableEq ι] {κ : List (ι × β)} {p : ι} {U : β}
    (h : κ.lookup p = some U) : (p, U) ∈ κ := by
  induction κ with
  | nil => simp at h
  | cons e κ ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.lookup_cons] at h
    by_cases ha : p = a
    · subst ha; simp at h; subst h; exact List.mem_cons_self
    · rw [beq_false_of_ne ha] at h; exact List.mem_cons_of_mem _ (ih h)

theorem lookup_zip_none [DecidableEq ι] {src : List ι} {ys : List β} {p : ι} (hp : p ∉ src) :
    (src.zip ys).lookup p = none := by
  induction src generalizing ys with
  | nil => rfl
  | cons b src ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [List.zip_cons_cons, List.lookup_cons]
      have hb : p ≠ b := fun e => hp (e ▸ List.mem_cons_self)
      rw [beq_false_of_ne hb]
      exact ih fun h => hp (List.mem_cons_of_mem _ h)

theorem lookup_append_none [DecidableEq ι] {xs ys : List (ι × β)} {p : ι}
    (h : xs.lookup p = none) : (xs ++ ys).lookup p = ys.lookup p := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.lookup_cons] at h
    by_cases ha : p = a
    · subst ha; simp at h
    · rw [beq_false_of_ne ha] at h
      simp only [List.cons_append, List.lookup_cons]
      rw [beq_false_of_ne ha]; exact ih h

theorem lookup_filter_nmem [DecidableEq ι] {κ : List (ι × β)} {src : List ι} {p : ι} (hp : p ∉ src) :
    (κ.filter fun e => !src.contains e.1).lookup p = κ.lookup p := by
  induction κ with
  | nil => rfl
  | cons e κ ih =>
    obtain ⟨a, b⟩ := e
    by_cases ha : a ∈ src
    · have hpa : p ≠ a := fun e => hp (e ▸ ha)
      rw [List.filter_cons_of_neg (by simp [ha]), ih]
      simp only [List.lookup_cons, beq_false_of_ne hpa]
    · rw [List.filter_cons_of_pos (by simp [ha])]
      cases hpa : p == a <;> simp [List.lookup_cons, hpa] <;> simpa using ih

/-- Outside the binders, entering changes nothing. -/
theorem enter_nmem [DecidableEq ι] (κ : Ctx ι) {src tgt : List ι} {p : ι} (hp : p ∉ src) :
    (enter κ src tgt).lookup p = κ.lookup p := by
  unfold enter
  rw [lookup_append_none (lookup_zip_none hp), lookup_filter_nmem hp]

/-- A binder entered stands for the binder at its position, and both sides are
given the same family there. -/
theorem enter_binder [DecidableEq ι] (ηL ηR : Assignment ι) :
    ∀ {src tgt : List ι} {As : List ValueFamily} {p : ι} {U : List ι},
      tgt.Nodup → src.length = As.length → tgt.length = As.length →
      (src.zip (tgt.map ([·]))).lookup p = some U →
      ∃ q, U = [q] ∧ (assign ηL src As).1 p = (assign ηR tgt As).1 q
  | [], _, _, _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp at h
  | b :: src, c :: tgt, [], _, _, _, h1, _, _ => by simp at h1
  | b :: src, c :: tgt, A :: As, p, U, hnd, h1, h2, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons] at h
    by_cases hb : p = b
    · subst hb
      simp only [beq_self_eq_true, Option.some.injEq] at h
      refine ⟨c, h.symm, ?_⟩
      rw [assign_cons_head, assign_cons_head]
    · rw [beq_false_of_ne hb] at h
      obtain ⟨q, hq, he⟩ := enter_binder ηL ηR (List.nodup_cons.mp hnd).2
        (by simpa using h1) (by simpa using h2) h
      refine ⟨q, hq, ?_⟩
      have hqt : q ∈ tgt := by
        have hm := (List.of_mem_zip (mem_of_lookup h)).2
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
        rw [hq] at hxe
        cases hxe; exact hx
      have hqc : q ≠ c := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hqt)
      have e1 := assign_cons_ne ηL src A As hb
      have e2 := assign_cons_ne ηR tgt A As hqc
      rw [e1, e2, he]

theorem mapM_some {f : α → Option α} :
    ∀ {xs ys : List α}, xs.mapM f = some ys → ys = xs.map (fun x => (f x).getD x) ∧
      ∀ x ∈ xs, (f x).isSome
  | [], ys, h => by simp at h; subst h; simp
  | x :: xs, ys, h => by
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some zs =>
        have hys : ys = y :: zs := by simp [List.mapM_cons, hx, hxs] at h; exact h.symm
        subst hys
        obtain ⟨h1, h2⟩ := mapM_some hxs
        refine ⟨by simp [hx, h1], ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · simp [hx]
        · exact h2 z hz

theorem lookup_zip_isSome [DecidableEq ι] {src : List ι} {ys : List β} {p : ι}
    (h : p ∈ src) (hl : src.length = ys.length) : ∃ U, (src.zip ys).lookup p = some U := by
  induction src generalizing ys with
  | nil => cases h
  | cons b src ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.zip_cons_cons, List.lookup_cons]
      by_cases hb : p = b
      · subst hb; simp
      · rw [beq_false_of_ne hb]
        exact ih ((List.mem_cons.mp h).resolve_left hb) (by simpa using hl)

theorem lookup_append_some [DecidableEq ι] {xs ys : List (ι × β)} {p : ι} {U : β}
    (h : xs.lookup p = some U) : (xs ++ ys).lookup p = some U := by
  induction xs with
  | nil => simp at h
  | cons e xs ih =>
    obtain ⟨a, b⟩ := e
    by_cases ha : p = a
    · subst ha; simp only [List.cons_append, List.lookup_cons, beq_self_eq_true] at h ⊢; exact h
    · simp only [List.lookup_cons, beq_false_of_ne ha] at h
      simp only [List.cons_append, List.lookup_cons, beq_false_of_ne ha]; exact ih h

/-- A binder entered stands for a target binder, given the same family on both
sides. -/
theorem enter_rel [DecidableEq ι] (κ : Ctx ι) (ηL ηR : Assignment ι) {src tgt : List ι}
    {As : List ValueFamily} {p : ι} (hp : p ∈ src) (hnd : tgt.Nodup)
    (h1 : src.length = As.length) (h2 : tgt.length = As.length) :
    ∃ q ∈ tgt, (enter κ src tgt).lookup p = some [q] ∧
      (assign ηL src As).1 p = (assign ηR tgt As).1 q := by
  obtain ⟨U, hU⟩ := lookup_zip_isSome (ys := tgt.map ([·])) hp (by simp [h1, h2])
  obtain ⟨q, rfl, he⟩ := enter_binder ηL ηR hnd h1 h2 hU
  have hq : q ∈ tgt := by
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp (List.of_mem_zip (mem_of_lookup hU)).2
    cases hxe; exact hx
  exact ⟨q, hq, by unfold enter; exact lookup_append_some hU, he⟩

theorem sigImg_some [DecidableEq ι] {tbl : InstTable ι} {κ : Ctx ι}
    {p q : List ι × List (List ι) × List ι} (h : sigImg tbl κ p = some q) :
    tyImg tbl κ p.1 = some q.1 ∧ p.2.1.mapM (tyImg tbl κ) = some q.2.1 ∧
      tyImg tbl κ p.2.2 = some q.2.2 := by
  unfold sigImg at h
  cases h1 : tyImg tbl κ p.1 with
  | none => simp [h1] at h
  | some a =>
    cases h2 : p.2.1.mapM (tyImg tbl κ) with
    | none => simp [h1, h2] at h
    | some b =>
      cases h3 : tyImg tbl κ p.2.2 with
      | none => simp [h1, h2, h3] at h
      | some c =>
        simp [h1, h2, h3] at h
        subst h; exact ⟨rfl, rfl, rfl⟩

/-- **Instance tables.** Under its context, an entry's row means its image. -/
theorem table_row [DecidableEq ι] {G : NormalGraph ι} {tbl : InstTable ι} {D : List ι}
    {V : FreeMap ι} (hok : TableOk G tbl D V = true) :
    ∀ n, ∀ ηL ηR : Assignment ι, ∀ e ∈ tbl, RelK G e.2.1 (fv V e.1) ηL ηR →
      ∀ (W : WorldT n) v, qDenote G (ηL, e.1) n W v ↔ qMeaning G ηR e.2.2 n W v := by
  simp only [TableOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hF, hrowsD⟩, hents⟩ := hok
  have inD : ∀ e ∈ tbl, e.1 ∈ D ∧ (∀ l ∈ e.2.2, l ∈ D) ∧
      ∀ p U, e.2.1.lookup p = some U → ∀ l ∈ U, l ∈ D := by
    intro e he
    have h := fun l hl => by simpa using hrowsD l hl
    refine ⟨h _ (List.mem_flatMap.mpr ⟨e, he, List.mem_cons_self⟩),
      fun l hl => h _ (List.mem_flatMap.mpr ⟨e, he, List.mem_cons_of_mem _ (List.mem_append_left _ hl)⟩),
      fun p U hU l hl => h _ (List.mem_flatMap.mpr ⟨e, he, List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨(p, U), mem_of_lookup hU, hl⟩))⟩)⟩
  have singleton : ∀ (η : Assignment ι) (j : ι) m (U : WorldT m) u,
      qMeaning G η [j] m U u ↔ qDenote G (η, j) m U u := fun η j m U u =>
    ⟨fun ⟨_, hm, h⟩ => by cases List.mem_singleton.mp hm; exact h,
     fun h => ⟨j, List.mem_singleton_self j, h⟩⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  rintro ηL ηR ⟨i, κ, T⟩ he hrel W v
  have hrow := hents _ he
  obtain ⟨hiD, _, hκD⟩ := inD _ he
  have ⟨hself, hreads, hbounds⟩ := freeOk_row hF hiD
  simp only at hrel hiD hκD
  -- A type whose rows have entries under a context, related on their free
  -- rows, means its image below the budget.
  have hty : ∀ (ηL' ηR' : Assignment ι) (κ' : Ctx ι) (S S' : List ι),
      tyImg tbl κ' S = some S' →
      (∀ l ∈ S, RelK G κ' (fv V l) ηL' ηR') →
      Agree (setSem (fun l => qDenote G (ηL', l)) S) (qMeaning G ηR' S') n := by
    intro ηL' ηR' κ' S S' hS hrl m hm U u
    exact tyImg_iff hS fun l hl T hT =>
      ih m hm ηL' ηR' (l, κ', T) (entryImg_mem hT) (hrl l hl) U u
  simp only [entryOk] at hrow
  cases hpar : G.params i
  · simp only [hpar, Bool.false_eq_true, if_false] at hrow
    by_cases hrig : (T == [i] && (fv V i).all (fun p => (κ.lookup p).isNone)) = true
    · -- its own image, with no free row in the context's domain
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
        Option.isNone_iff_eq_none] at hrig
      obtain ⟨rfl, hfree⟩ := hrig
      rw [singleton]
      exact agree_free hF n ηL ηR i hiD (fun p hp => by
        have := hrel p hp; rw [hfree p hp] at this; exact this) W v
    · have hrigF : (T == [i] && (fv V i).all (fun p => (κ.lookup p).isNone)) = false := by
        simpa using hrig
      simp only [hrigF, Bool.false_eq_true, if_false] at hrow
      cases hsch : G.schemes i with
      | some s =>
        cases hT : T with
        | nil => simp [hsch, hT] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hsch, hT] at hrow
          | nil =>
            simp only [hsch, hT] at hrow
            cases hs2 : G.schemes j with
            | none => simp [hs2] at hrow
            | some s2 =>
            simp only [hs2, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq,
              List.all_eq_true] at hrow
            obtain ⟨⟨⟨⟨⟨⟨hjp, hnd⟩, hlen⟩, hpars⟩, hcap⟩, hsigs⟩, hbnds⟩ := hrow
            rw [singleton, qDenote_unfold, qDenote_unfold]
            simp only [qLayer, hpar, hjp, hsch, hs2, Bool.false_eq_true, if_false]
            refine and_congr Iff.rfl ?_
            rw [hlen]
            refine forall_congr' fun As => forall_congr' fun hlA => imp_congr ?_ ?_
            · -- Each bound maps to the target's: the same family on the binders,
              -- and the bound types related at the outer assignments.
              obtain ⟨hbmap, hbsome⟩ := mapM_some hbnds
              unfold Bounded
              rw [hbmap]
              simp only [List.forall_mem_map]
              refine forall_congr' fun b => forall_congr' fun hb => ?_
              obtain ⟨⟨q, B'⟩, hbi⟩ := Option.isSome_iff_exists.mp (hbsome b hb)
              simp only [hbi, Option.getD_some]
              unfold boundImg at hbi
              split at hbi
              · rename_i q' hU
                obtain ⟨B'', hB'', hqB⟩ := Option.map_eq_some_iff.mp hbi
                cases hqB
                obtain ⟨q'', hq'', he⟩ := enter_binder ηL ηR hnd hlA.symm (hlen.trans hlA.symm) hU
                cases hq''
                have hb1 : b.1 ∈ s.binders := (List.of_mem_zip (mem_of_lookup hU)).1
                have hq2 : q ∈ s2.binders := by
                  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp (List.of_mem_zip (mem_of_lookup hU)).2
                  cases hxe; exact hx
                refine imp_congr (iff_of_true hb1 hq2) (forall_congr' fun j => forall_congr' fun hj =>
                  forall_congr' fun U => forall_congr' fun u => imp_congr (by rw [he]) ?_)
                have hbr : ∀ l ∈ b.2, l ∈ reads G i ∧ l ∈ boundReads G i := by
                  intro l hl'
                  refine ⟨?_, ?_⟩
                  · simp only [reads, hsch]
                    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, hl'⟩)
                  · simp only [boundReads, hsch]
                    exact List.mem_flatMap.mpr ⟨b, hb, hl'⟩
                exact tyImg_iff hB'' fun l hl T hT =>
                  ih j hj ηL ηR (l, κ, T) (entryImg_mem hT)
                    (fun p hp => hrel p (hbounds l (hbr l hl).2 p hp)) U u
              · simp at hbi
            -- Inside, the relation holds on each signature row's free rows.
            have hrel' : ∀ l ∈ reads G i, RelK G (enter κ s.binders s2.binders) (fv V l)
                (assign ηL s.binders As) (assign ηR s2.binders As) := by
              intro l hl p hp
              by_cases hb : p ∈ s.binders
              · obtain ⟨q, hq, hk, he⟩ := enter_rel κ ηL ηR hb hnd hlA.symm (hlen.trans hlA.symm)
                rw [hk]
                show (assign ηL s.binders As).1 p = qMeaning G _ [q]
                rw [he]
                funext m U u
                apply propext
                rw [singleton, qDenote_unfold]
                simp [qLayer, hpars q hq]
              · rw [enter_nmem κ hb, assign_nmem ηL s.binders As hb]
                have hpi : p ∈ fv V i := by
                  rcases (hreads l hl).2 p hp with h1 | ⟨s', hs', h2⟩
                  · exact h1
                  · rw [hsch] at hs'; cases hs'; exact absurd h2 hb
                have hr := hrel p hpi
                have hc := hcap p hpi
                cases hk : κ.lookup p with
                | none =>
                  rw [hk] at hr hc
                  have : p ∉ s2.binders := by simpa using hc
                  rw [assign_nmem ηR s2.binders As this]; exact hr
                | some U =>
                  rw [hk] at hr
                  simp only [hk, List.all_eq_true, Bool.not_eq_true', List.contains_iff_mem,
                    decide_eq_false_iff_not] at hc
                  rw [hr]
                  funext m W' u
                  apply propext
                  constructor
                  · rintro ⟨l', hl', h⟩
                    refine ⟨l', hl', (agree_free hF m ηR _ l' (hκD p U hk l' hl')
                      (fun q hq => ?_) W' u).mp h⟩
                    have := (hc l' hl') q hq
                    rw [assign_nmem ηR s2.binders As (by simpa using this)]
                  · rintro ⟨l', hl', h⟩
                    refine ⟨l', hl', (agree_free hF m ηR _ l' (hκD p U hk l' hl')
                      (fun q hq => ?_) W' u).mpr h⟩
                    have := (hc l' hl') q hq
                    rw [assign_nmem ηR s2.binders As (by simpa using this)]
            obtain ⟨hmap, _⟩ := mapM_some hsigs
            unfold instanceSigs
            rw [hmap]
            simp only [List.map_map]
            refine callsT_congr s.signatures _ _ (fun p hps => ?_) W v
            have hin : ∀ l ∈ p.1 ++ p.2.1.flatten ++ p.2.2, l ∈ reads G i := fun l hl => by
              simp only [reads, hsch]
              exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨p, hps, hl⟩)
            obtain ⟨q, hq⟩ : ∃ q, sigImg tbl (enter κ s.binders s2.binders) p = some q := by
              obtain ⟨_, hsome⟩ := mapM_some hsigs
              exact Option.isSome_iff_exists.mp (hsome p hps)
            obtain ⟨h1, h2, h3⟩ := sigImg_some hq
            simp only [Function.comp, hq, Option.getD_some]
            refine ⟨hty _ _ _ _ _ h1 fun l hl => hrel' l (hin l (by simp [hl])), ?_,
              hty _ _ _ _ _ h3 fun l hl => hrel' l (hin l (by simp [hl]))⟩
            have hargs : ∀ (Ss Ts : List (List ι)), Ss.mapM (tyImg tbl (enter κ s.binders s2.binders)) = some Ts →
                (∀ S ∈ Ss, ∀ l ∈ S, l ∈ reads G i) →
                ArgsAgree n (Ss.map (setSem fun l => qDenote G (assign ηL s.binders As, l)))
                  (Ts.map (qMeaning G (assign ηR s2.binders As))) := by
              intro Ss
              induction Ss with
              | nil => intro Ts h _; simp at h; subst h; exact .nil
              | cons S Ss ihs =>
                intro Ts h hSs
                cases hS : tyImg tbl (enter κ s.binders s2.binders) S with
                | none => simp [List.mapM_cons, hS] at h
                | some S' =>
                  cases hr : Ss.mapM (tyImg tbl (enter κ s.binders s2.binders)) with
                  | none => simp [List.mapM_cons, hS, hr] at h
                  | some Ts' =>
                    have : Ts = S' :: Ts' := by simp [List.mapM_cons, hS, hr] at h; exact h.symm
                    subst this
                    exact .cons (hty _ _ _ _ _ hS fun l hl => hrel' l (hSs S List.mem_cons_self l hl))
                      (ihs Ts' hr fun T hT => hSs T (List.mem_cons_of_mem _ hT))
            exact hargs _ _ h2 fun S hS l hl => hin l (by
              simp only [List.mem_append, List.mem_flatten]
              exact .inl (.inr ⟨S, hS, hl⟩))
      | none =>
        cases hT : T with
        | nil => simp [hsch, hT] at hrow
        | cons j rest =>
          cases rest with
          | cons _ _ => simp [hsch, hT] at hrow
          | nil =>
            simp only [hsch, hT, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hrow
            obtain ⟨⟨⟨hip, hjp⟩, hops⟩, hG⟩ := hrow
            have hl : qDenote G (ηL, i) n W v ↔
                semList (setSem fun l => qDenote G (ηL, l)) (G i) n W v :=
              unfold_plain (G := { G with env := ηL }) hip n W v
            have hr : qMeaning G ηR [j] n W v ↔ semList (qMeaning G ηR) (G j) n W v := by
              rw [singleton]
              exact unfold_plain (G := { G with env := ηR }) hjp n W v
            rw [hl, hr, hG]
            simp only [semList, setSem, List.mem_map]
            have clause : ∀ c ∈ G i,
                sem (setSem fun l => qDenote G (ηL, l)) c n W v ↔
                  sem (qMeaning G ηR) (clauseImg tbl κ c) n W v := by
              intro c hc
              let r : List ι → List ι := fun S => if S ∈ c.operands then S else []
              have hcr : c.map r = c := map_of_operands fun S hS => by simp [r, hS]
              unfold clauseImg
              rw [sem_map, ← hcr, sem_map, sem_map]
              apply sem_congr _ _ n (fun S => ?_) c W v
              by_cases hS : S ∈ c.operands
              · simp only [r, hS, if_true]
                obtain ⟨S', hS'⟩ := Option.isSome_iff_exists.mp (by simpa using hops c hc S hS)
                rw [hS', Option.getD_some]
                exact hty ηL ηR κ S S' hS' fun l hl p hp => hrel p (by
                  have hlr : l ∈ reads G i := by
                    simp only [reads, hsch]
                    exact List.mem_flatMap.mpr ⟨c, hc, List.mem_flatten.mpr ⟨S, hS, hl⟩⟩
                  rcases (hreads l hlr).2 p hp with h1 | ⟨s', hs', _⟩
                  · exact h1
                  · rw [hsch] at hs'; cases hs')
              · simp only [r, hS, if_false]
                have : tyImg tbl κ [] = some [] := by simp [tyImg]
                rw [this, Option.getD_some]
                intro m _ U u
                simp [setSem, qMeaning]
            constructor
            · rintro ⟨c, hc, h⟩
              exact ⟨_, ⟨c, hc, rfl⟩, (clause c hc).mp h⟩
            · rintro ⟨_, ⟨c, hc, rfl⟩, h⟩
              exact ⟨c, hc, (clause c hc).mpr h⟩
  · -- a parameter row
    simp only [hpar, if_true, beq_iff_eq] at hrow
    subst hrow
    have hr := hrel i (hself hpar)
    rw [qDenote_unfold]
    simp only [qLayer, hpar, if_true]
    cases hk : κ.lookup i with
    | none =>
      rw [hk] at hr
      simp only [Option.getD_none]
      rw [singleton, qDenote_unfold]
      simp only [qLayer, hpar, if_true]
      rw [hr]
    | some U =>
      rw [hk] at hr
      simp only [Option.getD_some]
      rw [hr]

theorem assign_zip_map [DecidableEq ι] (η : Assignment ι) (F : List ι → ValueFamily) :
    ∀ {bs : List ι} {θs : List (List ι)} {b : ι} {U : List ι},
      (bs.zip θs).lookup b = some U → (assign η bs (θs.map F)).1 b = (F U).1
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | c :: bs, θ :: θs, b, U, h => by
    simp only [List.zip_cons_cons, List.lookup_cons] at h
    by_cases hb : b = c
    · subst hb
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      simp only [List.map_cons]
      exact assign_cons_head η b bs (F θ) (θs.map F)
    · rw [beq_false_of_ne hb] at h
      simp only [List.map_cons]
      rw [assign_cons_ne η bs (F θ) (θs.map F) hb]
      exact assign_zip_map η F h

/-- A member of a scheme row meets each checked instance of its signatures. -/
theorem inst_sound [DecidableEq ι] {G : NormalGraph ι} {T : List ι} {i : ι} {s : SchemeRow ι}
    {tbl : InstTable ι} {θs : List (List ι)} {D : List ι} {V : FreeMap ι} {L : Ops ι}
    (hp : G.params i = false) (hq : G.schemes i = some s) (hlen : θs.length = s.binders.length)
    (hbnd : ∀ b ∈ s.bounds, ∀ U, (s.binders.zip θs).lookup b.1 = some U →
      FamLe (meaning G U) (meaning G b.2))
    (hok : TableOk G tbl D V = true)
    (hL : ∀ q ∈ L, ∃ p ∈ s.signatures, sigImg tbl (s.binders.zip θs) p = some q)
    (hT : expand G T = [.arrs L []]) : FamLe (meaning G [i]) (meaning G T) := by
  intro n W v hv
  obtain ⟨_, hm, hv⟩ := hv
  cases List.mem_singleton.mp hm
  have hs := (qDenote_unfold G (G.env, i) n W v).mp hv
  simp only [qLayer, hp, hq, Bool.false_eq_true, if_false] at hs
  obtain ⟨hinv, hall⟩ := hs
  let As : List ValueFamily := θs.map fun U => ⟨meaning G U, meaning_valueFam G U⟩
  have hbounded : Bounded (fun η' S => setSem (fun l => qDenote G (η', l)) S) G.env s As n := by
    intro b hb hbin j _ U' u hu
    obtain ⟨θ, hθ⟩ := lookup_zip_isSome (ys := θs) hbin (by omega)
    rw [assign_zip_map G.env (fun U => ⟨meaning G U, meaning_valueFam G U⟩) hθ] at hu
    exact hbnd b hb θ hθ j U' u hu
  have hc := (hall As (by simp [As, hlen]) hbounded).2
  have hTp := plain_of_mem_expand (G := G) (S := T) (c := .arrs L []) (by simp [hT])
  refine (expand_sem G T hTp n W v).mpr ⟨.arrs L [], by simp [hT], ?_⟩
  refine ⟨⟨hinv, fun q' hq' => ?_⟩, ⟨hinv, by simp⟩⟩
  obtain ⟨q, hqL, rfl⟩ := List.mem_map.mp hq'
  obtain ⟨p, hps, hsig⟩ := hL q hqL
  have hpr := hc _ (List.mem_map_of_mem hps)
  obtain ⟨h1, h2, h3⟩ := sigImg_some hsig
  -- The instance's assignment is related to the graph's by the binders' images.
  have hrel : ∀ l, RelK G (s.binders.zip θs) (fv V l) (assign G.env s.binders As) G.env := by
    intro l b _
    cases hk : (s.binders.zip θs).lookup b with
    | none =>
      have hb : b ∉ s.binders := fun hb => by
        obtain ⟨U, hU⟩ := lookup_zip_isSome (ys := θs) hb (by omega)
        rw [hU] at hk; cases hk
      exact assign_nmem _ _ _ hb
    | some U => exact assign_zip_map G.env (fun U => ⟨meaning G U, meaning_valueFam G U⟩) hk
  have hfam : ∀ S S', tyImg tbl (s.binders.zip θs) S = some S' →
      setSem (fun l => qDenote G (assign G.env s.binders As, l)) S = meaning G S' := by
    intro S S' hS
    funext m W' u
    exact propext (tyImg_iff hS fun l _ T hT =>
      table_row hok m _ G.env (l, _, T) (entryImg_mem hT) (hrel l) W' u)
  have hargs : ∀ (Ss Ts : List (List ι)), Ss.mapM (tyImg tbl (s.binders.zip θs)) = some Ts →
      Ss.map (setSem fun l => qDenote G (assign G.env s.binders As, l)) = Ts.map (meaning G) := by
    intro Ss
    induction Ss with
    | nil => intro Ts h; simp at h; subst h; rfl
    | cons S Ss ihs =>
      intro Ts h
      cases hS : tyImg tbl (s.binders.zip θs) S with
      | none => simp [List.mapM_cons, hS] at h
      | some S' =>
        cases hr : Ss.mapM (tyImg tbl (s.binders.zip θs)) with
        | none => simp [List.mapM_cons, hS, hr] at h
        | some Ts' =>
          have : Ts = S' :: Ts' := by simp [List.mapM_cons, hS, hr] at h; exact h.symm
          subst this
          simp only [List.map_cons, hfam S S' hS, ihs Ts' hr]
  have e1 := hfam _ _ h1
  have e3 := hfam _ _ h3
  have e2 := hargs _ _ h2
  simp only [e1, e2, e3] at hpr
  exact hpr

/-- Structural rules compose completed proofs. They cannot bypass the guarded
coverage obligation for any row of a recursive table. -/
inductive Sub (G : NormalGraph ι) : List ι → List ι → Prop where
  | core : Core G S T → Sub G S T
  | subset : (∀ i ∈ S, i ∈ T) → Sub G S T
  | trans : Sub G S U → Sub G U T → Sub G S T
  /-- **Instantiation.** A scheme row is below an arrow type whose signatures
  are images of its own under one checked instance map. -/
  | inst [DecidableEq ι] {i : ι} {s : SchemeRow ι} {tbl : InstTable ι} {θs : List (List ι)}
      {D : List ι} {V : FreeMap ι} {L : Ops ι} :
      G.params i = false → G.schemes i = some s → θs.length = s.binders.length →
      (∀ b ∈ s.bounds, ∀ U, (s.binders.zip θs).lookup b.1 = some U →
        Core G U b.2 ∨ ∀ l ∈ U, l ∈ b.2) →
      TableOk G tbl D V = true →
      (∀ q ∈ L, ∃ p ∈ s.signatures, sigImg tbl (s.binders.zip θs) p = some q) →
      expand G T = [.arrs L []] → Sub G [i] T
  /-- **Renaming.** A type is below one holding its rows' images under a checked
  instance table with the empty context: the same rows up to renaming the
  binders of the schemes they reach. -/
  | table [DecidableEq ι] {tbl : InstTable ι} {D : List ι} {V : FreeMap ι} :
      TableOk G tbl D V = true →
      (∀ l ∈ S, ∃ U, entryImg tbl [] l = some U ∧ ∀ x ∈ U, x ∈ T) → Sub G S T
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
  | inst hp hq hlen hbnd hok hL hT =>
    exact fun η => inst_sound (G := reassign G η) hp hq hlen (fun b hb U hU => by
      rcases hbnd b hb U hU with hc | hsub
      · exact Core.sound (G := reassign G η) hc
      · rintro n W v ⟨l, hl, hv⟩; exact ⟨l, hsub l hl, hv⟩) hok hL hT
  | table hok hS =>
    intro η n W v hv
    obtain ⟨l, hl, hv⟩ := hv
    obtain ⟨U, hU, hUT⟩ := hS l hl
    have hr := (table_row hok n η η (l, [], U) (entryImg_mem hU)
      (fun p _ => by simp [RelK]) W v).mp hv
    obtain ⟨x, hx, hxv⟩ := hr
    exact ⟨x, hUT x hx, hxv⟩
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
    exact ⟨(hsig []).1, fun As _ _ => hsig As⟩

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
