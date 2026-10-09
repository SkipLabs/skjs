import Verification.Types.PositiveGraphs
import Verification.Types.PositiveRules

/- A syntax-preserving import of a closed normal graph. The correspondence is
   proved from mapped production rows, including quantified callable rows and
   the array realm; no denotation equality is a hypothesis.

   A native kernel must include the reviewed Promise/PromiseLike equations,
   stable-value bounds and the realm's ArrayProto closure. Payloads enter by
   semantic assignment. This file does not construct that reviewed kernel,
   validate an EquationLowering head map, or identify a source application
   Promise<User> with such a semantic application. -/
namespace Verification.QualifiedTemplateEmbedding
open PositiveGraphs PositiveNormalization Tower CallEffects

variable {ι κ : Type}

def mapScheme (e : ι → κ) (s : SchemeRow ι) : SchemeRow κ where
  binders := s.binders.map e
  signatures := s.signatures.map (Arrow.map (List.map e))
  bounds := s.bounds.map fun b => (e b.1, b.2.map e)
  variadic := s.variadic.map (RestArrow.map (List.map e))
  resolution := s.resolution

def mapRealm (e : ι → κ) (r : ArrayRealm ι) : ArrayRealm κ :=
  ⟨r.proto.map e, r.keys⟩

/-- Row-preserving imports retain every dependency of the template, including
   realm dependencies. Extra source rows are unrestricted. -/
structure Embedding (G : NormalGraph ι) (H : NormalGraph κ) where
  node : ι → κ
  injective : Function.Injective node
  rows : ∀ i, H.rows (node i) = (G.rows i).map (Clause.map (List.map node))
  kinds : ∀ i, H.parameterKinds (node i) = G.parameterKinds i
  schemes : ∀ i, H.schemes (node i) = (G.schemes i).map (mapScheme node)
  meets : ∀ i, H.meets (node i) = (G.meets i).map
    (fun q => (node q.1, q.2.map (Clause.map (List.map node))))
  meetParams : ∀ i, H.meetParams (node i) = (G.meetParams i).map node
  realm : H.realm = G.realm.map (mapRealm node)
  /-- Domain membership is retained at each mapped callable row. -/
  domains : ∀ i s, G.schemes i = some s → ∀ As,
    H.domain.allowed (mapScheme node s) As ↔ G.domain.allowed s As

def pull (e : ι → κ) (η : MixedAssignment κ) : MixedAssignment ι :=
  ⟨fun i => η.1 (e i), fun i => η.2 (e i)⟩

@[simp] theorem pull_empty (e : ι → κ) :
    pull e (ParameterAssignment.empty .mixed) = ParameterAssignment.empty .mixed := rfl

theorem exists_map {α β : Type} (f : α → β) (S : List α) (P : β → Prop) :
    (∃ i ∈ S.map f, P i) ↔ ∃ i ∈ S, P (f i) := by
  constructor
  · rintro ⟨i, hi, h⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact ⟨j, hj, h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨f i, List.mem_map.mpr ⟨i, hi, rfl⟩, h⟩

theorem setSem_map (e : ι → κ) (X : κ → Fam) (S : List ι) :
    setSem X (S.map e) = setSem (fun i => X (e i)) S := by
  funext n W v
  apply propext
  exact exists_map e S _

open Classical in
theorem pull_assign (e : ι → κ) (he : Function.Injective e)
    (η : MixedAssignment κ) (bs : List ι) (As : List MixedFamily) :
    pull e (assign η (bs.map e) As) = assign (pull e η) bs As := by
  apply Subtype.ext
  funext p
  induction bs generalizing As with
  | nil => simp [pull, assign]
  | cons b bs ih =>
    cases As with
    | nil => simp [pull, assign]
    | cons A As =>
      by_cases hp : p = b
      · subst p
        simp only [List.map_cons, pull, assign_cons_head]
      · have hep : e p ≠ e b := fun h => hp (he h)
        simp only [List.map_cons, pull, assign_cons_ne _ _ _ _ hep,
          assign_cons_ne _ _ _ _ hp]
        exact ih As

theorem Embedding.params {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) (i : ι) : H.params (E.node i) = G.params i := by
  simp [NormalGraph.params, E.kinds]

theorem Embedding.plain {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) (i : ι) : H.plain (E.node i) = G.plain i := by
  simp [NormalGraph.plain, E.params, E.schemes, E.meets]

theorem Embedding.clauses {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) (i : ι) :
    H (E.node i) = (G i).map (Clause.map (List.map E.node)) := by
  simp only [NormalGraph.clauses, E.plain]
  split <;> simp [E.rows]

theorem Embedding.arguments {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) (η : MixedAssignment κ) (X : List κ → Fam)
    (S : List ι) :
    graphArguments H η X (S.map E.node) =
      graphArguments G (pull E.node η) (fun A => X (A.map E.node)) S := by
  funext n W vs
  apply propext
  simp only [graphArguments, exists_map, E.kinds]
  refine exists_congr fun i => and_congr Iff.rfl ?_
  by_cases hk : G.parameterKinds i = some .arguments
  · simp [hk, pull]
  · simp only [hk, ite_false, E.clauses, exists_map, clauseArguments_map]

theorem Embedding.realm_sem {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) (X : List κ → Fam) (c : Clause (List ι)) :
    realmInvariant H X (c.map (List.map E.node)) =
      realmInvariant G (fun S => X (S.map E.node)) c := by
  simp only [realmInvariant, E.realm, Clause.record_map]
  cases G.realm <;> rfl

theorem Embedding.row_sem {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) (Z X : List κ → Fam) (η : MixedAssignment κ)
    (c : Clause (List ι)) :
    rowSem H Z X (graphArguments H η X) (c.map (List.map E.node)) =
      rowSem G (fun S => Z (S.map E.node)) (fun S => X (S.map E.node))
        (graphArguments G (pull E.node η) (fun S => X (S.map E.node))) c := by
  unfold rowSem
  rw [semWithArgs_map, E.realm_sem]
  simp only [E.arguments]

theorem Embedding.values {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) {X : MixedAssignment ι × ι → Fam}
    {Y : MixedAssignment κ × κ → Fam}
    (h : ∀ η i, Y (η,E.node i) = X (pull E.node η,i))
    (η : MixedAssignment κ) (S : List ι) :
    setSem (fun i => Y (η,i)) (S.map E.node) =
      setSem (fun i => X (pull E.node η,i)) S := by
  rw [setSem_map]
  congr 1
  funext i
  exact h η i

theorem Embedding.instance {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) {X : MixedAssignment ι × ι → Fam}
    {Y : MixedAssignment κ × κ → Fam}
    (h : ∀ η i, Y (η,E.node i) = X (pull E.node η,i))
    (η : MixedAssignment κ) (s : SchemeRow ι) (As : List MixedFamily) :
    instanceTWithArgs (fun θ S => setSem (fun i => Y (θ,i)) S)
      η (mapScheme E.node s) As (graphArguments H) =
    instanceTWithArgs (fun θ S => setSem (fun i => X (θ,i)) S)
      (pull E.node η) s As (graphArguments G) := by
  have hv : ∀ S,
      setSem (fun i => Y (assign η (s.binders.map E.node) As,i)) (S.map E.node) =
      setSem (fun i => X (assign (pull E.node η) s.binders As,i)) S := by
    intro S
    rw [E.values h, pull_assign E.node E.injective]
  have ha : ∀ S,
      graphArguments H (assign η (s.binders.map E.node) As)
        (setSem fun i => Y (assign η (s.binders.map E.node) As,i)) (S.map E.node) =
      graphArguments G (assign (pull E.node η) s.binders As)
        (setSem fun i => X (assign (pull E.node η) s.binders As,i)) S := by
    intro S
    rw [E.arguments, pull_assign E.node E.injective]
    congr 1
    funext S
    exact hv S
  unfold instanceTWithArgs instanceSigs instanceRestsWithArgs
  simp only [mapScheme, List.map_map]
  congr 2
  · congr 1
    funext a
    simp only [Function.comp_apply, Arrow.map, Contract.map, hv]
    congr 1
    simp only [List.map_map, Function.comp_def, hv]
  · congr 1
    funext a
    simp only [Function.comp_apply, RestArrow.map, RestArrow.mapWith,
      Contract.map, hv, ha]
    congr 2
    simp only [List.map_map, Function.comp_def, hv]

theorem Embedding.bound {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) {X : MixedAssignment ι × ι → Fam}
    {Y : MixedAssignment κ × κ → Fam}
    (h : ∀ η i, Y (η,E.node i) = X (pull E.node η,i))
    (η : MixedAssignment κ) (S : List ι) :
    (mixedParameters H).bound η (setSem fun i => Y (η,i)) (S.map E.node) =
      (mixedParameters G).bound (pull E.node η)
        (setSem fun i => X (pull E.node η,i)) S := by
  funext n W u
  cases u with
  | inl v => exact congrFun (congrFun (congrFun (E.values h η S) n) W) v
  | inr vs =>
    change graphArguments H η (setSem fun i => Y (η,i)) (S.map E.node) n W vs = _
    rw [E.arguments]
    have hv := funext (E.values h η)
    rw [hv]
    rfl

theorem Embedding.bounded {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) {X : MixedAssignment ι × ι → Fam}
    {Y : MixedAssignment κ × κ → Fam}
    (h : ∀ η i, Y (η,E.node i) = X (pull E.node η,i))
    (η : MixedAssignment κ) (s : SchemeRow ι) (As : List MixedFamily) (n : Nat) :
    Bounded (fun θ S => (mixedParameters H).bound θ (setSem fun i => Y (θ,i)) S)
      η (mapScheme E.node s) As n ↔
    Bounded (fun θ S => (mixedParameters G).bound θ (setSem fun i => X (θ,i)) S)
      (pull E.node η) s As n := by
  have hmem : ∀ i, E.node i ∈ s.binders.map E.node ↔ i ∈ s.binders := by
    intro i
    constructor
    · intro hi
      obtain ⟨j,hj,hji⟩ := List.mem_map.mp hi
      exact E.injective hji ▸ hj
    · exact fun hi => List.mem_map.mpr ⟨i,hi,rfl⟩
  unfold Bounded
  simp only [mapScheme, List.forall_mem_map, hmem, E.bound h]
  have hp : ∀ i, (assign η (s.binders.map E.node) As).1 (E.node i) =
      (assign (pull E.node η) s.binders As).1 i :=
    fun i => congrFun (congrArg Subtype.val (pull_assign E.node E.injective η s.binders As)) i
  simp only [hp]

theorem Embedding.scheme_sem {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) {X : MixedAssignment ι × ι → Fam}
    {Y : MixedAssignment κ × κ → Fam}
    (h : ∀ η i, Y (η,E.node i) = X (pull E.node η,i))
    (η : MixedAssignment κ) (s : SchemeRow ι) (hs : ∃ i, G.schemes i = some s) :
    schemeSemWithArgs (mixedParameters H) (fun θ S => setSem (fun i => Y (θ,i)) S)
      η (mapScheme E.node s) =
    schemeSemWithArgs (mixedParameters G) (fun θ S => setSem (fun i => X (θ,i)) S)
      (pull E.node η) s := by
  obtain ⟨i, hs⟩ := hs
  funext n W v
  apply propext
  simp only [schemeSemWithArgs, boundedSem, mapScheme, List.length_map]
  refine and_congr Iff.rfl (forall_congr' fun q => forall_congr' fun hq => forall_congr' fun As => imp_congr_right fun _ => ?_)
  exact imp_congr (E.domains i s hs As) (imp_congr (E.bounded h η s As q)
    (iff_of_eq (congrFun (congrFun (congrFun (E.instance h η s As) q) (trunc q hq W)) v)))

theorem Embedding.row_values {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) {X : MixedAssignment ι × ι → Fam}
    {Y : MixedAssignment κ × κ → Fam}
    (h : ∀ η i, Y (η,E.node i) = X (pull E.node η,i))
    (η : MixedAssignment κ) (c : Clause (List ι)) :
    rowSem H (setSem fun i => Y (ParameterAssignment.empty .mixed,i))
      (setSem fun i => Y (η,i))
      (graphArguments H η (setSem fun i => Y (η,i))) (c.map (List.map E.node)) =
    rowSem G (setSem fun i => X (ParameterAssignment.empty .mixed,i))
      (setSem fun i => X (pull E.node η,i))
      (graphArguments G (pull E.node η) (setSem fun i => X (pull E.node η,i))) c := by
  rw [E.row_sem]
  have hz := funext (E.values h (ParameterAssignment.empty .mixed))
  simp only [pull_empty] at hz
  rw [hz, funext (E.values h η)]

theorem Embedding.row_set {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) {X : MixedAssignment ι × ι → Fam}
    {Y : MixedAssignment κ × κ → Fam}
    (h : ∀ η i, Y (η,E.node i) = X (pull E.node η,i))
    (η : MixedAssignment κ) (cs : List (Clause (List ι))) :
    setSem (rowSem H (setSem fun i => Y (ParameterAssignment.empty .mixed,i))
      (setSem fun i => Y (η,i)) (graphArguments H η (setSem fun i => Y (η,i))))
        (cs.map (Clause.map (List.map E.node))) =
    setSem (rowSem G (setSem fun i => X (ParameterAssignment.empty .mixed,i))
      (setSem fun i => X (pull E.node η,i))
      (graphArguments G (pull E.node η) (setSem fun i => X (pull E.node η,i)))) cs := by
  rw [setSem_map]
  congr 1
  funext c
  exact E.row_values h η c

theorem Embedding.part {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) {X : MixedAssignment ι × ι → Fam}
    {Y : MixedAssignment κ × κ → Fam}
    (h : ∀ η i, Y (η,E.node i) = X (pull E.node η,i))
    (η : MixedAssignment κ) (i : ι) :
    partSemWithArgs H (mixedParameters H) Y η (E.node i) =
      partSemWithArgs G (mixedParameters G) X (pull E.node η) i := by
  unfold partSemWithArgs
  simp only [E.params, E.schemes]
  by_cases hp : G.params i = true
  · simp only [hp, ite_true, mixedParameters, E.kinds, pull]
  · simp only [hp]
    cases hs : G.schemes i with
    | some s =>
      simp only [Option.map_some]
      exact E.scheme_sem h η s ⟨i, hs⟩
    | none =>
      simp only [Option.map_none, E.clauses]
      exact E.row_set h η (G i)

/-- Exact layer naturality, derived for all four production row cases. -/
theorem Embedding.layer {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) {X : MixedAssignment ι × ι → Fam}
    {Y : MixedAssignment κ × κ → Fam}
    (h : ∀ η i, Y (η,E.node i) = X (pull E.node η,i))
    (η : MixedAssignment κ) (i : ι) :
    qLayerWithArgs H (mixedParameters H) Y (η,E.node i) =
      qLayerWithArgs G (mixedParameters G) X (pull E.node η,i) := by
  unfold qLayerWithArgs
  simp only [E.params, E.schemes]
  by_cases hp : G.params i = true
  · simp only [hp, ite_true, mixedParameters, E.kinds, pull]
  · simp only [hp]
    cases hs : G.schemes i with
    | some s =>
      simp only [Option.map_some]
      exact E.scheme_sem h η s ⟨i, hs⟩
    | none =>
      simp only [Option.map_none, E.meets]
      cases hm : G.meets i with
      | none =>
        simp only [Option.map_none, E.clauses]
        exact E.row_set h η (G i)
      | some q =>
        simp only [Bool.false_eq_true, ite_false, Option.map_some, E.part h,
          E.meetParams, List.forall_mem_map]
        change (fun n W v => _ ∧ setSem (rowSem H
          (setSem fun i => Y (ParameterAssignment.empty .mixed,i))
          (setSem fun i => Y (η,i)) (graphArguments H η (setSem fun i => Y (η,i))))
          (q.2.map (Clause.map (List.map E.node))) n W v) = _
        rw [E.row_set h]
        rfl

/-- Every finite approximation agrees with the imported closed template.
   The induction hypothesis comes from the preceding approximation;
   descriptor validity never reads any approximation. -/
theorem Embedding.approx {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) (k : Nat) (η : MixedAssignment κ) (i : ι) :
    Tower.approx (qLayerWithArgs H (mixedParameters H)) k (η,E.node i) =
      Tower.approx (qLayerWithArgs G (mixedParameters G)) k (pull E.node η,i) := by
  induction k generalizing η i with
  | zero => rfl
  | succ k ih => exact E.layer ih η i

/-- Interpretation preservation for an imported closed standard template,
   with arbitrary external source rows and arbitrary semantic arguments. -/
theorem Embedding.denote {G : NormalGraph ι} {H : NormalGraph κ}
    (E : Embedding G H) (η : MixedAssignment κ) (i : ι) :
    qDenoteWithArgs H (mixedParameters H) (η,E.node i) =
      qDenoteWithArgs G (mixedParameters G) (pull E.node η,i) := by
  funext n W v
  exact congrFun (congrFun (congrFun (E.approx (n+1) η i) n) W) v

#print axioms Embedding.layer
#print axioms Embedding.denote

variable {υ : Type}

/-- A concrete closed import: the standard summand retains mapped standard
   rows. The other summand can contain arbitrary rows and dependencies. -/
def extend (G : NormalGraph ι) (U : NormalGraph (ι ⊕ υ)) : NormalGraph (ι ⊕ υ) where
  rows := fun i => match i with
    | .inl i => (G.rows i).map (Clause.map (List.map Sum.inl))
    | .inr i => U.rows (.inr i)
  parameterKinds := fun i => match i with
    | .inl i => G.parameterKinds i
    | .inr i => U.parameterKinds (.inr i)
  schemes := fun i => match i with
    | .inl i => (G.schemes i).map (mapScheme Sum.inl)
    | .inr i => U.schemes (.inr i)
  meets := fun i => match i with
    | .inl i => (G.meets i).map
      (fun q => (Sum.inl q.1,q.2.map (Clause.map (List.map Sum.inl))))
    | .inr i => U.meets (.inr i)
  meetParams := fun i => match i with
    | .inl i => (G.meetParams i).map Sum.inl
    | .inr i => U.meetParams (.inr i)
  realm := G.realm.map (mapRealm Sum.inl)
  domain := U.domain

section DomainChange
open PositiveRules
variable [DecidableEq ι]

/-- A dependency-closed portion of the graph whose quantified rows admit
exactly the same substitutions in two domains. -/
structure DomainRegion (G : NormalGraph ι) (domain : SchemeDomain ι .mixed)
    (D : ι → Prop) : Prop where
  reads : ∀ i, D i → ∀ j ∈ PositiveRules.reads G i, D j
  parts : ∀ i, D i → ∀ j ∈ meetParts G i, D j
  realm : ∀ r, G.realm = some r → ∀ j ∈ r.proto, D j
  allowed : ∀ i, D i → ∀ s, G.schemes i = some s → ∀ As,
    domain.allowed s As ↔ G.domain.allowed s As

omit [DecidableEq ι] in
private theorem region_set {D : ι → Prop}
    {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (S : List ι) (hs : ∀ i ∈ S, D i) :
    setSem (fun i => Y (η,i)) S = setSem (fun i => X (η,i)) S := by
  funext n W v
  apply propext
  exact exists_congr fun i => and_congr_right fun hi =>
    iff_of_eq (congrFun (congrFun (congrFun (h η i (hs i hi)) n) W) v)

private theorem DomainRegion.arguments {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (S : List ι) (hs : ∀ i ∈ S, D i) :
    graphArguments G η (setSem fun i => Y (η,i)) S =
      graphArguments G η (setSem fun i => X (η,i)) S := by
  funext n W vs
  apply propext
  apply exists_congr fun i => and_congr_right fun hi => ?_
  by_cases hp : G.parameterKinds i = some .arguments
  · simp only [hp, ite_true]
  · simp only [hp, ite_false]
    apply exists_congr fun c => and_congr_right fun hc => ?_
    have hq := (NormalGraph.plain_iff.mp (NormalGraph.plain_of_clauses hc)).2.1
    apply clauseArguments_congr_on (D := PositiveRules.reads G i) (fun T hT j hj => ?_)
      _ _ n (fun j hj U v => ?_) W vs
    · simp only [PositiveRules.reads, hq]
      exact List.mem_flatMap.mpr ⟨c, List.mem_append_left _ hc,
        List.mem_flatten.mpr ⟨T,hT,hj⟩⟩
    · rw [h η j (R.reads i (hs i hi) j hj)]

private theorem DomainRegion.row {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (i : ι) (hi : D i)
    (c : Clause (List ι))
    (hc : ∀ S ∈ c.operands, ∀ j ∈ S, j ∈ PositiveRules.reads G i) :
    rowSem { G with domain := domain }
      (setSem fun j => Y (ParameterAssignment.empty .mixed,j))
      (setSem fun j => Y (η,j)) (graphArguments G η (setSem fun j => Y (η,j))) c =
    rowSem G (setSem fun j => X (ParameterAssignment.empty .mixed,j))
      (setSem fun j => X (η,j)) (graphArguments G η (setSem fun j => X (η,j))) c := by
  have realm : realmInvariant { G with domain := domain }
      (setSem fun j => Y (ParameterAssignment.empty .mixed,j)) c =
      realmInvariant G (setSem fun j => X (ParameterAssignment.empty .mixed,j)) c := by
    simp only [realmInvariant]
    cases hr : G.realm with
    | none => rfl
    | some r =>
      dsimp only
      rw [region_set h (ParameterAssignment.empty .mixed) r.proto (R.realm r hr)]
  funext n W v
  apply propext
  unfold rowSem
  rw [realm]
  apply and_congr _ Iff.rfl
  apply semWithArgs_congr_on hc _ _ _ _ n
    (fun j hj => ?_) (fun S hS => ?_) W v
  · rw [h η j (R.reads i hi j hj)]
    exact fun _ _ _ _ => Iff.rfl
  · rw [R.arguments h η S (fun j hj => R.reads i hi j (hS j hj))]
    exact fun _ _ _ _ => Iff.rfl

private theorem DomainRegion.scheme {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (i : ι) (hi : D i)
    (s : SchemeRow ι) (hs : G.schemes i = some s) :
    schemeSemWithArgs (mixedParameters { G with domain := domain })
      (fun θ S => setSem (fun j => Y (θ,j)) S) η s =
    schemeSemWithArgs (mixedParameters G)
      (fun θ S => setSem (fun j => X (θ,j)) S) η s := by
  have hv : ∀ θ S, (∀ j ∈ S, j ∈ PositiveRules.reads G i) →
      setSem (fun j => Y (θ,j)) S = setSem (fun j => X (θ,j)) S :=
    fun θ S hS => region_set h θ S (fun j hj => R.reads i hi j (hS j hj))
  have hp : ∀ θ S, (∀ j ∈ S, j ∈ PositiveRules.reads G i) →
      graphArguments G θ (setSem fun j => Y (θ,j)) S =
      graphArguments G θ (setSem fun j => X (θ,j)) S :=
    fun θ S hS => R.arguments h θ S (fun j hj => R.reads i hi j (hS j hj))
  have hb : ∀ b ∈ s.bounds, ∀ j ∈ b.2, j ∈ PositiveRules.reads G i := by
    intro b hb j hj
    simp only [PositiveRules.reads, hs]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b,hb,hj⟩))
  have hbound : ∀ As n,
      Bounded (fun θ S => (mixedParameters { G with domain := domain }).bound θ
        (setSem fun j => Y (θ,j)) S) η s As n ↔
      Bounded (fun θ S => (mixedParameters G).bound θ
        (setSem fun j => X (θ,j)) S) η s As n := by
    intro As n
    unfold Bounded
    refine forall_congr' fun b => forall_congr' fun hbm =>
      forall_congr' fun _ => forall_congr' fun j => forall_congr' fun _ =>
      forall_congr' fun W => forall_congr' fun u => imp_congr_right fun _ => ?_
    cases u with
    | inl v => exact iff_of_eq (congrFun (congrFun (congrFun (hv η b.2 (hb b hbm)) j) W) v)
    | inr vs => exact iff_of_eq (congrFun (congrFun (congrFun (hp η b.2 (hb b hbm)) j) W) vs)
  have sigs : ∀ θ,
      s.signatures.map (Arrow.map (setSem fun j => Y (θ,j))) =
      s.signatures.map (Arrow.map (setSem fun j => X (θ,j))) := by
    intro θ
    apply List.map_congr_left
    intro a ha
    have hop : ∀ S ∈ a.operands, ∀ j ∈ S, j ∈ PositiveRules.reads G i := by
      intro S hS j hj
      simp only [PositiveRules.reads, hs]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨a,ha,List.mem_flatten.mpr ⟨S,hS,hj⟩⟩))
    cases a
    simp only [Arrow.map, Contract.map, Arrow.operands] at *
    congr 1
    · exact hv θ _ (hop _ (by simp))
    · apply List.map_congr_left
      intro S hS
      exact hv θ S (hop S (by simp [hS]))
    · exact hv θ _ (hop _ (by simp))
  have rests : ∀ θ,
      s.variadic.map (RestArrow.mapWith (setSem fun j => Y (θ,j))
        (graphArguments G θ (setSem fun j => Y (θ,j)))) =
      s.variadic.map (RestArrow.mapWith (setSem fun j => X (θ,j))
        (graphArguments G θ (setSem fun j => X (θ,j)))) := by
    intro θ
    apply List.map_congr_left
    intro a ha
    have hop : ∀ S ∈ a.operands, ∀ j ∈ S, j ∈ PositiveRules.reads G i := by
      intro S hS j hj
      simp only [PositiveRules.reads, hs]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨a,ha,List.mem_flatten.mpr ⟨S,hS,hj⟩⟩)
    cases a
    simp only [RestArrow.mapWith, Contract.map, RestArrow.operands] at *
    congr 1
    · exact hv θ _ (hop _ (by simp))
    · congr 1
      · apply List.map_congr_left
        intro S hS
        exact hv θ S (hop S (by simp [hS]))
      · exact hp θ _ (hop _ (by simp))
    · exact hv θ _ (hop _ (by simp))
  funext n W v
  apply propext
  unfold schemeSemWithArgs boundedSem
  refine and_congr Iff.rfl (forall_congr' fun q => forall_congr' fun hq => forall_congr' fun As => imp_congr_right fun _ => ?_)
  refine imp_congr (R.allowed i hi s hs As) (imp_congr (hbound As q) ?_)
  simp only [instanceTWithArgs, instanceSigs, instanceRestsWithArgs]
  change interT (CallEffects.callsT _) (CallEffects.restsT _) q (trunc q hq W) v ↔
    interT (CallEffects.callsT _) (CallEffects.restsT _) q (trunc q hq W) v
  dsimp only [mixedParameters]
  have sameArgs : graphArguments { G with domain := domain } = graphArguments G := rfl
  rw [sameArgs, sigs, rests]

private theorem DomainRegion.part {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (i : ι) (hi : D i) :
    partSemWithArgs { G with domain := domain } (mixedParameters { G with domain := domain }) Y η i =
      partSemWithArgs G (mixedParameters G) X η i := by
  unfold partSemWithArgs
  change (if G.params i then _ else match G.schemes i with | some _ => _ | none => _) = _
  split
  · rfl
  · cases hs : G.schemes i with
    | some s => exact R.scheme h η i hi s hs
    | none =>
      funext n W v
      apply propext
      apply exists_congr fun c => and_congr_right fun hc => ?_
      have hop : ∀ S ∈ c.operands, ∀ j ∈ S, j ∈ PositiveRules.reads G i := by
        intro S hS j hj
        simp only [PositiveRules.reads, hs]
        exact List.mem_flatMap.mpr ⟨c,List.mem_append_left _ hc,
          List.mem_flatten.mpr ⟨S,hS,hj⟩⟩
      exact iff_of_eq (congrFun (congrFun (congrFun (R.row h η i hi c hop) n) W) v)

/-- Domain replacement agrees at each approximation on the closed region. -/
theorem DomainRegion.layer {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) {X Y : MixedAssignment ι × ι → Fam}
    (h : ∀ η i, D i → Y (η,i) = X (η,i))
    (η : MixedAssignment ι) (i : ι) (hi : D i) :
    qLayerWithArgs { G with domain := domain } (mixedParameters { G with domain := domain }) Y (η,i) =
      qLayerWithArgs G (mixedParameters G) X (η,i) := by
  by_cases hp : G.params i = true
  · rw [qLayer_part (Or.inl (show ({ G with domain := domain } : NormalGraph ι).params i = true from hp)),
      qLayer_part (Or.inl hp)]
    exact R.part h η i hi
  · cases hs : G.schemes i with
    | some s =>
      rw [qLayer_part (Or.inr (Or.inl (show (({ G with domain := domain } : NormalGraph ι).schemes i).isSome = true by simp [hs]))),
        qLayer_part (Or.inr (Or.inl (by simp [hs])))]
      exact R.part h η i hi
    | none =>
      cases hm : G.meets i with
      | none =>
        rw [qLayer_part (Or.inr (Or.inr (show ({ G with domain := domain } : NormalGraph ι).meets i = none from hm))),
          qLayer_part (Or.inr (Or.inr hm))]
        exact R.part h η i hi
      | some pc =>
        have parts : ∀ j ∈ pc.1 :: G.meetParams i,
            partSemWithArgs { G with domain := domain } (mixedParameters { G with domain := domain }) Y η j =
              partSemWithArgs G (mixedParameters G) X η j := by
          intro j hj
          exact R.part h η j (R.parts i hi j (by simpa [meetParts, hm] using hj))
        have rows : ∀ c ∈ pc.2,
            rowSem { G with domain := domain }
              (setSem fun j => Y (ParameterAssignment.empty .mixed,j))
              (setSem fun j => Y (η,j)) (graphArguments G η (setSem fun j => Y (η,j))) c =
            rowSem G (setSem fun j => X (ParameterAssignment.empty .mixed,j))
              (setSem fun j => X (η,j)) (graphArguments G η (setSem fun j => X (η,j))) c := by
          intro c hc
          apply R.row h η i hi c
          intro S hS j hj
          simp only [PositiveRules.reads, hs]
          exact List.mem_flatMap.mpr ⟨c,List.mem_append_right _ (by simpa [meetClauses,hm] using hc),
            List.mem_flatten.mpr ⟨S,hS,hj⟩⟩
        funext n W v
        apply propext
        have hp' : G.params i = false := Bool.eq_false_iff.mpr hp
        have hpH : ({ G with domain := domain } : NormalGraph ι).params i = false := hp'
        simp only [qLayerWithArgs, hp', hpH, Bool.false_eq_true, ite_false, hs, hm]
        refine and_congr (and_congr ?_ (forall_congr' fun j => imp_congr_right fun hj => ?_)) ?_
        · rw [parts pc.1 (by simp)]
        · rw [parts j (by simp [hj])]
        · apply exists_congr fun c => and_congr_right fun hc => ?_
          exact iff_of_eq (congrFun (congrFun (congrFun (rows c hc) n) W) v)

theorem DomainRegion.approx {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D) (k : Nat)
    (η : MixedAssignment ι) (i : ι) (hi : D i) :
    Tower.approx (qLayerWithArgs { G with domain := domain }
      (mixedParameters { G with domain := domain })) k (η,i) =
    Tower.approx (qLayerWithArgs G (mixedParameters G)) k (η,i) := by
  induction k generalizing η i with
  | zero => rfl
  | succ k ih => exact R.layer ih η i hi

/-- Native definitions retain their exact meaning when a source graph uses
a descriptor domain, provided their dependency region retains admission. -/
theorem DomainRegion.denote {G : NormalGraph ι}
    {domain : SchemeDomain ι .mixed} {D : ι → Prop}
    (R : DomainRegion G domain D)
    (η : MixedAssignment ι) (i : ι) (hi : D i) :
    qDenoteWithArgs { G with domain := domain }
      (mixedParameters { G with domain := domain }) (η,i) =
      qDenoteWithArgs G (mixedParameters G) (η,i) := by
  funext n W v
  exact congrFun (congrFun (congrFun (R.approx (n+1) η i hi) n) W) v

#print axioms DomainRegion.denote

end DomainChange

end Verification.QualifiedTemplateEmbedding
