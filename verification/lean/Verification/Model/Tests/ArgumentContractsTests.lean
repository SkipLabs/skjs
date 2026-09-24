import Verification.Model.Types.PositiveRules
import Verification.Model.Semantics.ModelBoundaries

/-! The argument-contract replacement removes a semantic restriction, not just
a search restriction. Test non-stable object/callback positions, a recursive
callable graph, the shared array bound, and the old extra-delay counterexample. -/
namespace Verification.Model.ArgumentContractsTests
open ArgumentContracts PositiveNormalization PositiveGraphs ModelBoundaries Tower

/-- A real graph tuple row taking an object supports fixed-constructor
conversion, without the old stability restriction on the element type. -/
example (η : MixedAssignment Nat) :
    ctorsT [([refT nulT], numT)] = ctorRestsT [([], graphArguments
      (.ofRows fun _ => [.pack ⟨[[1]], [], none, false⟩ []]) η
      (fun _ => refT nulT) [0], numT)] := by
  rw [graphArguments_pack _ _ _ _ _ _ rfl]
  have shape : (fun n W vs => ∀ t ∈ [Tuple.mk [[1]] [] none false],
      Fits (tupleFams (fun _ => refT nulT) t) n W vs) =
      Fits ⟨[refT nulT], [], none, false⟩ := by
    funext n W vs
    apply propext
    simp [tupleFams]
  rw [shape]
  exact fixed_constructor_eq_rest _ _

/-- An actual certificate substitutes an object type for a tuple element's
value parameter. Its value-row proof feeds the argument-row proof at the same
level, so object information is retained through the checked image. -/
private def imageGraph : NormalGraph Nat := {
  rows := fun i => match i with
    | 0 => [.pack ⟨[[1]], [], none, false⟩ []]
    | 2 => [.refs [(valueField, [4])] [] []]
    | 3 => [.pack ⟨[[2]], [], none, false⟩ []]
    | _ => [.nul]
  parameterKinds := fun i => if i = 1 then some .value else none }

private def imageContext : PositiveRules.Ctx Nat := [(1, [2])]
private def imageTable : PositiveRules.InstTable Nat :=
  [(0, imageContext, [3]), (1, imageContext, [2])]
private def imageFree : PositiveRules.FreeMap Nat := [(0, [1]), (1, [1])]

private theorem imageChecked :
    PositiveRules.TableOk imageGraph imageTable [0,1,2,3,4] imageFree = true := by decide

/-- An absent operand image is a refusal, never an implicit empty type. -/
example : PositiveRules.TableOk imageGraph [(0, imageContext, [3])]
    [0,1,2,3,4] imageFree = false := by decide

private noncomputable def objectAssignment : Assignment Nat :=
  assign Assignment.empty [1]
    [⟨PositiveRules.meaning imageGraph [2], PositiveRules.meaning_valueFam imageGraph [2]⟩]

example (μ ν : MixedAssignment Nat) (n : Nat) (W : WorldT n) (vs : List Val) :
    graphArguments imageGraph μ (qMeaning imageGraph objectAssignment) [0] n W vs ↔
      graphArguments imageGraph ν (qMeaning imageGraph Assignment.empty) [3] n W vs := by
  apply PositiveRules.graphArguments_image imageGraph imageTable imageContext μ ν
    _ _ 0 3 (by decide) (by decide) (by decide) n W vs
  · intro c hc S hS
    have hc' : c = .pack ⟨[[1]], [], none, false⟩ [] := by
      simpa [imageGraph, NormalGraph.clauses, NormalGraph.plain, NormalGraph.params] using hc
    subst c
    have hS' : S = [1] := by simpa [Clause.operands, Tuple.operands] using hS
    subst S
    refine ⟨[2], by decide, fun v => ?_⟩
    have hrel : PositiveRules.RelK imageGraph imageContext [1] objectAssignment Assignment.empty := by
      intro p hp
      have hp' : p = 1 := by simpa using hp
      subst p
      simp [imageContext, objectAssignment, assign_cons_head, PositiveRules.meaning,
        qMeaning, imageGraph]
      rfl
    have hi := PositiveRules.table_row imageChecked n objectAssignment Assignment.empty
      (1, imageContext, [2]) (by decide) hrel W v
    simpa [qMeaning, setSem] using hi
  · intro v; simp [qMeaning, setSem]

/-- A callback argument may itself have an arbitrary higher-order contract. -/
example (A B R : Fam) : ctorsT [([arrowT A B], R)] =
    ctorRestsT [([], Fits ⟨[arrowT A B], [], none, false⟩, R)] :=
  fixed_constructor_eq_rest _ _

/-- The array constraint and the actuals use the same element evidence.
This holds for object-valued dependencies just as for number-valued ones. -/
example (T : TupleF) (Bound : Fam)
    (hb : ∀ i A, positionFam T i = some A → FamLe A Bound) :
    (∀ n W vs, Fits T n W vs → ∀ v ∈ vs, Bound n W v) ∧
    FamLe (listT T) (listT ⟨[], [], some Bound, true⟩) :=
  ⟨fun _ _ _ h => fits_bound hb h, array_bound hb⟩

/-- Recursion through a real graph pack row is guarded by the callable.
Node 0 takes a list whose single element is itself; node 1 is the result. -/
def recursive : PositiveGraphs.NormalGraph Nat := .ofRows fun
  | 0 => [.arrs [] [([1], [], [2], [1])]]
  | 2 => [.pack ⟨[[0]], [], none, false⟩ []]
  | _ => [.num]

example (η : MixedAssignment Nat) (n W v) :
    qDenoteWithArgs recursive (mixedParameters recursive) (η, 0) n W v ↔
      qLayerWithArgs recursive (mixedParameters recursive)
        (qDenoteWithArgs recursive (mixedParameters recursive))
        (η, 0) n W v :=
  qDenoteWithArgs_unfold _ _ _ n W v

example (η : MixedAssignment Nat) : Adm
    (qDenoteWithArgs recursive (mixedParameters recursive) (η, 0)) :=
  qDenoteWithArgs_adm _ _ _

/-- A pack parameter's bound is a tuple containing a recursive callable.
This exercises quantified restriction and recursive negative positions together,
using real rows for both the pack parameter and its bound. -/
def quantified : NormalGraph Nat := {
  rows := fun i => match i with
    | 1 => [.pack ⟨[[4]], [], none, false⟩ []]
    | 4 => [.arrs [([3], [[0]], [3])] []]
    | _ => [.top]
  parameterKinds := fun i => if i == 2 then some .arguments else none
  schemes := fun i => if i = 0 then some {
    binders := [2], bounds := [(2, [1])], signatures := [],
    variadic := [([3], [], [2], [3])] } else none }

example (η : MixedAssignment Nat) :
    Adm (qDenoteWithArgs quantified (mixedParameters quantified) (η, 0)) :=
  qDenoteWithArgs_adm _ _ _

/-- The fixed-point equation retains universal quantification over mixed
assignments and both components of the bound; no observed calls replace it. -/
example (η : MixedAssignment Nat) (n W v) :
    qDenoteWithArgs quantified (mixedParameters quantified) (η, 0) n W v ↔
      schemeSemWithArgs (mixedParameters quantified)
        (fun θ S => setSem (fun i => qDenoteWithArgs quantified
          (mixedParameters quantified) (θ, i)) S)
        η ⟨[2], [], [(2, [1])], [([3], [], [2], [3])]⟩
        n W v := by
  rw [qDenoteWithArgs_unfold _ _]
  rfl

/-- A scheme has a value parameter and a list parameter in one substitution.
The same list contract appears in a constructor operand and trailing arguments;
the same value contract is the constructor and call result. -/
private def mixedScheme : SchemeRow Nat :=
  { binders := [0,1], signatures := [], bounds := [(0, [2]), (1, [3])],
    variadic := [([3], [[2]], [1], [0])] }

private def closedTop : ValueFamily :=
  ⟨topT, ⟨⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩, fun _ _ _ h => h⟩⟩

private def closedArguments : ArgumentFamily :=
  ⟨All topT, ⟨all_adm closedTop.2.1, fun _ _ _ h => h⟩⟩

private def mixedBound (_ : MixedAssignment Nat) (S : List Nat) : MixedFamily :=
  if S = [2] then .ofValue closedTop else .ofArguments closedArguments

private def mixedGraph : NormalGraph Nat := {
  rows := fun _ => [],
  parameterKinds := fun i => if i = 0 then some .value else
    if i = 1 then some .arguments else none }

private def mixedValue (η : MixedAssignment Nat) (S : List Nat) : Fam :=
  let R : Fam := fun n W v => η.1 0 n W (.inl v)
  let P : ArgFam := fun n W vs => η.1 1 n W (.inr vs)
  if S = [2] then ArgumentContracts.constructor P R else
    if S = [0] then R else topT

private theorem mixedValue_nonexp (η θ : MixedAssignment Nat) (n : Nat)
    (h : ∀ p, Model.Agree (η.1 p) (θ.1 p) n) (S : List Nat) :
    Model.Agree (mixedValue η S) (mixedValue θ S) n := by
  intro j hj W v
  unfold mixedValue
  split
  · exact constructor_congr (fun i hi U vs => h 1 i (by omega) U (.inr vs))
      (fun i hi U u => h 0 i (by omega) U (.inl u)) W v
  · split
    · exact h 0 j hj W (.inl v)
    · exact Iff.rfl

private noncomputable def mixedBody (η : MixedAssignment Nat)
    (As : List MixedFamily) : Fam :=
  instanceTWithArgs mixedValue η mixedScheme As (graphArguments mixedGraph)

private noncomputable def quantifiedMixed (η : MixedAssignment Nat) : Fam :=
  boundedSem (k := .mixed) (fun θ S => (mixedBound θ S).1)
    η mixedScheme (mixedBody η)

/-- Mixed quantification uses the production bound-restriction proof. -/
example (η : MixedAssignment Nat) : Adm (quantifiedMixed η) := by
  apply boundedSem_adm
  · intro S
    exact (mixedBound η S).2.1
  · intro As
    exact instanceTWithArgs_adm _ _ _ _ _
  · intro As Bs m h W v
    exact instanceT_congrWithArgs _ (graphArguments_nonexp mixedGraph) h
      (mixedValue_nonexp _ _ m h) W v

/-- One checked substitution supplies an arbitrary value type and an arbitrary
argument-list contract. No monomorphization or synthetic runtime pack occurs. -/
example (η : MixedAssignment Nat) (A : ValueFamily) (P : ArgumentFamily)
    (n W f) (hf : quantifiedMixed η n W f) :
    restsT [(topT, [ArgumentContracts.constructor P.1 A.1], P.1, A.1)] n W f := by
  let F : List Nat → MixedFamily := fun S =>
    if S = [4] then .ofValue A else .ofArguments P
  have hb : ∀ b ∈ mixedScheme.bounds, ∀ U,
      (mixedScheme.binders.zip [[4],[5]]).lookup b.1 = some U →
      FamLe (F U).1 (mixedBound η b.2).1 := by
    intro b hb U hu
    simp only [mixedScheme, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · have : U = [4] := by simpa [mixedScheme, List.lookup_cons] using hu.symm
      subst U
      intro n W x hx
      cases x with
      | inl v => exact A.2.2 n W v hx
      | inr vs => exact hx.elim
    · have : U = [5] := by simpa [mixedScheme, List.lookup_cons] using hu.symm
      subst U
      intro n W x hx
      cases x with
      | inl v => exact hx.elim
      | inr vs => exact P.2.2 n W vs hx
  have hi := PositiveRules.bounded_substitution_elim η F
    (fun θ S => (mixedBound θ S).1) mixedScheme [[4],[5]] (mixedBody η) rfl hb n W f hf
  have rest := hi.2
  simp only [instanceRestsWithArgs, mixedScheme, List.map_cons, List.map_nil] at rest
  rw [graphArguments_parameter _ _ _ _ (by simp [mixedGraph])] at rest
  simpa [mixedValue, F, assign_cons_head, assign_cons_ne,
    MixedFamily.ofValue, MixedFamily.ofArguments] using rest

/-- A real callback value that returns the wrong result. -/
def badCallback : Tm := .objAt [] (.closure 1 .tru)

theorem callback_shallow {k : Nat} (hk : k < 2) (W : WorldT k) :
    arrowT nulT nulT k W badCallback := by
  refine ⟨⟨1, .tru, [], rfl, by trivial⟩, ?_⟩
  intro j hj U hx hu heap hh a ha
  have : j = 0 := by omega
  subst j
  trivial

theorem callback_not_deep : ¬ arrowT nulT nulT 2 (ofList []) badCallback := by
  intro h
  have hh : HeapOk 1 (ofList []) [] := by
    refine ⟨by simp, ?_⟩
    intro l c hc
    simp [lookup] at hc
  have hx : WExt (trunc 1 (by omega) (ofList ([] : List (Ctr 2)))) (ofList []) := by
    rw [trunc_empty]
    exact WExt_refl _
  have hs := h.2 1 (by omega) (ofList []) hx (emptyWorld_adm 1) [] hh .nul rfl
  change Safe nulT 1 (ofList []) [] .tru at hs
  have := safe_value_mem (show isVal .tru = true from rfl) hs
  simp [nulT] at this

/-- The old guarded pack admits the callback at level 2 because it checks the
position only below 2; the same-level contract correctly distinguishes it. -/
theorem old_pack_loses_information :
    PackFits ⟨[arrowT nulT nulT], [], none, false⟩ 2 (ofList []) [badCallback] ∧
    ¬ Fits ⟨[arrowT nulT nulT], [], none, false⟩ 2 (ofList []) [badCallback] := by
  constructor
  · refine ⟨by simp, by simp, ?_⟩
    intro i v A hv hA j hj U hx
    have hi : i = 0 := by
      obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hv
      simp only [List.length_singleton] at hi
      omega
    subst i
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
    subst v
    simp only [positionFam, List.getElem?_cons_zero, Option.some.injEq] at hA
    subst A
    exact callback_shallow hj U
  · intro h
    have hargs := (fits_exact [arrowT nulT nulT] 2 (ofList []) [badCallback]).mp h
    exact callback_not_deep hargs.1

/-- A constructor returning its sole argument. This isolates the contract
conversion from allocation and from any implementation-specific behavior. -/
def identityConstructor : Tm := .objAt [] (.closure 1 (.var 1) .construct)

theorem identity_constructor (A : Fam)
    (hA : ∀ n W v, A n W v → Scoped 0 v) (n W) :
    ctorsT [([A], A)] n W identityConstructor := by
  refine ⟨⟨[], 1, .var 1, rfl, by change 1 < 2; omega⟩, ?_⟩
  intro p hp j hj U hx hu heap hh args hv ha
  cases List.mem_singleton.mp hp
  obtain ⟨a, rfl, harg⟩ := (ArgsT_singleton A j U args).mp ha
  refine ⟨a, ⟨[], 1, .var 1, rfl, ?_⟩, ?_⟩
  · change a = subst 0 .undef a
    exact (subst_above (hA j U a harg) (Nat.le_refl 0) .undef).symm
  · exact value_safe A j U heap a (hv a (by simp)) harg

/-- Removing stability from the old rule would be false in the old semantics,
not merely difficult to prove. The new same-level interpretation is necessary. -/
theorem old_constructor_conversion_false :
    ¬ FamLe (ctorsT [([arrowT nulT nulT], arrowT nulT nulT)])
      (ctorRestsT [([], packArgs (packT [⟨[arrowT nulT nulT], [], none, false⟩]), arrowT nulT nulT)]) := by
  intro rule
  have h := rule 3 (ofList []) identityConstructor (identity_constructor _ (fun _ _ _ h => h.1.scoped) _ _)
  have hh : HeapOk 2 (ofList []) [] := by
    refine ⟨by simp, ?_⟩
    intro l c hc
    simp [lookup] at hc
  have hx : WExt (trunc 2 (by omega) (ofList ([] : List (Ctr 3)))) (ofList []) := by
    rw [trunc_empty]
    exact WExt_refl _
  have hpack : packT [⟨[arrowT nulT nulT], [], none, false⟩] 2 (ofList []) (.args [badCallback]) := by
    refine ⟨[badCallback], rfl, by trivial, ?_⟩
    intro T hT
    cases List.mem_singleton.mp hT
    exact old_pack_loses_information.1
  have ha : CtorRest [] (packArgs (packT [⟨[arrowT nulT nulT], [], none, false⟩])) 2
      (ofList []) [badCallback] := by
    exact ⟨by simp, trivial, hpack⟩
  obtain ⟨result, hi, hs⟩ := h.2 _ (List.mem_singleton_self _) 2 (by omega) (ofList []) hx
    (emptyWorld_adm 2) [] hh [badCallback] (by intro v hv; cases List.mem_singleton.mp hv; rfl) ha
  obtain ⟨fs, arity, body, he, hr⟩ := hi
  cases he
  subst result
  change Safe (arrowT nulT nulT) 2 (ofList []) [] badCallback at hs
  exact callback_not_deep (safe_value_mem rfl hs)

/-- Wrong argument types remain rejected. -/
example (n W) : ¬ Fits ⟨[numT], [], none, false⟩ n W [.nul] := by
  rw [fits_exact]
  simp [ArgsT, numT]

#print axioms old_pack_loses_information
#print axioms old_constructor_conversion_false
end Verification.Model.ArgumentContractsTests
