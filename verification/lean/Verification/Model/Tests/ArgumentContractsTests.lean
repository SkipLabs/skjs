import Verification.Model.Types.PositiveRules
import Verification.Model.Semantics.ModelBoundaries

/-! The argument-contract replacement removes a semantic restriction, not just
a search restriction. Test non-stable object/callback positions, a recursive
callable graph, the shared array bound, and the old extra-delay counterexample. -/
namespace Verification.Model.ArgumentContractsTests
open ArgumentContracts PositiveNormalization PositiveGraphs ModelBoundaries Tower

/-- A constructor may take an object, even when its contract reads the world. -/
example : ctorsT [([refT nulT], numT)] =
    ctorRestsT [([], Fits ⟨[refT nulT], [], none, false⟩, numT)] :=
  fixed_constructor_eq_rest _ _

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

/-- Recursion through an argument type is guarded by the callable itself.
Node 0 accepts itself as an argument; node 1 is its number result/receiver. -/
def recursive : PositiveGraphs.NormalGraph Nat := .ofRows fun
  | 0 => [.arrs [] [([1], [], [2], [1])]]
  | _ => [.num]

def recursiveArgs (X : List Nat → Fam) (_ : List Nat) : ArgFam := ArgsT [X [0]]

theorem recursiveArgs_nonexp : ArgumentNonExp recursiveArgs := by
  intro X Y n h S j hj W vs
  exact ArgsT_congr (.cons (h [0]) .nil) hj W vs

example (n W v) :
    qDenoteWithArgs recursive recursiveArgs (Assignment.empty, 0) n W v ↔
      qLayerWithArgs recursive (qDenoteWithArgs recursive recursiveArgs) recursiveArgs
        (Assignment.empty, 0) n W v :=
  qDenoteWithArgs_unfold recursive recursiveArgs recursiveArgs_nonexp _ n W v

example : Adm (qDenoteWithArgs recursive recursiveArgs (Assignment.empty, 0)) :=
  qDenoteWithArgs_adm _ _ recursiveArgs_nonexp _

/-- A bounded generic may take its binder at the same level inside a rest.
The bound is itself recursive: it accepts the generic callable as an argument.
This exercises quantified restriction and recursive negative positions together. -/
def quantified : NormalGraph Nat := {
  rows := fun i => if i = 1 then [.arrs [([3], [[0]], [3])] []] else [.top]
  parameterKinds := fun i => if i == 2 then some .value else none
  schemes := fun i => if i = 0 then some {
    binders := [2], bounds := [(2, [1])], signatures := [],
    variadic := [([3], [], [2], [2])] } else none }

def singleArgument : ArgumentInterpreter Nat := fun X S => ArgsT [X S]

theorem singleArgument_nonexp : ArgumentNonExp singleArgument := by
  intro X Y n h S j hj W vs
  exact ArgsT_congr (.cons (h S) .nil) hj W vs

example (η : Assignment Nat) :
    Adm (qDenoteWithArgs quantified singleArgument (η, 0)) :=
  qDenoteWithArgs_adm _ _ singleArgument_nonexp _

/-- The fixed-point equation retains the universal quantifier and bounds;
it is not a collection of separately checked observed instances. -/
example (η : Assignment Nat) (n W v) :
    qDenoteWithArgs quantified singleArgument (η, 0) n W v ↔
      schemeSemWithArgs
        (fun θ S => setSem (fun i => qDenoteWithArgs quantified singleArgument (θ, i)) S)
        η ⟨[2], [], [(2, [1])], [([3], [], [2], [2])]⟩ singleArgument n W v := by
  rw [qDenoteWithArgs_unfold _ _ singleArgument_nonexp]
  rfl

/-- A scheme has a value parameter and a list parameter in one substitution.
The same list contract appears in a constructor operand and trailing arguments;
the same value contract is the constructor and call result. -/
private def mixedScheme : SchemeRow Nat :=
  { binders := [0,1], signatures := [], bounds := [(0, [2]), (1, [3])] }

private def closedTop : ValueFamily :=
  ⟨topT, ⟨⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩, fun _ _ _ h => h⟩⟩

private def closedArguments : ArgumentFamily :=
  ⟨All topT, ⟨all_adm closedTop.2.1, fun _ _ _ h => h⟩⟩

private def mixedBound (_ : MixedAssignment Nat) (S : List Nat) : MixedFamily :=
  if S = [2] then .ofValue closedTop else .ofArguments closedArguments

private noncomputable def mixedBody (η : MixedAssignment Nat)
    (As : List MixedFamily) : Fam :=
  let θ := assign η mixedScheme.binders As
  let R : Fam := fun n W v => θ.1 0 n W (.inl v)
  let P : ArgFam := fun n W vs => θ.1 1 n W (.inr vs)
  restsT [(topT, [ArgumentContracts.constructor P R], P, R)]

private noncomputable def quantifiedMixed (η : MixedAssignment Nat) : Fam :=
  boundedSem (k := .mixed) (fun θ S => (mixedBound θ S).1)
    η mixedScheme (mixedBody η)

/-- Mixed quantification uses the production bound-restriction proof. -/
example (η : MixedAssignment Nat) : Adm (quantifiedMixed η) := by
  apply boundedSem_adm
  · intro S
    exact (mixedBound η S).2.1
  · intro As
    exact restsT_adm _
  · intro As Bs m h W v
    apply restsT_congr [()] (fun _ => _) (fun _ => _) _ W v
    intro _ _
    refine ⟨fun _ _ _ _ => Iff.rfl, .cons ?_ .nil,
      fun j hj U vs => h 1 j hj U (.inr vs),
      fun j hj U u => h 0 j hj U (.inl u)⟩
    intro j hj U u
    exact constructor_congr (fun i hi V vs => h 1 i (by omega) V (.inr vs))
      (fun i hi V v => h 0 i (by omega) V (.inl v)) U u

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
  simpa [mixedBody, mixedScheme, F, assign_cons_head, assign_cons_ne, MixedFamily.ofValue, MixedFamily.ofArguments]
    using hi

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
