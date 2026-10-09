import Verification.Types.PositiveGraphs

/- Qualified generic parameters carry input, literal observation and stable
associated-result families. The operation relations and stable family are
fixed independently of recursive graph approximations. -/
namespace Verification.ResolutionDescriptors
open PositiveGraphs

structure Qualification where
  holds : Fam → Fam → Prop
  narrow : ∀ {S S' R}, FamLe S' S → holds S R → holds S' R

/-- Fresh settlement and observation retain independent operation contracts. -/
structure Capabilities where
  resolve : Qualification
  observe : Qualification

/-- Stable inputs have their own type as both observation and resolved result.
Operation-output inclusions alone do not establish this type equality. -/
def StableExact (N A O R : Fam) : Prop :=
  FamLe A N → O = A ∧ R = A

structure Descriptor (C : Capabilities) (N : Fam) where
  input : Fam
  observation : Fam
  result : Fam
  input_valid : ValueFam input
  observation_valid : ValueFam observation
  result_valid : ValueFam result
  stable : FamLe result N
  resolved : C.resolve.holds input result
  observed : C.observe.holds input observation
  forwarded : C.resolve.holds observation result
  exactStable : StableExact N input observation result

theorem Descriptor.result_eq_input {C : Capabilities} {N : Fam}
    (d : Descriptor C N) (h : FamLe d.input N) : d.result = d.input :=
  (d.exactStable h).2

abbrev ProtectedSlots (s : SchemeRow ι) := s.protectedSlots

/-- One allowed tuple retains all three operation contracts. The value
projection permits ordinary argument-list binders alongside resolution groups. -/
def SlotCoherent (C : Capabilities) (N : Fam) (As : List MixedFamily)
    (g : ResolutionSlots) : Prop :=
  ∃ T O R : MixedFamily,
    As[g.input]? = some T ∧ As[g.observation]? = some O ∧ As[g.result]? = some R ∧
    FamLe R.value.1 N ∧ C.resolve.holds T.value.1 R.value.1 ∧
    C.observe.holds T.value.1 O.value.1 ∧ C.resolve.holds O.value.1 R.value.1 ∧
    StableExact N T.value.1 O.value.1 R.value.1

/-- The fixed descriptor universe is shared by all schemes in the graph.
Ordinary schemes retain their unrestricted substitutions. -/
def descriptorDomain (C : Capabilities) (N : Fam) : SchemeDomain ι .mixed where
  allowed s As := ProtectedSlots s ∧ ∀ g ∈ s.resolution, SlotCoherent C N As g
  ordinary_allowed := by
    intro s As hs
    simp [ProtectedSlots, SchemeRow.protectedSlots, hs]
  congr := by
    intro s t hm hp As
    exact and_congr hp (by rw [hm])

/-- Allowed-instance elimination exposes a genuine descriptor, including the
literal observation family rather than a result inferred from the input alone. -/
theorem allowed_descriptor (C : Capabilities) (N : Fam) (s : SchemeRow ι)
    (As : List MixedFamily) (ha : (descriptorDomain C N).allowed s As)
    (g : ResolutionSlots) (hg : g ∈ s.resolution) :
    ∃ (d : Descriptor C N) (T O R : MixedFamily),
      As[g.input]? = some T ∧ As[g.observation]? = some O ∧ As[g.result]? = some R ∧
      T.value.1 = d.input ∧ O.value.1 = d.observation ∧ R.value.1 = d.result := by
  obtain ⟨T, O, R, hT, hO, hR, hs, hr, ho, hf, he⟩ := ha.2 g hg
  exact ⟨⟨T.value.1, O.value.1, R.value.1, T.value.2, O.value.2, R.value.2,
    hs, hr, ho, hf, he⟩, T, O, R, hT, hO, hR, rfl, rfl, rfl⟩

variable {C : Capabilities} {N : Fam}

/-- A bound tests only the input, below the current level. -/
def InputBounded (B : Fam) (d : Descriptor C N) (n : Nat) : Prop :=
  ∀ j, j < n → ∀ W v, d.input j W v → B j W v

def quantified (B : Fam) (body : Descriptor C N → Fam) : Fam :=
  fun n W f => Invocable f ∧ ∀ j (hj : j ≤ n) d, InputBounded B d j →
    body d j (trunc j hj W) f

abbrev Assignment (C : Capabilities) (N : Fam) := Nat → Descriptor C N

/-- Variable renaming carries all three projections of a descriptor. -/
def substitute (η : Assignment C N) (σ : Nat → Nat) : Assignment C N :=
  fun i => η (σ i)

/-- Actual mutable storage uses the same associated family on both reads
and writes; admissibility needs no covariance rule for writable references. -/
def storage (η : Assignment C N) (i : Nat) : Fam := refT (η i).result

/-- Negative occurrences are ordinary arrow-domain occurrences of R. -/
def consumer (η : Assignment C N) (i : Nat) : Fam :=
  callsT [(topF, [(η i).result], numT)]

#print axioms Descriptor.result_eq_input
#print axioms allowed_descriptor
end Verification.ResolutionDescriptors
