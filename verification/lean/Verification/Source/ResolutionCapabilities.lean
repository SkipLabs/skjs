import Verification.Types.ResolutionDescriptors

/-! Finite native-resolution classifications over a fixed, independently
interpreted native Promise constructor. These relations specify the instances
of external operation contracts; their constructors do not prove JavaScript
execution. Native callable membership remains a reviewed environment premise. -/
namespace Verification.ResolutionCapabilities
open PositiveGraphs PositiveNormalization ResolutionDescriptors

/-- Fresh resolution follows the literal payload of a native promise until
it reaches a stable family. Union arms share the declared target family. -/
inductive Resolves (P : Fam → Fam) (N : Fam) : Fam → Fam → Prop where
  | stable {A} : ValueFam A → FamLe A N → Resolves P N A A
  | native {A R} : Resolves P N A R → Resolves P N (P A) R
  | union {A B R S} : Resolves P N A R → Resolves P N B S →
      Resolves P N (unionT A B) (unionT R S)

/-- Observation reads a native promise's literal fulfillment family once. -/
inductive Observes (P : Fam → Fam) (N : Fam) : Fam → Fam → Prop where
  | stable {A} : ValueFam A → FamLe A N → Observes P N A A
  | native {A} : ValueFam A → FamLe A sourceT → Observes P N (P A) A
  | union {A B O Q} : Observes P N A O → Observes P N B Q →
      Observes P N (unionT A B) (unionT O Q)

/-- The native constructor preserves value families and keeps every
application outside the stable family. -/
structure NativeSeparation (P : Fam → Fam) (N : Fam) : Prop where
  valid : ∀ A, ValueFam A → ValueFam (P A)
  separate : ∀ A, ValueFam A → ¬ FamLe (P A) N
  native_source : ∀ A, ValueFam A → FamLe (P A) sourceT
  stable_source : FamLe N sourceT

private theorem union_valid {A B : Fam} (ha : ValueFam A) (hb : ValueFam B) :
    ValueFam (unionT A B) :=
  ⟨unionT_adm A B ha.1 hb.1, fun n W v h => h.elim (ha.2 n W v) (hb.2 n W v)⟩

section
variable {P : Fam → Fam} {N : Fam}

theorem Resolves.input_valid (h : NativeSeparation P N) {A R} (r : Resolves P N A R) :
    ValueFam A := by
  induction r with
  | stable hv _ => exact hv
  | native _ ih => exact h.valid _ ih
  | union _ _ ih₁ ih₂ => exact union_valid ih₁ ih₂

/-- Resolution is exact on stable inputs: a union of stable arms resolves
arm by arm to itself, and a native application is never stable. -/
theorem Resolves.exact (h : NativeSeparation P N) {A R} (r : Resolves P N A R) :
    FamLe A N → R = A := by
  induction r with
  | stable => intro _; rfl
  | native r _ => intro hn; exact (h.separate _ (r.input_valid h) hn).elim
  | union _ _ ih₁ ih₂ =>
      intro hn
      rw [ih₁ (fun n W v hv => hn n W v (Or.inl hv)),
        ih₂ (fun n W v hv => hn n W v (Or.inr hv))]

/-- Observation is exact on stable inputs, by the same case analysis. -/
theorem Observes.exact (h : NativeSeparation P N) {A O} (o : Observes P N A O) :
    FamLe A N → O = A := by
  induction o with
  | stable => intro _; rfl
  | native hv _ => intro hn; exact (h.separate _ hv hn).elim
  | union _ _ ih₁ ih₂ =>
      intro hn
      rw [ih₁ (fun n W v hv => hn n W v (Or.inl hv)),
        ih₂ (fun n W v hv => hn n W v (Or.inr hv))]

/-- Resolution and observation carry only JavaScript values at every slot. -/
theorem Resolves.source (h : NativeSeparation P N) {A R} (r : Resolves P N A R) :
    FamLe A sourceT ∧ FamLe R sourceT := by
  induction r with
  | stable _ hn => exact ⟨fun n W v hv => h.stable_source n W v (hn n W v hv),
      fun n W v hv => h.stable_source n W v (hn n W v hv)⟩
  | native r ih => exact ⟨h.native_source _ (r.input_valid h), ih.2⟩
  | union _ _ ih₁ ih₂ => exact ⟨fun n W v hv => hv.elim (ih₁.1 n W v) (ih₂.1 n W v),
      fun n W v hv => hv.elim (ih₁.2 n W v) (ih₂.2 n W v)⟩

theorem Observes.source (h : NativeSeparation P N) {A O} (o : Observes P N A O) :
    FamLe A sourceT ∧ FamLe O sourceT := by
  induction o with
  | stable _ hn => exact ⟨fun n W v hv => h.stable_source n W v (hn n W v hv),
      fun n W v hv => h.stable_source n W v (hn n W v hv)⟩
  | native hv hs => exact ⟨h.native_source _ hv, hs⟩
  | union _ _ ih₁ ih₂ => exact ⟨fun n W v hv => hv.elim (ih₁.1 n W v) (ih₂.1 n W v),
      fun n W v hv => hv.elim (ih₁.2 n W v) (ih₂.2 n W v)⟩

end

def capabilities {P : Fam → Fam} {N : Fam} (h : NativeSeparation P N) : Capabilities N where
  resolve := Resolves P N
  observe := Observes P N
  resolve_exact hn r := r.exact h hn
  observe_exact hn o := o.exact h hn
  resolve_source r := r.source h
  observe_source o := o.source h

section
variable {P : Fam → Fam} {N : Fam} (h : NativeSeparation P N)

/-- A stable leaf is its own observation. -/
def stableObservation (A : Fam) (ha : ValueFam A) (hn : FamLe A N) :
    Observation (capabilities h) where
  input := A
  observation := A
  input_valid := ha
  observation_valid := ha
  observed := .stable ha hn

/-- A native promise of any payload is observed at that payload. -/
def nativeObservation (A : Fam) (ha : ValueFam A) (hs : FamLe A sourceT) : Observation (capabilities h) where
  input := P A
  observation := A
  input_valid := h.valid A ha
  observation_valid := ha
  observed := .native ha hs

/-- Every union arm contributes its input and observation. -/
def unionObservation (d e : Observation (capabilities h)) : Observation (capabilities h) where
  input := unionT d.input e.input
  observation := unionT d.observation e.observation
  input_valid := union_valid d.input_valid e.input_valid
  observation_valid := union_valid d.observation_valid e.observation_valid
  observed := .union d.observed e.observed

/-- A stable leaf uses one family for all three slots. -/
def stable (A : Fam) (ha : ValueFam A) (hn : FamLe A N) :
    Descriptor (capabilities h) where
  toObservation := stableObservation h A ha hn
  result := A
  result_valid := ha
  stable := hn
  resolved := .stable ha hn
  forwarded := .stable ha hn

/-- Native lifting preserves the child's associated result and observes its
input literally, including when that input is itself a native promise. -/
def native (d : Descriptor (capabilities h)) : Descriptor (capabilities h) where
  toObservation := nativeObservation h d.input d.input_valid (d.observed.source h).1
  result := d.result
  result_valid := d.result_valid
  stable := d.stable
  resolved := .native d.resolved
  forwarded := d.resolved

/-- Every union arm contributes its input, observation and result. -/
def union (d e : Descriptor (capabilities h)) : Descriptor (capabilities h) where
  toObservation := unionObservation h d.toObservation e.toObservation
  result := unionT d.result e.result
  result_valid := union_valid d.result_valid e.result_valid
  stable := fun n W v h => h.elim (d.stable n W v) (e.stable n W v)
  resolved := .union d.resolved e.resolved
  forwarded := .union d.forwarded e.forwarded

/-- **Resolvable inputs are described.** Every input with a fresh resolution
has a descriptor with that result: the classification rules construct its
observation alongside, so the observation exists also where no source type
names it, as for the observation of a qualified binder's observation. -/
theorem Resolves.describe {A R} (r : Resolves P N A R) :
    ∃ d : Descriptor (capabilities h), d.input = A ∧ d.result = R := by
  induction r with
  | stable hv hn => exact ⟨ResolutionCapabilities.stable h _ hv hn, rfl, rfl⟩
  | native _ ih =>
      obtain ⟨d, hd, hr⟩ := ih
      exact ⟨ResolutionCapabilities.native h d, by rw [← hd]; rfl, hr⟩
  | union _ _ ih₁ ih₂ =>
      obtain ⟨d, hd, hr⟩ := ih₁
      obtain ⟨e, he, hs⟩ := ih₂
      exact ⟨ResolutionCapabilities.union h d e, by rw [← hd, ← he]; rfl, by rw [← hr, ← hs]; rfl⟩

end

/-- The descriptor domain depends only on the constructor and stable family. -/
theorem domain_congr {ι : Type} {P P' : Fam → Fam} {N N' : Fam}
    (h : NativeSeparation P N) (h' : NativeSeparation P' N') (hp : P' = P) (hn : N' = N) :
    descriptorDomain (ι := ι) (capabilities h') = descriptorDomain (capabilities h) := by
  subst hp hn
  rfl

#print axioms Resolves.source
#print axioms Observes.source
#print axioms Resolves.exact
#print axioms Observes.exact
#print axioms stableObservation
#print axioms nativeObservation
#print axioms unionObservation
#print axioms stable
#print axioms native
#print axioms union
#print axioms Resolves.describe

/-- The modeled operation is safe at every admissible world and satisfying
heap. Unlike an outcome-only relation, this also constrains executions that
throw or do not return. -/
def OperationContract (Ξ : Fam) (op : Val → Tm) (A B : Fam) : Prop :=
  ∀ n (W : WorldT n) heap v, WorldAdm W → HeapOk n W heap →
    A n W v → Safe Ξ B n W heap (op v)

namespace OperationContract

theorem narrow {op A A' B} (h : OperationContract Ξ op A B)
    (ha : FamLe A' A) : OperationContract Ξ op A' B :=
  fun n W heap v hw hh hv => h n W heap v hw hh (ha n W v hv)

theorem widen {op A B B'} (h : OperationContract Ξ op A B)
    (hb : FamLe B B') : OperationContract Ξ op A B' := by
  intro n W heap v hw hh hv
  exact Safe_mono n (fun m _ U u hu => hb m U u hu) W heap (op v)
    (h n W heap v hw hh hv)

theorem union {op A B R S} (ha : OperationContract Ξ op A R)
    (hb : OperationContract Ξ op B S) :
    OperationContract Ξ op (unionT A B) (unionT R S) := by
  intro n W heap v hw hh hv
  rcases hv with hv | hv
  · exact ha.widen (fun _ _ _ h => Or.inl h) n W heap v hw hh hv
  · exact hb.widen (fun _ _ _ h => Or.inr h) n W heap v hw hh hv

theorem union_input {op A B R} :
    OperationContract Ξ op (unionT A B) R ↔
      OperationContract Ξ op A R ∧ OperationContract Ξ op B R := by
  constructor
  · intro h
    exact ⟨h.narrow (fun _ _ _ h => Or.inl h), h.narrow (fun _ _ _ h => Or.inr h)⟩
  · rintro ⟨ha, hb⟩ n W heap v hw hh (hv | hv)
    · exact ha n W heap v hw hh hv
    · exact hb n W heap v hw hh hv
end OperationContract

/-- A reviewed host operation that reads an awaitable input's observation:
on a stable input it produces `F` of the input, on a native promise `F` of
its payload. `await` is such an operation with `F` the identity, and
`Promise.resolve`, which returns a native promise itself and wraps a stable
value in a fresh one, with `F` the native constructor. -/
structure ObservationContract (Ξ : Fam) (P : Fam → Fam) (N : Fam) (op : Val → Tm) (F : Fam → Fam) : Prop where
  mono : ∀ {A B}, FamLe A B → FamLe (F A) (F B)
  stable : ∀ {A}, ValueFam A → FamLe A N → OperationContract Ξ op A (F A)
  native : ∀ A, FamLe A sourceT → OperationContract Ξ op (P A) (F A)

/-- Reviewed host contracts expressed in the verifier's own world and safety
model. `observe` returns a native promise's delivered value, `identity` is
`Promise.resolve`, and `fresh` returns a fresh native promise resolved with
its input. These are explicit premises, not consequences of structural
Promise methods. -/
structure NativeOperationContracts (Ξ : Fam) (P : Fam → Fam) (N : Fam)
    (observe identity fresh : Val → Tm) : Prop where
  promise_mono : ∀ {A B}, FamLe A B → FamLe (P A) (P B)
  observes : ObservationContract Ξ P N observe id
  identifies : ObservationContract Ξ P N identity P
  fresh_stable : ∀ {A}, ValueFam A → FamLe A N → OperationContract Ξ fresh A (P A)
  fresh_native : ∀ {A R}, OperationContract Ξ fresh A (P R) →
    OperationContract Ξ fresh (P A) (P R)

/-- Every finite observation derivation supplies the actual safety contract of
an observing operation: `F` of the observation. -/
theorem Observes.safe {P N op F} (host : ObservationContract Ξ P N op F)
    {A O} (h : Observes P N A O) : OperationContract Ξ op A (F O) := by
  induction h with
  | stable hv hn => exact host.stable hv hn
  | native _ hs => exact host.native _ hs
  | union _ _ ih₁ ih₂ =>
      apply (OperationContract.union_input).mpr
      exact ⟨ih₁.widen (host.mono (fun _ _ _ h => Or.inl h)),
        ih₂.widen (host.mono (fun _ _ _ h => Or.inr h))⟩

/-- `await` of an awaitable input yields its observation. -/
theorem Observes.await_safe {P N observe identity fresh}
    (host : NativeOperationContracts Ξ P N observe identity fresh)
    {A O} (h : Observes P N A O) : OperationContract Ξ observe A O :=
  h.safe host.observes

/-- `Promise.resolve` of an awaitable input is a native promise of its
observation. -/
theorem Observes.resolve_safe {P N observe identity fresh}
    (host : NativeOperationContracts Ξ P N observe identity fresh)
    {A O} (h : Observes P N A O) : OperationContract Ξ identity A (P O) :=
  h.safe host.identifies

/-- Resolution derivations produce the declared native result; safety includes
world evolution and every intermediate computation admitted by Safe. -/
theorem Resolves.safe {P N observe identity fresh}
    (host : NativeOperationContracts Ξ P N observe identity fresh)
    {A R} (h : Resolves P N A R) : OperationContract Ξ fresh A (P R) := by
  induction h with
  | stable hv hn => exact host.fresh_stable hv hn
  | native _ ih => exact host.fresh_native ih
  | union _ _ ih₁ ih₂ =>
      apply (OperationContract.union_input).mpr
      exact ⟨ih₁.widen (host.promise_mono (fun _ _ _ h => Or.inl h)),
        ih₂.widen (host.promise_mono (fun _ _ _ h => Or.inr h))⟩

#print axioms OperationContract.union_input
#print axioms Observes.safe
#print axioms Observes.await_safe
#print axioms Observes.resolve_safe
#print axioms Resolves.safe

end Verification.ResolutionCapabilities
