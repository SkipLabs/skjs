import Verification.Types.ResolutionDescriptors

/-! Finite native-resolution classifications over a fixed, independently
interpreted native Promise constructor. These relations specify the instances
of external operation contracts; their constructors do not prove JavaScript
execution. Native callable membership remains a reviewed environment premise. -/
namespace Verification.ResolutionCapabilities
open PositiveGraphs ResolutionDescriptors

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
  | native {A} : ValueFam A → Observes P N (P A) A
  | union {A B O Q} : Observes P N A O → Observes P N B Q →
      Observes P N (unionT A B) (unionT O Q)

/-- The native constructor preserves value families and keeps every
application outside the stable family. -/
structure NativeSeparation (P : Fam → Fam) (N : Fam) : Prop where
  valid : ∀ A, ValueFam A → ValueFam (P A)
  separate : ∀ A, ValueFam A → ¬ FamLe (P A) N

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
  | native hv => intro hn; exact (h.separate _ hv hn).elim
  | union _ _ ih₁ ih₂ =>
      intro hn
      rw [ih₁ (fun n W v hv => hn n W v (Or.inl hv)),
        ih₂ (fun n W v hv => hn n W v (Or.inr hv))]

end

def capabilities {P : Fam → Fam} {N : Fam} (h : NativeSeparation P N) : Capabilities N where
  resolve := Resolves P N
  observe := Observes P N
  resolve_exact hn r := r.exact h hn
  observe_exact hn o := o.exact h hn

section
variable {P : Fam → Fam} {N : Fam} (h : NativeSeparation P N)

/-- A stable leaf uses one family for all three slots. -/
def stable (A : Fam) (ha : ValueFam A) (hn : FamLe A N) :
    Descriptor (capabilities h) where
  input := A
  observation := A
  result := A
  input_valid := ha
  observation_valid := ha
  result_valid := ha
  stable := hn
  resolved := .stable ha hn
  observed := .stable ha hn
  forwarded := .stable ha hn

/-- Native lifting preserves the child's associated result and observes its
input literally, including when that input is itself a native promise. -/
def native (d : Descriptor (capabilities h)) : Descriptor (capabilities h) where
  input := P d.input
  observation := d.input
  result := d.result
  input_valid := h.valid d.input d.input_valid
  observation_valid := d.input_valid
  result_valid := d.result_valid
  stable := d.stable
  resolved := .native d.resolved
  observed := .native d.input_valid
  forwarded := d.resolved

/-- Every union arm contributes its input, observation and result. -/
def union (d e : Descriptor (capabilities h)) : Descriptor (capabilities h) where
  input := unionT d.input e.input
  observation := unionT d.observation e.observation
  result := unionT d.result e.result
  input_valid := union_valid d.input_valid e.input_valid
  observation_valid := union_valid d.observation_valid e.observation_valid
  result_valid := union_valid d.result_valid e.result_valid
  stable := fun n W v h => h.elim (d.stable n W v) (e.stable n W v)
  resolved := .union d.resolved e.resolved
  observed := .union d.observed e.observed
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

/-- Finite instance evidence constructs all slots together. A lexical binder
retains its whole descriptor, including its operation witnesses. -/
inductive Certificate where
  | stable (A : Fam) (valid : ValueFam A) (bounded : FamLe A N)
  | native (child : Certificate)
  | union (left right : Certificate)
  | binder (descriptor : Descriptor (capabilities h))

def Certificate.denote : Certificate h → Descriptor (capabilities h)
  | .stable A hv hn => ResolutionCapabilities.stable h A hv hn
  | .native child => ResolutionCapabilities.native h child.denote
  | .union left right => ResolutionCapabilities.union h left.denote right.denote
  | .binder d => d

end

/-- The descriptor domain depends only on the constructor and stable family. -/
theorem domain_congr {ι : Type} {P P' : Fam → Fam} {N N' : Fam}
    (h : NativeSeparation P N) (h' : NativeSeparation P' N') (hp : P' = P) (hn : N' = N) :
    descriptorDomain (ι := ι) (capabilities h') = descriptorDomain (capabilities h) := by
  subst hp hn
  rfl

#print axioms Resolves.exact
#print axioms Observes.exact
#print axioms stable
#print axioms native
#print axioms union
#print axioms Resolves.describe

/-- The modeled operation is safe at every admissible world and satisfying
heap. Unlike an outcome-only relation, this also constrains executions that
throw or do not return. -/
def OperationContract (op : Val → Tm) (A B : Fam) : Prop :=
  ∀ n (W : WorldT n) heap v, WorldAdm W → HeapOk n W heap →
    A n W v → Safe B n W heap (op v)

namespace OperationContract

theorem narrow {op A A' B} (h : OperationContract op A B)
    (ha : FamLe A' A) : OperationContract op A' B :=
  fun n W heap v hw hh hv => h n W heap v hw hh (ha n W v hv)

theorem widen {op A B B'} (h : OperationContract op A B)
    (hb : FamLe B B') : OperationContract op A B' := by
  intro n W heap v hw hh hv
  exact Safe_mono n (fun m _ U u hu => hb m U u hu) W heap (op v)
    (h n W heap v hw hh hv)

theorem union {op A B R S} (ha : OperationContract op A R)
    (hb : OperationContract op B S) :
    OperationContract op (unionT A B) (unionT R S) := by
  intro n W heap v hw hh hv
  rcases hv with hv | hv
  · exact ha.widen (fun _ _ _ h => Or.inl h) n W heap v hw hh hv
  · exact hb.widen (fun _ _ _ h => Or.inr h) n W heap v hw hh hv

theorem union_input {op A B R} :
    OperationContract op (unionT A B) R ↔
      OperationContract op A R ∧ OperationContract op B R := by
  constructor
  · intro h
    exact ⟨h.narrow (fun _ _ _ h => Or.inl h), h.narrow (fun _ _ _ h => Or.inr h)⟩
  · rintro ⟨ha, hb⟩ n W heap v hw hh (hv | hv)
    · exact ha n W heap v hw hh hv
    · exact hb n W heap v hw hh hv
end OperationContract

/-- Reviewed host contracts expressed in the verifier's own world and safety
model. `fresh` returns a native promise, while `observe` returns its delivered
value. Fresh resolution is not the native-identity operation Promise.resolve.
These are explicit premises, not consequences of structural Promise methods. -/
structure NativeOperationContracts (P : Fam → Fam) (N : Fam)
    (observe fresh : Val → Tm) : Prop where
  promise_mono : ∀ {A B}, FamLe A B → FamLe (P A) (P B)
  observe_stable : ∀ {A}, ValueFam A → FamLe A N → OperationContract observe A A
  fresh_stable : ∀ {A}, ValueFam A → FamLe A N → OperationContract fresh A (P A)
  observe_native : ∀ A, OperationContract observe (P A) A
  fresh_native : ∀ {A R}, OperationContract fresh A (P R) →
    OperationContract fresh (P A) (P R)

/-- Every finite observation derivation supplies the actual safety contract. -/
theorem Observes.safe {P N observe fresh}
    (host : NativeOperationContracts P N observe fresh)
    {A O} (h : Observes P N A O) : OperationContract observe A O := by
  induction h with
  | stable hv hn => exact host.observe_stable hv hn
  | native _ => exact host.observe_native _
  | union _ _ ih₁ ih₂ => exact ih₁.union ih₂

/-- Resolution derivations produce the declared native result; safety includes
world evolution and every intermediate computation admitted by Safe. -/
theorem Resolves.safe {P N observe fresh}
    (host : NativeOperationContracts P N observe fresh)
    {A R} (h : Resolves P N A R) : OperationContract fresh A (P R) := by
  induction h with
  | stable hv hn => exact host.fresh_stable hv hn
  | native _ ih => exact host.fresh_native ih
  | union _ _ ih₁ ih₂ =>
      apply (OperationContract.union_input).mpr
      exact ⟨ih₁.widen (host.promise_mono (fun _ _ _ h => Or.inl h)),
        ih₂.widen (host.promise_mono (fun _ _ _ h => Or.inr h))⟩

#print axioms OperationContract.union_input
#print axioms Observes.safe
#print axioms Resolves.safe

end Verification.ResolutionCapabilities
