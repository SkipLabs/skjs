import Verification.Model.Programs.ProgramTyping

/-! # Quantified rows in the type graph

A generic method's type, such as `Promise<T>`'s
`then<R1, R2>(onfulfilled?: (value: T) => R1 | PromiseLike<R1>, …) => …`, is a
scheme row: its binders, which are parameter rows, and the signatures its
instances meet. The rows its signatures reach (`PromiseLike<R1>`) mention the
binders, so their meaning depends on what the binders are assigned.

The denotation (`PositiveGraphs.qDenoteWithArgs` under `mixedParameters`) is
therefore indexed by an assignment as well as by a label, and a graph's
`meaning` reads it at the graph's own assignment, `env`. An assignment gives
each binder a mixed family: a value binder reads its runtime values, a pack
binder its argument lists. This file states the rules the rows obey:

* a parameter row means what the assignment gives it;
* a clause row means its clauses, read at the same assignment;
* **elimination**: a member of a scheme row meets each instance's signatures;
* **introduction**: a callable meeting, at every instantiation, the signatures
  read in the graph reassigned there is a member of the scheme row.

Reassigning a graph is `reassign G η`, `{G with env := η}`. No check reads
`env`: the syntactic judgments read a graph only through its rows, so a
derivation over `G` is one over every reassignment. `Sub.sound_at` states it
for subtyping; a generic body, typed once with its binders opaque, discharges
the introduction premise the same way.

The subtyping rules over scheme rows are in `PositiveRules`: `Sub.inst`
(elimination: a scheme below a checked instance of its signatures, named by an
instance map, `inst_type`) and `Sub.gen` (generalization: a type reading none
of a scheme's binders, below its signatures with the binders opaque, is below
the scheme, `agree_free`).

The quantifier ranges over every family of closed values. A bound on a binder
is not part of this row: bounded binders are a separate step. -/
namespace Verification.Model.QuantifiedGraphs
open PositiveNormalization PositiveGraphs PositiveRules Tower ProgramTyping

variable {ι : Type}

/-- The reassigned graph's meaning is the denotation at `η`: the fixed point
does not read the assignment it is taken at. -/
theorem meaning_reassign (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι) :
    meaning (reassign G η) S = mixedValues G η S := rfl

theorem meaning_env (G : NormalGraph ι) (S : List ι) : meaning G S = mixedValues G G.env S := rfl

/-- The row denotation at an assignment. -/
noncomputable abbrev qDenote (G : NormalGraph ι) : MixedAssignment ι × ι → Fam :=
  qDenoteWithArgs G (mixedParameters G)

/-- A scheme row's meaning, unfolded. -/
theorem scheme_row {G : NormalGraph ι} {η : MixedAssignment ι} {i : ι} {s : SchemeRow ι}
    (hp : G.params i = false) (hq : G.schemes i = some s) (n : Nat) (W : WorldT n) (v : Val) :
    qDenote G (η, i) n W v ↔
      schemeSemWithArgs (mixedParameters G) (fun η' S => mixedValues G η' S) η s n W v := by
  show qDenoteWithArgs G (mixedParameters G) (η, i) n W v ↔ _
  rw [qDenoteWithArgs_unfold]
  simp only [qLayerWithArgs, hp, hq, Bool.false_eq_true, if_false]
  exact Iff.rfl

/-- **Instantiation.** A member of a scheme row meets each of its instances
within its bounds, each signature read at that instance. -/
theorem scheme_elim {G : NormalGraph ι} {i : ι} {s : SchemeRow ι}
    (hp : G.params i = false) (hq : G.schemes i = some s)
    {n : Nat} {W : WorldT n} {v : Val} (h : meaning G [i] n W v)
    (As : List MixedFamily) (hl : As.length = s.binders.length)
    (hb : Bounded (fun η S => mixedMeaning G η S) G.env s As n) :
    instanceTWithArgs (fun η S => mixedValues G η S) G.env s As (graphArguments G) n W v := by
  obtain ⟨_, hi, hv⟩ := h
  cases List.mem_singleton.mp hi
  exact ((scheme_row hp hq n W v).mp hv).2 As hl hb

/-- **Generalization.** A callable meeting every instance's signatures, each
read at that instance, is a member of the scheme row. -/
theorem scheme_intro {G : NormalGraph ι} {i : ι} {s : SchemeRow ι}
    (hp : G.params i = false) (hq : G.schemes i = some s)
    {n : Nat} {W : WorldT n} {v : Val} (hv : Invocable v)
    (h : ∀ As : List MixedFamily, As.length = s.binders.length →
      Bounded (fun η S => mixedMeaning G η S) G.env s As n →
      instanceTWithArgs (fun η S => mixedValues G η S) G.env s As (graphArguments G) n W v) :
    meaning G [i] n W v :=
  ⟨i, List.mem_singleton_self i, (scheme_row hp hq n W v).mpr ⟨hv, h⟩⟩

/-- A clause row means its clauses, read at the same assignment. -/
theorem clause_row {G : NormalGraph ι} {η : MixedAssignment ι} {i : ι} (hi : G.plain i = true)
    (n : Nat) (W : WorldT n) (v : Val) :
    qDenote G (η, i) n W v ↔ setSem (mixedSem G η) (G i) n W v :=
  mixed_unfold_plain η hi n W v

/-- A parameter row means the component of its assignment its kind selects. -/
theorem param_row {G : NormalGraph ι} {η : MixedAssignment ι} {i : ι} (hp : G.params i = true)
    (n : Nat) (W : WorldT n) (v : Val) :
    qDenote G (η, i) n W v ↔ G.parameterKinds i = some .value ∧ η.1 i n W (.inl v) := by
  show qDenoteWithArgs G (mixedParameters G) (η, i) n W v ↔ _
  rw [qDenoteWithArgs_unfold]
  simp [qLayerWithArgs, mixedParameters, hp]

#print axioms scheme_elim
#print axioms scheme_intro

end Verification.Model.QuantifiedGraphs
