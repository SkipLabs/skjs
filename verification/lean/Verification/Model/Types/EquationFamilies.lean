import Verification.Model.Types.EquationCertificates

/-! Family subtyping on recursive equations (RECURSIVE-EQUATIONS §6–§7). The
equation graph supplies what the generic rules need (`Renaming`): structural
substitution and free support with their proved laws, and family variables,
which are labels of their own (`Tree.var`), so no scheme binds one. Each
head's variance declaration is a family entry; the declarations are checked
together, once (`Variances`), and the `Var` rule relates two applications of
one head by an instance of its entry, without unfolding it. -/
namespace Verification.Model.EquationGraphs
open PositiveGraphs PositiveRules PositiveCertificates PositiveNormalization

/-! ## The renaming of equation graphs -/

/- Whether a tree occurs anywhere in another: the claim discipline of §7.1. -/
mutual
def Tree.subtrees : Tree → List Tree
  | .app h args => .app h args :: args.subtrees
  | .bound h args i => .bound h args i :: args.subtrees
  | .meet ps => .meet ps :: ps.subtrees
  | t => [t]
def Types.subtrees : Types → List Tree
  | .nil => []
  | .cons t ts => t.subtrees ++ ts.subtrees
def Args.subtrees : Args → List Tree
  | .nil => []
  | .cons ts args => ts.subtrees ++ args.subtrees
end

/-- Substitution into a type: the union of its labels' substitutions. -/
def substituteAll (σ : List (Label sig × List (Label sig))) (A : List (Label sig)) :
    List (Label sig) :=
  A.flatMap fun l => l.substitute (replace σ)

private theorem meaning_cons (G : NormalGraph ι) (η : MixedAssignment ι) (l : ι) (A : List ι)
    (n : Nat) (W : WorldT n) (x : ParameterSpace.mixed.Carrier) :
    mixedMeaning G η (l :: A) n W x ↔ mixedMeaning G η [l] n W x ∨ mixedMeaning G η A n W x := by
  rw [mixedMeaning_union G η (l :: A), mixedMeaning_union G η [l], mixedMeaning_union G η A]
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left]

private theorem meaning_append (G : NormalGraph ι) (η : MixedAssignment ι) (A B : List ι)
    (n : Nat) (W : WorldT n) (x : ParameterSpace.mixed.Carrier) :
    mixedMeaning G η (A ++ B) n W x ↔ mixedMeaning G η A n W x ∨ mixedMeaning G η B n W x := by
  rw [mixedMeaning_union G η (A ++ B), mixedMeaning_union G η A, mixedMeaning_union G η B]
  simp only [List.mem_append, or_and_right, exists_or]

/-- Substitution into a union means the union of its labels' meanings at the
images (`Label.substitute_meaning`). -/
theorem Equations.substituteAll_meaning (equations : Equations)
    (η θ : MixedAssignment (Label equations.signature))
    (σ : List (Label equations.signature × List (Label equations.signature)))
    (images : ∀ p, equations.graph.params p = true →
      mixedMeaning equations.graph η [p] = mixedMeaning equations.graph θ (replace σ p)) :
    ∀ A, mixedMeaning equations.graph η A = mixedMeaning equations.graph θ (substituteAll σ A)
  | [] => by simp only [substituteAll, List.flatMap_nil, mixedMeaning_nil]
  | l :: A => by
    have hl := Label.substitute_meaning equations η θ (replace σ) images l
    have hA := equations.substituteAll_meaning η θ σ images A
    funext n W x
    apply propext
    rw [meaning_cons, show substituteAll σ (l :: A) = l.substitute (replace σ) ++ substituteAll σ A
      from List.flatMap_cons .., meaning_append, hl, hA]

/-- A scheme row of an equation graph binds its application's owned labels,
never a family variable. -/
theorem Equations.scheme_binders (equations : Equations) (i : Label equations.signature)
    (s : SchemeRow (Label equations.signature)) (hs : equations.graph.schemes i = some s) :
    ∀ x ∈ s.binders, x.isVariable = false := by
  revert hs
  apply i.cases
  · intro scope hs
    have hv := (equations.body scope.head).2
    cases hb : (equations.body scope.head).1 with
    | scheme bs sigs bounds rests =>
      simp only [hb, RowTemplate.wellBound, Bool.and_eq_true_iff, decide_eq_true_eq] at hv
      simp only [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Scope.view_label,
        Template.instantiate, hb, GraphRow.map, Option.some.injEq] at hs
      subst hs
      intro x hx
      rw [scope.instantiate_binders bs hv.1] at hx
      obtain ⟨slot, rfl⟩ := Scope.mem_binders.mp hx
      rfl
    | clauses cs =>
      simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Template.instantiate, hb,
        GraphRow.map] at hs
    | param p name kind =>
      simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Template.instantiate, hb,
        GraphRow.map] at hs
    | meet p cs ps =>
      simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Template.instantiate, hb,
        GraphRow.map] at hs
  · intro scope slot hs
    simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow] at hs
  · intro o i k hs
    simp [Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow] at hs
  · intro ps valid hs
    rw [(equations.meet_rigid ps valid).1] at hs
    cases hs

/-- A family variable is a parameter row. -/
theorem Equations.variable_param (equations : Equations) (x : Label equations.signature)
    (hx : x.isVariable = true) : equations.graph.params x = true := by
  obtain ⟨t, valid⟩ := x
  cases t with
  | var o i k =>
    simp [NormalGraph.params, Equations.graph, NormalGraph.ofRowMap, Equations.row, Equations.baseRow, Label.view]
  | _ => simp [Label.isVariable] at hx

/-- **The equation graph's renaming.** Substitution is `Label.substitute`,
free support `Label.free`, and family variables are `Tree.var` labels. -/
def Equations.renaming (equations : Equations) : Renaming equations.graph where
  substitute := substituteAll
  free A := A.flatMap Label.free
  familyVar := Label.isVariable
  mentions A x := A.any fun l => decide (x.1 ∈ l.1.subtrees)
  substitute_meaning η θ σ images := equations.substituteAll_meaning η θ σ images
  agree_free η θ A h := equations.agree_free η θ A fun l hl p hp =>
    h p (List.mem_flatMap.mpr ⟨l, hl, hp⟩)
  familyVar_param x hx := equations.variable_param x hx
  familyVar_unbound i s x hs hx hin := by
    have := equations.scheme_binders i s hs x hin
    rw [hx] at this
    cases this

/-! ## Variance declarations -/

/-- The arguments of head `h`'s declaration entry on one side: for parameter
`i`, the variable owned by `h` at slot `2i + side`, of the declared kind. -/
def varianceArgs (h : Fin sig.length) (side : Nat) : List (List (Label sig)) :=
  sig[h].variance.mapIdx fun i d => [Label.familyVar h.val (2 * i + side) d.1]

/-- One side of head `h`'s declaration entry: `h` applied to its variables. A
declaration of the wrong length has none. -/
def varianceSide (h : Fin sig.length) (side : Nat) : List (Label sig) :=
  if hl : sig[h].variance.length = sig[h].parameters then
    [(Scope.mk h (varianceArgs h side) (by simp only [varianceArgs, List.length_mapIdx]; exact hl)).label]
  else []

/-- The hypotheses a declaration reads off its variances: `x ≤ y` for `co`,
`y ≤ x` for `contra`, both for `inv`, none for `none`. -/
def varianceHypotheses (h : Fin sig.length) : List (Label sig × Label sig) :=
  (sig[h].variance.mapIdx fun i d =>
    let x := Label.familyVar h.val (2 * i) d.1
    let y := Label.familyVar h.val (2 * i + 1) d.1
    match d.2 with
    | .co => [(x, y)]
    | .contra => [(y, x)]
    | .inv => [(x, y), (y, x)]
    | .none => []).flatten

/-- The variables of `h`'s declaration, in the order `Var` instantiates them:
`x₀, y₀, x₁, y₁, …`. -/
def varianceVariables (h : Fin sig.length) : List (Label sig) :=
  (sig[h].variance.mapIdx fun i d =>
    [Label.familyVar h.val (2 * i) d.1, Label.familyVar h.val (2 * i + 1) d.1]).flatten

/-- The producer's evidence for the declarations: per head, a table and the
instances its premises name, and arrow evidence for all of them. -/
structure VarianceEvidence (sig : Signature) where
  tables : List (Nat × Table (Label sig)) := []
  instances : List (Nat × List (Nat × List (List (Label sig)))) := []
  arrows : Evidence (Label sig) := []

/-- Head `h`'s declaration as a family entry: `h(x⃗) ≤ h(y⃗)` with the
hypotheses its variances state (§7.5). -/
def varianceEntry (ev : VarianceEvidence sig) (h : Fin sig.length) : Entry (Label sig) where
  source := varianceSide h 0
  target := varianceSide h 1
  variables := varianceVariables h
  hypotheses := varianceHypotheses h
  table := (ev.tables.lookup h.val).getD []
  instances := (ev.instances.lookup h.val).getD []

/-- Every head's entry, at its head's index. -/
def varianceEntries (ev : VarianceEvidence sig) : List (Entry (Label sig)) :=
  (List.finRange sig.length).map (varianceEntry ev)

def interleave : List α → List α → List α
  | a :: as, b :: bs => a :: b :: interleave as bs
  | _, _ => []

/-- **`Var` as a premise.** A label `h(A⃗)` and a label `h(B⃗)` of the target
propose the instance of `h`'s declaration at `x⃗ := A⃗`, `y⃗ := B⃗`. Only a
proposal: the premise holds when it is checked like any instance, each
hypothesis discharged by a table pair, a subset or a hypothesis. -/
def varGen (l : Label sig) (B : List (Label sig)) : List (Nat × List (List (Label sig))) :=
  match l.view with
  | .application a => B.filterMap fun b => match b.view with
    | .application c => if a.head = c.head then some (a.head.val, interleave a.arguments c.arguments)
      else none
    | _ => none
  | _ => []

/-- Each head declares one kind and variance per parameter. -/
def declarationsOk (sig : Signature) : Bool :=
  (List.finRange sig.length).all fun h => sig[h].variance.length == sig[h].parameters

/-- **The declarations, checked once**: every head's entry valid, together,
their premises drawing on each other through `Var`. -/
def Equations.checkVariance (equations : Equations) (ev : VarianceEvidence equations.signature) : Bool :=
  declarationsOk equations.signature &&
    variablesOk (some equations.renaming) (varianceEntries ev) &&
    checkEntries equations.graph (some equations.renaming) [] varGen [] (varianceEntries ev) ev.arrows

/-- The heads whose declaration fails, each checked against all the others:
the located refusal. -/
def Equations.varianceRefused (equations : Equations) (ev : VarianceEvidence equations.signature) :
    List Nat :=
  (List.finRange equations.signature.length).filterMap fun h =>
    if equations.signature[h].variance.length == equations.signature[h].parameters &&
        checkEntries equations.graph (some equations.renaming) [] varGen (varianceEntries ev)
          [varianceEntry ev h] ev.arrows then none
    else some h.val

/-- Equations whose variance declarations have been checked. -/
structure Variances (equations : Equations) where
  evidence : VarianceEvidence equations.signature
  checked : equations.checkVariance evidence = true

/-- Check the declarations once, keeping the result. -/
def Variances.check? (equations : Equations) (ev : VarianceEvidence equations.signature) :
    Option (Variances equations) :=
  if h : equations.checkVariance ev = true then some ⟨ev, h⟩ else none

/-- **Checked declarations are sound**: each head's entry holds wherever its
hypotheses do (§7.4). -/
theorem Variances.sound {equations : Equations} (v : Variances equations) :
    ∀ e ∈ varianceEntries v.evidence, EntrySound equations.graph e := by
  have h := v.checked
  simp only [Equations.checkVariance, Bool.and_eq_true] at h
  exact checkEntries_entries_sound h.2 h.1.2

/-- **Family subtyping on equations.** A certificate's entries may use `Var`
on every declared head; the claim is a pair of a variable-free entry. -/
def Equations.checkFamily (equations : Equations) (v : Variances equations)
    (S T : List (Label equations.signature)) (c : FamilyCertificate (Label equations.signature)) :
    Bool :=
  checkFamilyUsing equations.graph equations.instanceImageCheck (some equations.renaming) varGen
    (varianceEntries v.evidence) S T c

theorem Equations.checkFamily_sound (equations : Equations) (v : Variances equations)
    {S T : List (Label equations.signature)} {c : FamilyCertificate (Label equations.signature)}
    (h : equations.checkFamily v S T c = true) :
    ∀ η, FamLe (mixedMeaning equations.graph η S) (mixedMeaning equations.graph η T) :=
  checkFamilyUsing_sound h v.sound

/-- **The structural `Var` rule.** `h(A⃗) ≤ h(B⃗)` by one derivation per
hypothesis of `h`'s declaration, in order: `Aᵢ ≤ Bᵢ` for `co`, `Bᵢ ≤ Aᵢ` for
`contra`, both for `inv`, none for `none`. `h` is not unfolded. -/
def Equations.checkVar (equations : Equations) (v : Variances equations)
    (S T : List (Label equations.signature)) (proofs : List (Proof (Label equations.signature))) :
    Bool :=
  match S, T with
  | [l], [b] => match varGen l [b] with
    | [w] => checkEntryInstanceUsing equations.graph equations.instanceImageCheck
        equations.renaming (varianceEntries v.evidence) w S T proofs
    | _ => false
  | _, _ => false

theorem Equations.checkVar_sound (equations : Equations) (v : Variances equations)
    {S T : List (Label equations.signature)} {proofs : List (Proof (Label equations.signature))}
    (h : equations.checkVar v S T proofs = true) :
    ∀ η, FamLe (mixedMeaning equations.graph η S) (mixedMeaning equations.graph η T) := by
  unfold Equations.checkVar at h
  split at h
  · split at h
    · exact checkEntryInstanceUsing_sound h v.sound
    · cases h
  · cases h

#print axioms Equations.substituteAll_meaning
#print axioms Equations.scheme_binders
#print axioms Variances.sound
#print axioms Equations.checkFamily_sound
#print axioms Equations.checkVar_sound

end Verification.Model.EquationGraphs
