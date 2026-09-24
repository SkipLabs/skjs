import Verification.Model.Types.TypeParams

/-! # Quantified rows in the type graph

A generic method's type, such as `Promise<T>`'s
`then<R1, R2>(onfulfilled?: (value: T) => R1 | PromiseLike<R1>, …) => …`, is a
row of its own kind: its binders, which are parameter rows, and the signatures
its instances meet. The rows its signatures reach (`PromiseLike<R1>`) mention
the binders, so their meaning depends on what the binders are assigned.

The denotation is therefore indexed by an assignment of the parameter rows as
well as by the label: a parameter row means what the assignment gives it, a
scheme row means a callable meeting its signatures at every admissible
reassignment of its binders, each signature's rows read at that assignment, and
any other row means its clauses. The fixed point is the one `Tower` builds for
every positive graph, over the index `(assignment, label)`. Without scheme rows
it is the parametric semantics `denoteP`, at each assignment.

The quantifier ranges over every admissible family. A bound on a binder is not
part of this row: bounded binders are a separate step. -/
namespace Verification.Model.QuantifiedGraphs
open PositiveNormalization PositiveGraphs PositiveRules Tower TypeParams ProgramTyping

variable {ι : Type} [DecidableEq ι]

/-- An assignment of admissible families to the parameter rows. -/
abbrev Env (ι : Type) := { η : ι → Fam // ∀ i, Adm (η i) }

/-- An admissible family, what a binder may be instantiated at. -/
abbrev AdmFam := { A : Fam // Adm A }

/-- A quantified callable: its binders, which are parameter rows, and the
signatures `(receiver, parameters, result)` each of its instances meets. -/
structure SchemeRow (ι : Type) where
  binders : List ι
  signatures : List (List ι × List (List ι) × List ι)

/-- The assignment with each binder given the family at its position. -/
def assign (η : Env ι) (bs : List ι) (As : List AdmFam) : Env ι :=
  ⟨fun i => match (bs.zip As).lookup i with
      | some A => A.1
      | none => η.1 i,
   fun i => by
      cases h : (bs.zip As).lookup i with
      | some A => simpa [h] using A.2
      | none => simpa [h] using η.2 i⟩

/-- One instance's signatures, their rows read at the reassignment. -/
def instanceSigs (D : Env ι → List ι → Fam) (η : Env ι) (s : SchemeRow ι) (As : List AdmFam) :
    List (Fam × List Fam × Fam) :=
  let η' := assign η s.binders As
  s.signatures.map fun p => (D η' p.1, p.2.1.map (D η'), D η' p.2.2)

/-- **A scheme row.** A callable meeting its signatures at every admissible
instantiation of its binders: the same value, in the same world, at all of
them. -/
def schemeSem (D : Env ι → List ι → Fam) (η : Env ι) (s : SchemeRow ι) : Fam := fun n W v =>
  Invocable v ∧ ∀ As : List AdmFam, As.length = s.binders.length →
    callsT (instanceSigs D η s As) n W v

/-- One step of the assignment-indexed denotation. -/
def qLayer (G : NormalGraph ι) (P : ι → Bool) (Q : ι → Option (SchemeRow ι))
    (X : Env ι × ι → Fam) : Env ι × ι → Fam := fun ηi =>
  if P ηi.2 then ηi.1.1 ηi.2 else
  match Q ηi.2 with
  | some s => schemeSem (fun η' S => setSem (fun l => X (η', l)) S) ηi.1 s
  | none => normalLayer G (fun l => X (ηi.1, l)) ηi.2

private theorem argsAgree_map {n : Nat} (X Y : ι → Fam) (h : ∀ l, Agree (X l) (Y l) n) :
    ∀ Ss : List (List ι), ArgsAgree n (Ss.map (setSem X)) (Ss.map (setSem Y))
  | [] => .nil
  | S :: Ss => .cons (setSem_congr n h S) (argsAgree_map X Y h Ss)

theorem qLayer_congr (G : NormalGraph ι) (P : ι → Bool) (Q : ι → Option (SchemeRow ι)) :
    LayerCongr (qLayer G P Q) := by
  intro X Y n h ηi W v
  obtain ⟨η, i⟩ := ηi
  unfold qLayer
  by_cases hp : P i = true
  · simp [hp]
  · simp only [hp]
    cases hq : Q i with
    | none => exact normal_congr G _ _ n (fun l => h (η, l)) i W v
    | some s =>
      simp only [schemeSem]
      refine and_congr Iff.rfl (forall_congr' fun As => forall_congr' fun _ => ?_)
      unfold instanceSigs
      exact callsT_congr s.signatures _ _ (fun p _ =>
        ⟨setSem_congr n (fun l => h (_, l)) p.1,
         argsAgree_map _ _ (fun l => h (_, l)) p.2.1,
         setSem_congr n (fun l => h (_, l)) p.2.2⟩) W v

theorem schemeSem_adm (D : Env ι → List ι → Fam) (η : Env ι) (s : SchemeRow ι) :
    Adm (schemeSem D η s) := by
  constructor
  · intro n W v h
    exact ⟨h.1, fun As hl => (callsT_adm _).down n W v (h.2 As hl)⟩
  · intro n W W' hx v h
    exact ⟨h.1, fun As hl => (callsT_adm _).mono n W W' hx v (h.2 As hl)⟩

theorem qLayer_adm (G : NormalGraph ι) (P : ι → Bool) (Q : ι → Option (SchemeRow ι)) :
    LayerAdm (qLayer G P Q) := by
  intro X _ ηi
  obtain ⟨η, i⟩ := ηi
  unfold qLayer
  by_cases hp : P i = true
  · simpa [hp] using η.2 i
  · simp only [hp]
    cases hq : Q i with
    | none => simpa [normalLayer, semList] using
        setSem_adm (fun c => sem_adm (setSem fun l => X (η, l)) c) (G i)
    | some s => exact schemeSem_adm _ _ s

/-- The denotation at every assignment. -/
def qDenote (G : NormalGraph ι) (P : ι → Bool) (Q : ι → Option (SchemeRow ι)) :
    Env ι × ι → Fam :=
  Tower.denote (qLayer G P Q)

theorem qDenote_unfold (G : NormalGraph ι) (P : ι → Bool) (Q : ι → Option (SchemeRow ι))
    (ηi : Env ι × ι) (n : Nat) (W : WorldT n) (v : Val) :
    qDenote G P Q ηi n W v ↔ qLayer G P Q (qDenote G P Q) ηi n W v :=
  Tower.denote_unfold (qLayer_congr G P Q) ηi n W v

theorem qDenote_adm (G : NormalGraph ι) (P : ι → Bool) (Q : ι → Option (SchemeRow ι))
    (ηi : Env ι × ι) : Adm (qDenote G P Q ηi) :=
  Tower.denote_adm (qLayer_congr G P Q) (qLayer_adm G P Q) ηi

/-- A label list's meaning at an assignment. -/
def qMeaning (G : NormalGraph ι) (P : ι → Bool) (Q : ι → Option (SchemeRow ι))
    (η : Env ι) (S : List ι) : Fam :=
  setSem (fun l => qDenote G P Q (η, l)) S

/-- A scheme row's meaning, unfolded. -/
theorem scheme_row {G : NormalGraph ι} {P : ι → Bool} {Q : ι → Option (SchemeRow ι)}
    {η : Env ι} {i : ι} {s : SchemeRow ι} (hp : P i = false) (hq : Q i = some s)
    (n : Nat) (W : WorldT n) (v : Val) :
    qDenote G P Q (η, i) n W v ↔ schemeSem (qMeaning G P Q) η s n W v := by
  rw [qDenote_unfold]
  simp only [qLayer, hp, hq, Bool.false_eq_true, if_false]
  exact Iff.rfl

/-- **Instantiation.** A member of a scheme row meets each of its instances. -/
theorem scheme_elim {G : NormalGraph ι} {P : ι → Bool} {Q : ι → Option (SchemeRow ι)}
    {η : Env ι} {i : ι} {s : SchemeRow ι} (hp : P i = false) (hq : Q i = some s)
    {n : Nat} {W : WorldT n} {v : Val} (h : qDenote G P Q (η, i) n W v)
    (As : List AdmFam) (hl : As.length = s.binders.length) :
    callsT (instanceSigs (qMeaning G P Q) η s As) n W v :=
  ((scheme_row hp hq n W v).mp h).2 As hl

/-- A row that is neither a parameter nor a scheme means its clauses, read at
the same assignment. -/
theorem clause_row {G : NormalGraph ι} {P : ι → Bool} {Q : ι → Option (SchemeRow ι)}
    {η : Env ι} {i : ι} (hp : P i = false) (hq : Q i = none)
    (n : Nat) (W : WorldT n) (v : Val) :
    qDenote G P Q (η, i) n W v ↔ semList (setSem fun l => qDenote G P Q (η, l)) (G i) n W v := by
  rw [qDenote_unfold]
  simp [qLayer, hp, hq, normalLayer]

/-- A parameter row means what the assignment gives it. -/
theorem param_row {G : NormalGraph ι} {P : ι → Bool} {Q : ι → Option (SchemeRow ι)}
    {η : Env ι} {i : ι} (hp : P i = true) (n : Nat) (W : WorldT n) (v : Val) :
    qDenote G P Q (η, i) n W v ↔ η.1 i n W v := by
  rw [qDenote_unfold]
  simp [qLayer, hp]

private theorem approx_bridge (G : NormalGraph ι) (P : ι → Bool) (η : Env ι) :
    ∀ k, (fun i => Tower.approx (qLayer G P (fun _ => none)) k (η, i)) =
      Tower.approx (paramLayer G P η.1) k
  | 0 => rfl
  | k + 1 => by
    funext i
    have ih := approx_bridge G P η k
    show qLayer G P (fun _ => none) (Tower.approx (qLayer G P (fun _ => none)) k) (η, i) =
      paramLayer G P η.1 (Tower.approx (paramLayer G P η.1) k) i
    rw [← ih]
    unfold qLayer paramLayer
    rfl

/-- **Conservative.** Without scheme rows, the denotation at an assignment is
the parametric semantics at that assignment. -/
theorem qDenote_no_schemes (G : NormalGraph ι) (P : ι → Bool) (η : Env ι) (i : ι) :
    qDenote G P (fun _ => none) (η, i) = denoteP G P η.1 i := by
  funext n
  show Tower.approx (qLayer G P (fun _ => none)) (n + 1) (η, i) n =
    Tower.approx (paramLayer G P η.1) (n + 1) i n
  rw [← approx_bridge G P η (n + 1)]

#print axioms qDenote_adm
#print axioms scheme_elim
#print axioms qDenote_no_schemes

end Verification.Model.QuantifiedGraphs
