import Verification.Model.Types.PositiveNormalization

/-! Normalize each body of a guarded recursive graph without unfolding cycles
or allocating new labels. A label names a whole positive formula; normalized
labels name finite unions of clauses. Operands remain lists of labels. -/
namespace Verification.Model.PositiveGraphs
open PositiveNormalization Tower

abbrev Graph (ι : Type) := ι → Formula (List ι)

/-! ## Rows of a normal graph

A label's row is one of three kinds. A clause row means a finite union of
clauses. A parameter row is a binder of some scheme and means what the graph's
assignment gives it. A scheme row is a generic callable, such as `Promise<T>`'s
`then<R1, R2>`: a value meeting its signatures at every instantiation of its
binders.

The assignment is part of the graph. No check reads it; it enters only the
semantics. A theorem proved for every graph therefore holds at every
assignment, which is what typing a generic body once, for all of its
instances, needs. -/

/-- Semantic binders distinguish a runtime value from an argument list. -/
inductive ParameterKind where
  | value
  | arguments
  deriving DecidableEq, BEq, Repr, Inhabited

abbrev ParameterKind.Carrier : ParameterKind → Type
  | .value => Val
  | .arguments => List Val

abbrev ParameterKind.Closed : (k : ParameterKind) → k.Carrier → Prop
  | .value => fun (v : Val) => isVal v = true ∧ Scoped 0 v
  | .arguments => fun (vs : List Val) => ∀ v ∈ vs, isVal v = true ∧ Scoped 0 v

/-- The assignment algebra depends on a carrier and its closedness predicate,
not on every binder in a scheme having the same source-language kind. -/
structure ParameterSpace where
  Carrier : Type
  Closed : Carrier → Prop

abbrev ParameterSpace.value : ParameterSpace :=
  ⟨ParameterKind.Carrier .value, ParameterKind.Closed .value⟩
abbrev ParameterSpace.arguments : ParameterSpace :=
  ⟨ParameterKind.Carrier .arguments, ParameterKind.Closed .arguments⟩

/-- A semantic sum, not a calculus value constructor. It permits a single
substitution to contain both ordinary types and whole argument-list types. -/
abbrev ParameterSpace.mixed : ParameterSpace :=
  ⟨Val ⊕ List Val, fun
    | .inl v => ParameterKind.Closed .value v
    | .inr vs => ParameterKind.Closed .arguments vs⟩

/-- Both sorts obey the same approximation and world-extension laws. List
membership is at the current level; changing sorts does not insert a guard. -/
def ParameterValid (k : ParameterSpace) (A : WorldFamily k.Carrier) : Prop :=
  Adm A ∧ ∀ n W v, A n W v → k.Closed v

abbrev ParameterFamily (k : ParameterSpace) := { A : WorldFamily k.Carrier // ParameterValid k A }
abbrev ParameterAssignment (k : ParameterSpace) (ι : Type) :=
  { η : ι → WorldFamily k.Carrier // ∀ i, ParameterValid k (η i) }

/-- The production value environment is the value instance of the shared
assignment algebra, rather than a separate implementation. -/
abbrev ValueFam (A : Fam) : Prop := ParameterValid .value A
abbrev ValueFamily := ParameterFamily .value
abbrev Assignment (ι : Type) := ParameterAssignment .value ι
abbrev ArgumentFamily := ParameterFamily .arguments
abbrev ArgumentAssignment (ι : Type) := ParameterAssignment .arguments ι
abbrev MixedFamily := ParameterFamily .mixed
abbrev MixedAssignment (ι : Type) := ParameterAssignment .mixed ι

/-- Project a value contract without interpreting a list as a runtime value. -/
def MixedFamily.value (A : MixedFamily) : ValueFamily :=
  ⟨fun n W v => A.1 n W (.inl v),
    ⟨⟨fun n W v h => A.2.1.down n W (.inl v) h,
      fun n W U hx v h => A.2.1.mono n W U hx (.inl v) h⟩,
      fun n W v h => A.2.2 n W (.inl v) h⟩⟩

/-- Project a current-level contract on an actual argument list. -/
def MixedFamily.arguments (A : MixedFamily) : ArgumentFamily :=
  ⟨fun n W vs => A.1 n W (.inr vs),
    ⟨⟨fun n W vs h => A.2.1.down n W (.inr vs) h,
      fun n W U hx vs h => A.2.1.mono n W U hx (.inr vs) h⟩,
      fun n W vs h => A.2.2 n W (.inr vs) h⟩⟩

/-- An ordinary substitution argument has no argument-list members. -/
def MixedFamily.ofValue (A : ValueFamily) : MixedFamily :=
  ⟨fun n W x => match x with | .inl v => A.1 n W v | .inr _ => False,
    ⟨⟨fun n W x h => by cases x with
          | inl v => exact A.2.1.down n W v h
          | inr vs => exact h,
        fun n W U hx x h => by cases x with
          | inl v => exact A.2.1.mono n W U hx v h
          | inr vs => exact h⟩,
      fun n W x h => by cases x with
        | inl v => exact A.2.2 n W v h
        | inr vs => exact h.elim⟩⟩

/-- A pack substitution argument has no runtime-value members. -/
def MixedFamily.ofArguments (A : ArgumentFamily) : MixedFamily :=
  ⟨fun n W x => match x with | .inl _ => False | .inr vs => A.1 n W vs,
    ⟨⟨fun n W x h => by cases x with
          | inl v => exact h
          | inr vs => exact A.2.1.down n W vs h,
        fun n W U hx x h => by cases x with
          | inl v => exact h
          | inr vs => exact A.2.1.mono n W U hx vs h⟩,
      fun n W x h => by cases x with
        | inl v => exact h.elim
        | inr vs => exact A.2.2 n W vs h⟩⟩

@[simp] theorem MixedFamily.value_ofValue (A : ValueFamily) : (ofValue A).value = A := rfl
@[simp] theorem MixedFamily.arguments_ofArguments (A : ArgumentFamily) :
    (ofArguments A).arguments = A := rfl

/-- Inclusion at a mixed bound checks both projections; it cannot confuse
value subtyping with argument-list subtyping. -/
theorem MixedFamily.le_iff (A B : MixedFamily) : FamLe A.1 B.1 ↔
    FamLe A.value.1 B.value.1 ∧ FamLe A.arguments.1 B.arguments.1 := by
  constructor
  · intro h
    exact ⟨fun n W v => h n W (.inl v), fun n W vs => h n W (.inr vs)⟩
  · rintro ⟨hv, ha⟩ n W (v | vs) h
    · exact hv n W v h
    · exact ha n W vs h

def ParameterAssignment.empty (k : ParameterSpace) : ParameterAssignment k ι :=
  ⟨fun _ _ _ _ => False,
    fun _ => ⟨⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩, fun _ _ _ h => h.elim⟩⟩

/-- The assignment of a graph without parameter rows: none is read. -/
def Assignment.empty : Assignment ι := ParameterAssignment.empty .value

/-- A quantified callable: its binders, which are parameter rows, and the
signatures `(receiver, parameters, result)` each of its instances meets. -/
structure SchemeRow (ι : Type) where
  binders : List ι
  signatures : List (List ι × List (List ι) × List ι)
  /-- Upper bounds `(binder, type)`: an instance gives the binder a family below
  the type, read at the scheme's own assignment (a bound does not mention the
  scheme's binders). -/
  bounds : List (ι × List ι) := []
  /-- Variadic signatures `(receiver, parameters, rest, result)`, the rest an
  argument-list type; a binder may be one. -/
  variadic : List (List ι × List (List ι) × List ι × List ι) := []
  deriving DecidableEq, Repr

structure NormalGraph (ι : Type) where
  /-- A clause row's clauses. -/
  rows : ι → List (Clause (List ι))
  schemes : ι → Option (SchemeRow ι) := fun _ => none
  parameterKinds : ι → Option ParameterKind := fun _ => none
  /-- What the parameter rows mean. Semantic only. -/
  env : Assignment ι := Assignment.empty

/-- Whether a row is a parameter is derived from its kind, never maintained
separately. The legacy denotation still uses the value assignment until the
sorted certificate migration is complete. -/
def NormalGraph.params (G : NormalGraph ι) (i : ι) : Bool :=
  (G.parameterKinds i).isSome

/-- A clause row: neither a parameter nor a scheme. -/
def NormalGraph.plain (G : NormalGraph ι) (i : ι) : Bool := !G.params i && (G.schemes i).isNone

/-- A label's clauses. A parameter or scheme row has none: whatever `rows`
holds there is never read. -/
def NormalGraph.clauses (G : NormalGraph ι) (i : ι) : List (Clause (List ι)) :=
  if G.plain i then G.rows i else []

instance : CoeFun (NormalGraph ι) (fun _ => ι → List (Clause (List ι))) := ⟨NormalGraph.clauses⟩

/-- The sort of a type reference comes from its parameter or clause rows.
The empty union is bottom at either sort; a union cannot mix value and pack
rows. This checks only the outer sort, not recursive operand well-formedness. -/
def NormalGraph.hasKind (G : NormalGraph ι) (kind : ParameterKind) (S : List ι) : Bool :=
  S.all fun i => match G.parameterKinds i with
    | some k => k == kind
    | none => if (G.schemes i).isSome then kind == .value else
      (G.rows i).all fun c => match c with
        | .pack .. => kind == .arguments
        | _ => kind == .value

/-- A label with clauses is a clause row. -/
theorem NormalGraph.plain_of_clauses {G : NormalGraph ι} {i : ι} {c}
    (h : c ∈ G i) : G.plain i = true := by
  show G.plain i = true
  cases hp : G.plain i
  · simp [NormalGraph.clauses, hp] at h
  · rfl

/-- A graph of clause rows only. -/
def NormalGraph.ofRows (rows : ι → List (Clause (List ι))) : NormalGraph ι := { rows }

@[simp] theorem NormalGraph.ofRows_plain (rows : ι → List (Clause (List ι))) (i : ι) :
    (NormalGraph.ofRows rows).plain i = true := rfl

@[simp] theorem NormalGraph.ofRows_clauses (rows : ι → List (Clause (List ι))) (i : ι) :
    (NormalGraph.ofRows rows).clauses i = rows i := rfl

/-- Every label of a type is a clause row. -/
def NormalGraph.plainTy (G : NormalGraph ι) (S : List ι) : Bool := S.all G.plain

/-- A graph of clause rows only, at every label. -/
def NormalGraph.Plain (G : NormalGraph ι) : Prop := ∀ i, G.plain i = true

theorem NormalGraph.ofRows_Plain (rows : ι → List (Clause (List ι))) :
    (NormalGraph.ofRows rows).Plain := fun _ => rfl

@[simp] theorem NormalGraph.ofRows_plainTy (rows : ι → List (Clause (List ι))) (S : List ι) :
    (NormalGraph.ofRows rows).plainTy S = true := by
  simp [NormalGraph.plainTy]

def normalizeGraph (G : Graph ι) : NormalGraph ι := { rows := fun i => normalize (G i) }

def layer (G : Graph ι) (X : ι → Fam) (i : ι) : Fam := eval (setSem X) (G i)
def normalLayer (G : NormalGraph ι) (X : ι → Fam) (i : ι) : Fam := semList (setSem X) (G i)

theorem eval_congr (X Y : α → Fam) (n : Nat) (h : ∀ a, Agree (X a) (Y a) n)
    (f : Formula α) (W : WorldT n) (v : Val) : eval X f n W v ↔ eval Y f n W v := by
  induction f with
  | bot => rfl
  | atom c => exact sem_congr X Y n h c W v
  | union a b ih ih' => exact or_congr ih ih'
  | inter a b ih ih' => exact and_congr ih ih'

theorem eval_adm (X : α → Fam) (f : Formula α) : Adm (eval X f) := by
  induction f with
  | bot => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | atom c => exact sem_adm X c
  | union a b ih ih' => exact unionT_adm _ _ ih ih'
  | inter a b ih ih' => exact interT_adm _ _ ih ih'

theorem layer_congr (G : Graph ι) : LayerCongr (layer G) := by
  intro X Y n h i W v
  exact eval_congr _ _ n (fun a => setSem_congr n h a) (G i) W v

theorem layer_adm (G : Graph ι) : LayerAdm (layer G) := fun X _ i => eval_adm (setSem X) (G i)

/-- Equality of the entire guarded operators, not just an equation about one
nonrecursive example. -/
theorem normalized_layer (G : Graph ι) : normalLayer (normalizeGraph G) = layer G := by
  funext X i n W v
  exact propext (normalize_sound (setSem X) (G i) n W v)

def denote (G : Graph ι) : ι → Fam := Tower.denote (layer G)

/-! ## The denotation, at every assignment

The fixed point is over `(assignment, label)`: a scheme row reads its
signatures' rows at reassignments of its binders. -/

variable {k : ParameterSpace}

open Classical in
/-- The assignment with each binder given the family at its position. -/
noncomputable def assign (η : ParameterAssignment k ι) (bs : List ι) (As : List (ParameterFamily k)) :
    ParameterAssignment k ι :=
  ⟨fun i => match (bs.zip As).lookup i with
      | some A => A.1
      | none => η.1 i,
   fun i => by
      cases h : (bs.zip As).lookup i with
      | some A => simpa [h] using A.2
      | none => simpa [h] using η.2 i⟩

open Classical in
/-- A binder is given the family at its position. -/
theorem assign_map_mem (η : ParameterAssignment k ι) (bs : List ι) (F : ι → ParameterFamily k) {i : ι}
    (h : i ∈ bs) : (assign η bs (bs.map F)).1 i = (F i).1 := by
  have hl : (bs.zip (bs.map F)).lookup i = some (F i) := by
    induction bs with
    | nil => cases h
    | cons b bs ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
      by_cases hb : i = b
      · subst hb; simp
      · have hi : i ∈ bs := (List.mem_cons.mp h).resolve_left hb
        rw [beq_false_of_ne hb]; simp [ih hi]
  simp [assign, hl]

open Classical in
/-- Any other row keeps its family. -/
theorem assign_map_nmem (η : ParameterAssignment k ι) (bs : List ι) (F : ι → ParameterFamily k) {i : ι}
    (h : i ∉ bs) : (assign η bs (bs.map F)).1 i = η.1 i := by
  have hl : (bs.zip (bs.map F)).lookup i = none := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
      have hb : i ≠ b := fun e => h (e ▸ List.mem_cons_self)
      have hi : i ∉ bs := fun hi => h (List.mem_cons_of_mem _ hi)
      rw [beq_false_of_ne hb]; simp [ih hi]
  simp [assign, hl]

open Classical in
/-- A row that is no binder keeps its family, whatever the binders are given. -/
theorem assign_nmem (η : ParameterAssignment k ι) (bs : List ι) (As : List (ParameterFamily k)) {i : ι}
    (h : i ∉ bs) : (assign η bs As).1 i = η.1 i := by
  have hl : (bs.zip As).lookup i = none := by
    induction bs generalizing As with
    | nil => rfl
    | cons b bs ih =>
      cases As with
      | nil => rfl
      | cons A As =>
        simp only [List.zip_cons_cons, List.lookup_cons]
        have hb : i ≠ b := fun e => h (e ▸ List.mem_cons_self)
        rw [beq_false_of_ne hb]
        exact ih As fun hi => h (List.mem_cons_of_mem _ hi)
  simp [assign, hl]

open Classical in
private theorem lookup_zip_some {bs : List ι} {As : List (ParameterFamily k)} {p : ι}
    (h : p ∈ bs) (hl : As.length = bs.length) : ∃ A, (bs.zip As).lookup p = some A := by
  induction bs generalizing As with
  | nil => cases h
  | cons b bs ih =>
    cases As with
    | nil => simp at hl
    | cons A As =>
      simp only [List.zip_cons_cons, List.lookup_cons]
      by_cases hb : p = b
      · subst hb; simp
      · rw [beq_false_of_ne hb]
        exact ih ((List.mem_cons.mp h).resolve_left hb) (by simpa using hl)

open Classical in
private theorem mem_of_lookup_zip {bs : List ι} {As : List (ParameterFamily k)} {p : ι} {A}
    (h : (bs.zip As).lookup p = some A) : p ∈ bs := by
  induction bs generalizing As with
  | nil => simp at h
  | cons b bs ih =>
    cases As with
    | nil => simp at h
    | cons A' As =>
      simp only [List.zip_cons_cons, List.lookup_cons] at h
      by_cases hb : p = b
      · exact hb ▸ List.mem_cons_self
      · rw [beq_false_of_ne hb] at h
        exact List.mem_cons_of_mem _ (ih h)

open Classical in
/-- A binder is given the same family whatever the rest of the assignment. -/
theorem assign_mem_eq (η η' : ParameterAssignment k ι) (bs : List ι) (As : List (ParameterFamily k)) {p : ι}
    (h : p ∈ bs) (hl : As.length = bs.length) :
    (assign η bs As).1 p = (assign η' bs As).1 p := by
  obtain ⟨A, hA⟩ := lookup_zip_some h hl
  simp [assign, hA]

open Classical in
/-- Reassigning disjoint binders commutes. -/
theorem assign_comm (η : ParameterAssignment k ι) {bs cs : List ι} (As Bs : List (ParameterFamily k))
    (hd : ∀ p ∈ bs, p ∉ cs) :
    assign (assign η bs As) cs Bs = assign (assign η cs Bs) bs As := by
  apply Subtype.ext
  funext p
  show (match (cs.zip Bs).lookup p with
      | some B => B.1
      | none => match (bs.zip As).lookup p with | some A => A.1 | none => η.1 p) =
    (match (bs.zip As).lookup p with
      | some A => A.1
      | none => match (cs.zip Bs).lookup p with | some B => B.1 | none => η.1 p)
  cases hc : (cs.zip Bs).lookup p with
  | none => simp
  | some B =>
    have hp : p ∉ bs := fun hb => hd p hb (mem_of_lookup_zip hc)
    have hn : (bs.zip As).lookup p = none := by
      cases hb : (bs.zip As).lookup p with
      | none => rfl
      | some A => exact absurd (mem_of_lookup_zip hb) hp
    simp [hn]

open Classical in
theorem assign_cons_head (η : ParameterAssignment k ι) (b : ι) (bs : List ι) (A : ParameterFamily k)
    (As : List (ParameterFamily k)) : (assign η (b :: bs) (A :: As)).1 b = A.1 := by
  simp [assign, List.lookup_cons]

open Classical in
theorem assign_cons_ne (η : ParameterAssignment k ι) {b p : ι} (bs : List ι) (A : ParameterFamily k)
    (As : List (ParameterFamily k)) (h : p ≠ b) :
    (assign η (b :: bs) (A :: As)).1 p = (assign η bs As).1 p := by
  have : ((b :: bs).zip (A :: As)).lookup p = (bs.zip As).lookup p := by
    rw [List.zip_cons_cons, List.lookup_cons, beq_false_of_ne h]
  simp only [assign, this]

/-- Two assignments differing at most on `bs`. -/
def AgreeOff (bs : List ι) (η η' : ParameterAssignment k ι) : Prop := ∀ p, p ∉ bs → η.1 p = η'.1 p

open Classical in
theorem agreeOff_assign {bs : List ι} {η η' : ParameterAssignment k ι} (h : AgreeOff bs η η')
    (cs : List ι) (As : List (ParameterFamily k)) : AgreeOff bs (assign η cs As) (assign η' cs As) := by
  intro p hp
  simp only [assign]
  split <;> simp [h p hp]

/-- Argument contracts may read the current assignment directly, as well as
recursive value meanings. This keeps a pack parameter independent of the
value denotation of a graph row. -/
abbrev ArgumentInterpreter (ι : Type) (k : ParameterSpace := .value) :=
  ParameterAssignment k ι → (List ι → Fam) → List ι → ArgFam

def legacyArguments : ArgumentInterpreter ι := fun _ D S => packArgs (D S)

/-- Neither grouping arguments nor reading a pack assignment adds a guard.
Agreement must be preserved in both the assignment and recursive meanings. -/
def ArgumentNonExp {k : ParameterSpace} (P : ArgumentInterpreter ι k) : Prop :=
  ∀ η θ X Y n, (∀ p, Agree (η.1 p) (θ.1 p) n) →
    (∀ S, Agree (X S) (Y S) n) → ∀ S, Agree (P η X S) (P θ Y S) n

theorem legacyArguments_nonexp : ArgumentNonExp (legacyArguments (ι := ι)) :=
  fun _ _ _ _ _ _ h S => packArgs_congr (h S)

/-- Interpret argument rows from their shapes and parameter assignments.
Ordinary value rows and value parameters have no argument-list members.
Tuple positions use the recursive value meanings at the current level. -/
def graphArguments (G : NormalGraph ι) : ArgumentInterpreter ι .mixed :=
  fun η X S n W vs => ∃ i ∈ S,
    if G.parameterKinds i = some .arguments then η.1 i n W (.inr vs)
    else ∃ c ∈ G i, match c with
      | .pack a bs => ∀ t ∈ a :: bs, ArgumentContracts.Fits (tupleFams X t) n W vs
      | _ => False

/-- A pack parameter denotes its assigned list contract directly. -/
theorem graphArguments_parameter (G : NormalGraph ι) (η : MixedAssignment ι)
    (X : List ι → Fam) (i : ι) (h : G.parameterKinds i = some .arguments) :
    graphArguments G η X [i] = fun n W vs => η.1 i n W (.inr vs) := by
  funext n W vs
  apply propext
  simp [graphArguments, h]

/-- A tuple row denotes its shapes at the current level, with no encoded
value and no extra approximation delay. -/
theorem graphArguments_pack (G : NormalGraph ι) (η : MixedAssignment ι)
    (X : List ι → Fam) (i : ι) (a : Tuple (List ι)) (bs : List (Tuple (List ι)))
    (h : G i = [.pack a bs]) :
    graphArguments G η X [i] = fun n W vs =>
      ∀ t ∈ a :: bs, ArgumentContracts.Fits (tupleFams X t) n W vs := by
  have hp : G.parameterKinds i ≠ some .arguments := by
    intro hp
    have hplain := NormalGraph.plain_of_clauses (G := G) (i := i)
      (show Clause.pack a bs ∈ G i by rw [h]; simp)
    simp [NormalGraph.plain, NormalGraph.params, hp] at hplain
  funext n W vs
  apply propext
  simp [graphArguments, hp, h]

theorem graphArguments_nonexp (G : NormalGraph ι) : ArgumentNonExp (graphArguments G) := by
  intro η θ X Y n hη hX S j hj W vs
  unfold graphArguments
  apply exists_congr fun i => and_congr Iff.rfl ?_
  split
  · exact hη i j hj W (.inr vs)
  · apply exists_congr fun c => and_congr Iff.rfl ?_
    cases c <;> try exact Iff.rfl
    rename_i a bs
    exact forall_congr' fun t => forall_congr' fun _ =>
      arguments_congr X Y t j (fun a v => hX a j hj W v) vs

/-- Same-level argument interpretation preserves admissibility even for the
unrestricted approximations used to construct the recursive fixed point. -/
theorem graphArguments_adm (G : NormalGraph ι) (η : MixedAssignment ι)
    (X : List ι → Fam) (hX : ∀ S, Adm (X S)) (S : List ι) :
    Adm (graphArguments G η X S) := by
  have position : ∀ t i A, positionFam (tupleFams X t) i = some A → Adm A := by
    intro t i A h
    rw [positionFam_tupleFams] at h
    cases hp : t.position i <;> simp [hp] at h
    subst h
    exact hX _
  apply Adm.of_transfer
  intro n W vs h j hj U hx
  obtain ⟨i, hi, h⟩ := h
  refine ⟨i, hi, ?_⟩
  by_cases hp : G.parameterKinds i = some .arguments
  · simp only [hp, ite_true] at h ⊢
    exact (η.2 i).1.transfer h j hj U hx
  · simp only [hp, ite_false] at h ⊢
    obtain ⟨c, hc, h⟩ := h
    refine ⟨c, hc, ?_⟩
    cases c <;> try exact h.elim
    rename_i a bs
    intro t ht
    exact (ArgumentContracts.fits_adm (fun i A hA => position t i A hA)).transfer
      (h t ht) j hj U hx

/-- Argument rows produce admissible contracts on closed lists, so they may
serve as genuine pack substitutions rather than as ordinary value types. -/
theorem graphArguments_valid (G : NormalGraph ι) (η : MixedAssignment ι)
    (X : List ι → Fam) (hX : ∀ S, ValueFam (X S)) (S : List ι) :
    ParameterValid .arguments (graphArguments G η X S) := by
  have position : ∀ t i A, positionFam (tupleFams X t) i = some A → ValueFam A := by
    intro t i A h
    rw [positionFam_tupleFams] at h
    cases hp : t.position i <;> simp [hp] at h
    subst h
    exact hX _
  constructor
  · exact graphArguments_adm G η X (fun S => (hX S).1) S
  · intro n W vs h
    obtain ⟨i, hi, h⟩ := h
    by_cases hp : G.parameterKinds i = some .arguments
    · simp only [hp, ite_true] at h
      exact (η.2 i).2 n W (.inr vs) h
    · simp only [hp, ite_false] at h
      obtain ⟨c, hc, h⟩ := h
      cases c <;> try exact h.elim
      rename_i a bs
      exact ArgumentContracts.fits_bound
        (fun i A hA n W v hv => (position a i A hA).2 n W v hv)
        (h a List.mem_cons_self)

/-- One instance's signatures, their rows read at the reassignment. -/
noncomputable def instanceSigs (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι)
    (s : SchemeRow ι) (As : List (ParameterFamily k)) : List (Fam × List Fam × Fam) :=
  let η' := assign η s.binders As
  s.signatures.map fun p => (D η' p.1, p.2.1.map (D η'), D η' p.2.2)

/-- One instance's variadic signatures, their rows read at the reassignment. -/
noncomputable def instanceRestsWithArgs (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι)
    (s : SchemeRow ι) (As : List (ParameterFamily k))
    (P : ArgumentInterpreter ι k) : List (Fam × List Fam × ArgFam × Fam) :=
  let η' := assign η s.binders As
  s.variadic.map fun p => (D η' p.1, p.2.1.map (D η'), P η' (D η') p.2.2.1, D η' p.2.2.2)

/-- One instance's contract: its fixed and its variadic signatures, as a call
clause's are. -/
noncomputable def instanceTWithArgs (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι)
    (s : SchemeRow ι) (As : List (ParameterFamily k))
    (P : ArgumentInterpreter ι k) : Fam :=
  interT (callsT (instanceSigs D η s As)) (restsT (instanceRestsWithArgs D η s As (P := P)))

theorem instanceTWithArgs_adm (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (As : List (ParameterFamily k)) (P : ArgumentInterpreter ι k) :
    Adm (instanceTWithArgs D η s As (P := P)) :=
  interT_adm _ _ (callsT_adm _) (restsT_adm _)

/-- The legacy graph entry point delegates to the shared interpretation. -/
noncomputable def instanceT (D : Assignment ι → List ι → Fam) (η : Assignment ι)
    (s : SchemeRow ι) (As : List ValueFamily) : Fam :=
  instanceTWithArgs D η s As legacyArguments

private theorem argsAgree_of {X Y : List ι → Fam} {m : Nat} (h : ∀ S, Agree (X S) (Y S) m) :
    ∀ Ss : List (List ι), ArgsAgree m (Ss.map X) (Ss.map Y)
  | [] => .nil
  | S :: Ss => .cons (h S) (argsAgree_of h Ss)

/-- Instances whose rows agree below `m` have contracts agreeing there. -/
theorem instanceT_congrWithArgs (P : ArgumentInterpreter ι k) (hP : ArgumentNonExp P) {D D' : ParameterAssignment k ι → List ι → Fam} {η η' : ParameterAssignment k ι}
    {s : SchemeRow ι} {As As' : List (ParameterFamily k)} {m : Nat}
    (hη : ∀ p, Agree ((assign η s.binders As).1 p) ((assign η' s.binders As').1 p) m)
    (h : ∀ S, Agree (D (assign η s.binders As) S) (D' (assign η' s.binders As') S) m)
    (W : WorldT m) (v : Val) :
    instanceTWithArgs D η s As (P := P) m W v ↔ instanceTWithArgs D' η' s As' (P := P) m W v := by
  unfold instanceTWithArgs instanceSigs instanceRestsWithArgs interT
  exact and_congr
    (callsT_congr s.signatures _ _ (fun p _ => ⟨h p.1, argsAgree_of h p.2.1, h p.2.2⟩) W v)
    (restsT_congr s.variadic _ _ (fun p _ => ⟨h p.1, argsAgree_of h p.2.1, hP _ _ _ _ m hη h p.2.2.1, h p.2.2.2⟩) W v)

/-- An instance is bounded below `n`: each bounded binder's family lies below
its bound at every level under `n`. Only levels below `n` are read, which keeps
the fixed point contractive. -/
def Bounded (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier) (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (As : List (ParameterFamily k)) (n : Nat) : Prop :=
  ∀ b ∈ s.bounds, b.1 ∈ s.binders → ∀ j, j < n → ∀ (U : WorldT j) u,
    (assign η s.binders As).1 b.1 j U u → D η b.2 j U u

/-- Universal quantification has one implementation for both semantic sorts.
The body still denotes a runtime callable; its parameters may denote lists. -/
noncomputable def boundedSem
    (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier)
    (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (body : List (ParameterFamily k) → Fam) : Fam := fun n W v =>
  Invocable v ∧ ∀ As, As.length = s.binders.length →
    Bounded D η s As n → body As n W v

/-- The assignment carrier is independent of recursive value outputs. A domain
projects parameter values and derives bounds from those outputs at the same
level. These laws are precisely what the shared guarded fixed point needs. -/
structure ParameterInterpretation (ι : Type) (k : ParameterSpace) where
  arguments : ArgumentInterpreter ι k
  arguments_nonexp : ArgumentNonExp arguments
  value : ι → WorldFamily k.Carrier → Fam
  value_adm : ∀ i A, Adm A → Adm (value i A)
  value_congr : ∀ i A B n, Agree A B n → Agree (value i A) (value i B) n
  bound : ParameterAssignment k ι → (List ι → Fam) → List ι → WorldFamily k.Carrier
  bound_adm : ∀ η X, (∀ S, Adm (X S)) → ∀ S, Adm (bound η X S)
  bound_congr : ∀ η θ X Y n, (∀ p, Agree (η.1 p) (θ.1 p) n) →
    (∀ S, Agree (X S) (Y S) n) → ∀ S, Agree (bound η X S) (bound θ Y S) n

/-- The old value-only interpretation is an instance of the shared machinery. -/
def legacyParameters : ParameterInterpretation ι .value where
  arguments := legacyArguments
  arguments_nonexp := legacyArguments_nonexp
  value := fun _ A => A
  value_adm := fun _ _ h => h
  value_congr := fun _ _ _ _ h => h
  bound := fun _ X S => X S
  bound_adm := fun _ _ h S => h S
  bound_congr := fun _ _ _ _ _ _ h S => h S

/-- Mixed bounds retain both components. Projecting only their value part would
make a pack bound vacuous. Argument rows are derived, never unfolded again. -/
def mixedParameters (G : NormalGraph ι) : ParameterInterpretation ι .mixed where
  arguments := graphArguments G
  arguments_nonexp := graphArguments_nonexp G
  value := fun i A n W v => G.parameterKinds i = some .value ∧ A n W (.inl v)
  value_adm := fun _ A h =>
    ⟨fun n W v hv => ⟨hv.1, h.down n W (.inl v) hv.2⟩,
     fun n W U hx v hv => ⟨hv.1, h.mono n W U hx (.inl v) hv.2⟩⟩
  value_congr := fun _ _ _ _ h j hj W v => and_congr Iff.rfl (h j hj W (.inl v))
  bound := fun η X S n W x => match x with
    | .inl v => X S n W v
    | .inr vs => graphArguments G η X S n W vs
  bound_adm := by
    intro η X h S
    have ha := graphArguments_adm G η X h S
    constructor
    · intro n W x hx
      cases x with
      | inl v => exact (h S).down n W v hx
      | inr vs => exact ha.down n W vs hx
    · intro n W U hw x hx
      cases x with
      | inl v => exact (h S).mono n W U hw v hx
      | inr vs => exact ha.mono n W U hw vs hx
  bound_congr := by
    intro η θ X Y n hη hX S j hj W x
    cases x with
    | inl v => exact hX S j hj W v
    | inr vs => exact graphArguments_nonexp G η θ X Y n hη hX S j hj W vs

/-- **A scheme row.** A callable meeting its signatures at every instantiation
of its binders within their bounds: the same value, in the same world, at all
of them. -/
noncomputable def schemeSemWithArgs (I : ParameterInterpretation ι k) (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι)
    (s : SchemeRow ι) : Fam :=
  boundedSem (fun θ S => I.bound θ (D θ) S) η s (fun As => instanceTWithArgs D η s As I.arguments)

noncomputable def schemeSem (D : Assignment ι → List ι → Fam) (η : Assignment ι)
    (s : SchemeRow ι) : Fam := schemeSemWithArgs legacyParameters D η s

/-- One step of the assignment-indexed denotation. -/
noncomputable def qLayerWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k) (X : ParameterAssignment k ι × ι → Fam) :
    ParameterAssignment k ι × ι → Fam := fun ηi =>
  if G.params ηi.2 then I.value ηi.2 (ηi.1.1 ηi.2) else
  match G.schemes ηi.2 with
  | some s => schemeSemWithArgs I (fun η' S => setSem (fun l => X (η', l)) S) ηi.1 s
  | none => setSem (semWithArgs (setSem fun l => X (ηi.1, l))
      (I.arguments ηi.1 (setSem fun l => X (ηi.1, l)))) (G ηi.2)

noncomputable def qLayer (G : NormalGraph ι) (X : Assignment ι × ι → Fam) :
    Assignment ι × ι → Fam := qLayerWithArgs G legacyParameters X

theorem normalLayer_congr (G : NormalGraph ι) : LayerCongr (normalLayer G) := by
  intro X Y n h i W v
  constructor <;> rintro ⟨c, hc, hv⟩ <;> refine ⟨c, hc, ?_⟩
  · exact (sem_congr _ _ n (fun a => setSem_congr n h a) c W v).mp hv
  · exact (sem_congr _ _ n (fun a => setSem_congr n h a) c W v).mpr hv

theorem Agree.mono {A B : WorldFamily α} {n m : Nat} (h : Agree A B n) (hm : m ≤ n) : Agree A B m :=
  fun k hk W v => h k (by omega) W v

theorem argsAgree_mono {As Bs : List Fam} {n m : Nat} (h : ArgsAgree n As Bs) (hm : m ≤ n) :
    ArgsAgree m As Bs := by
  induction h with
  | nil => exact .nil
  | cons hA _ ih => exact .cons (Agree.mono hA hm) ih

theorem qLayer_congrWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    : LayerCongr (fun X => qLayerWithArgs G I X) := by
  intro X Y n h ηi W v
  obtain ⟨η, i⟩ := ηi
  unfold qLayerWithArgs
  by_cases hp : G.params i = true
  · simp [hp]
  · simp only [hp]
    cases hq : G.schemes i with
    | none =>
      have hS := fun S => setSem_congr n (fun l => h (η, l)) S
      constructor <;> rintro ⟨c, hc, hv⟩ <;> refine ⟨c, hc, ?_⟩
      · exact (semWithArgs_congr _ _ _ _ n hS (I.arguments_nonexp η η _ _ n (fun _ _ _ _ _ => Iff.rfl) hS) c W v).mp hv
      · exact (semWithArgs_congr _ _ _ _ n hS (I.arguments_nonexp η η _ _ n (fun _ _ _ _ _ => Iff.rfl) hS) c W v).mpr hv
    | some s =>
      refine and_congr Iff.rfl (forall_congr' fun As => forall_congr' fun _ => ?_)
      refine imp_congr ?_ ?_
      · unfold Bounded
        refine forall_congr' fun b => forall_congr' fun _ => forall_congr' fun _ =>
          forall_congr' fun j => forall_congr' fun hj => forall_congr' fun U =>
          forall_congr' fun u => imp_congr Iff.rfl ?_
        exact I.bound_congr _ _ _ _ n (fun _ _ _ _ _ => Iff.rfl)
          (fun S => setSem_congr n (fun l => h (_, l)) S) b.2 j hj U u
      · exact instanceT_congrWithArgs I.arguments I.arguments_nonexp (fun _ _ _ _ _ => Iff.rfl) (fun S => setSem_congr n (fun l => h (_, l)) S) W v

/-! ### Non-expansiveness in the assignment

A bounded scheme's admissibility needs more than each step's: an instance
bounded only below a level is replaced by one bounded everywhere, which agrees
with it below that level, so the families read at the two instances must agree
below it too. Every approximation of the fixed point has that property. -/

/-- Assignments agreeing below `m` give families agreeing below `m`. -/
def NonExp (X : ParameterAssignment k ι × ι → Fam) : Prop :=
  ∀ (η η' : ParameterAssignment k ι) (i : ι) (m : Nat), (∀ p, Agree (η.1 p) (η'.1 p) m) →
    Agree (X (η, i)) (X (η', i)) m

/-- The invariant of the approximations: admissible and non-expansive. -/
def QInv (X : ParameterAssignment k ι × ι → Fam) : Prop := (∀ ηi, Adm (X ηi)) ∧ NonExp X

open Classical in
/-- An instance with each binder's family cut down to its bounds. -/
noncomputable def restrictArgs (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier) (η : ParameterAssignment k ι)
    (bounds : List (ι × List ι)) (hD : ∀ S, Adm (D η S)) :
    List ι → List (ParameterFamily k) → List (ParameterFamily k)
  | b :: bs, A :: As =>
    ⟨fun n W v => A.1 n W v ∧ ∀ B, (b, B) ∈ bounds → D η B n W v,
     ⟨⟨fun n W v h => ⟨A.2.1.down n W v h.1, fun B hB => (hD B).down n W v (h.2 B hB)⟩,
       fun n W W' hx v h => ⟨A.2.1.mono n W W' hx v h.1,
         fun B hB => (hD B).mono n W W' hx v (h.2 B hB)⟩⟩,
      fun n W v h => A.2.2 n W v h.1⟩⟩ :: restrictArgs D η bounds hD bs As
  | _, _ => []

theorem restrictArgs_length (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier) (η : ParameterAssignment k ι)
    (bounds : List (ι × List ι)) (hD : ∀ S, Adm (D η S)) :
    ∀ (bs : List ι) (As : List (ParameterFamily k)), As.length = bs.length →
      (restrictArgs D η bounds hD bs As).length = bs.length
  | [], _, _ => by simp [restrictArgs]
  | _ :: _, [], h => by simp at h
  | b :: bs, A :: As, h => by
    simp only [restrictArgs, List.length_cons]
    rw [restrictArgs_length D η bounds hD bs As (by simpa using h)]

/-- A restricted binder's family is its family within its bounds. -/
theorem assign_restrict (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier) (η' η : ParameterAssignment k ι)
    (bounds : List (ι × List ι)) (hD : ∀ S, Adm (D η S)) :
    ∀ (bs : List ι) (As : List (ParameterFamily k)) (p : ι) (n : Nat) (W : WorldT n) (v : k.Carrier),
      As.length = bs.length →
      ((assign η' bs (restrictArgs D η bounds hD bs As)).1 p n W v ↔
        (assign η' bs As).1 p n W v ∧ (p ∈ bs → ∀ B, (p, B) ∈ bounds → D η B n W v))
  | [], As, p, n, W, v, _ => by simp [restrictArgs, assign]
  | _ :: _, [], _, _, _, _, h => by simp at h
  | b :: bs, A :: As, p, n, W, v, h => by
    by_cases hb : p = b
    · subst hb
      simp only [restrictArgs]
      rw [assign_cons_head, assign_cons_head]
      simp
    · simp only [restrictArgs]
      rw [assign_cons_ne _ _ _ _ hb, assign_cons_ne _ _ _ _ hb,
        assign_restrict D η' η bounds hD bs As p n W v (by simpa using h)]
      simp [hb]

/-- Restricting each instance to its bounds makes universal quantification
admissible. The argument applies equally to value and list contracts; it does
not add an approximation delay to list membership. -/
theorem boundedSem_adm
    (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier)
    (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (body : List (ParameterFamily k) → Fam)
    (hD : ∀ S, Adm (D η S)) (hbody : ∀ As, Adm (body As))
    (hcongr : ∀ As Bs m,
      (∀ p, Agree ((assign η s.binders As).1 p) ((assign η s.binders Bs).1 p) m) →
      ∀ W v, body As m W v ↔ body Bs m W v) :
    Adm (boundedSem D η s body) := by
  constructor
  · intro n W v h
    refine ⟨h.1, fun As hl hb => ?_⟩
    let As' := restrictArgs D η s.bounds hD s.binders As
    have hl' : As'.length = s.binders.length := restrictArgs_length _ _ _ _ _ _ hl
    have hb' : Bounded D η s As' (n + 1) := by
      intro b hbm hbin j _ U u hu
      exact ((assign_restrict _ η η _ hD _ _ _ _ _ _ hl).mp hu).2 hbin b.2 hbm
    have hagree : ∀ p, Agree ((assign η s.binders As').1 p) ((assign η s.binders As).1 p) n := by
      intro p j hj U u
      rw [assign_restrict _ η η _ hD _ _ _ _ _ _ hl]
      constructor
      · exact fun h => h.1
      · intro hu
        exact ⟨hu, fun hps B hB => hb (p, B) hB hps j hj U u hu⟩
    exact (hcongr As' As n hagree _ v).mp ((hbody As').down n W v (h.2 As' hl' hb'))
  · intro n W W' hx v h
    exact ⟨h.1, fun As hl hb => (hbody As).mono n W W' hx v (h.2 As hl hb)⟩

theorem qLayer_invWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (X : ParameterAssignment k ι × ι → Fam) (hX : QInv X) :
    QInv (qLayerWithArgs G I X) := by
  obtain ⟨hadm, hne⟩ := hX
  have hD : ∀ (η : ParameterAssignment k ι) S, Adm (setSem (fun l => X (η, l)) S) :=
    fun η S => setSem_adm (fun l => hadm (η, l)) S
  -- Families read at assignments agreeing below `m` agree below `m`.
  have sets : ∀ (η η' : ParameterAssignment k ι) m, (∀ p, Agree (η.1 p) (η'.1 p) m) → ∀ S,
      Agree (setSem (fun l => X (η, l)) S) (setSem (fun l => X (η', l)) S) m :=
    fun η η' m h S => setSem_congr m (fun l => hne η η' l m h) S
  -- Reassigning the same binders keeps agreement.
  have reassign : ∀ (η η' : ParameterAssignment k ι) (bs : List ι) (As : List (ParameterFamily k)) m,
      (∀ p, Agree (η.1 p) (η'.1 p) m) →
      ∀ p, Agree ((assign η bs As).1 p) ((assign η' bs As).1 p) m := by
    intro η η' bs As m h p
    classical
    simp only [assign]
    split
    · exact fun j _ W v => Iff.rfl
    · exact h p
  refine ⟨fun ηi => ?_, fun η η' i m h => ?_⟩
  · -- admissible
    obtain ⟨η, i⟩ := ηi
    unfold qLayerWithArgs
    by_cases hp : G.params i = true
    · simpa [hp] using I.value_adm i (η.1 i) (η.2 i).1
    · simp only [hp]
      cases hq : G.schemes i with
      | none => exact setSem_adm (fun c => semWithArgs_adm _ _ c) (G i)
      | some s =>
        exact boundedSem_adm _ η s _ (I.bound_adm η _ (hD η))
          (fun As => instanceTWithArgs_adm _ η s As I.arguments)
          (fun As Bs m h W v => instanceT_congrWithArgs I.arguments I.arguments_nonexp h (fun S => sets _ _ m h S) W v)
  · -- non-expansive
    intro k hk W v
    unfold qLayerWithArgs
    by_cases hp : G.params i = true
    · simp only [hp, if_true]; exact I.value_congr i _ _ m (h i) k hk W v
    · simp only [hp]
      cases hq : G.schemes i with
      | none =>
        constructor
        · rintro ⟨c, hc, hv⟩
          exact ⟨c, hc, (semWithArgs_congr _ _ _ _ k
            (fun a => Agree.mono (sets η η' m h a) (by omega))
            (I.arguments_nonexp η η' _ _ k (fun p => Agree.mono (h p) (by omega)) (fun a => Agree.mono (sets η η' m h a) (by omega))) c W v).mp hv⟩
        · rintro ⟨c, hc, hv⟩
          exact ⟨c, hc, (semWithArgs_congr _ _ _ _ k
            (fun a => Agree.mono (sets η η' m h a) (by omega))
            (I.arguments_nonexp η η' _ _ k (fun p => Agree.mono (h p) (by omega)) (fun a => Agree.mono (sets η η' m h a) (by omega))) c W v).mpr hv⟩
      | some s =>
        refine and_congr Iff.rfl (forall_congr' fun As => forall_congr' fun _ => ?_)
        have hre := reassign η η' s.binders As m h
        refine imp_congr ?_ ?_
        · unfold Bounded
          refine forall_congr' fun b => forall_congr' fun _ => forall_congr' fun _ =>
            forall_congr' fun j => forall_congr' fun hj => forall_congr' fun U =>
            forall_congr' fun u => imp_congr (hre b.1 j (by omega) U u)
              (I.bound_congr η η' _ _ m h (sets η η' m h) b.2 j (by omega) U u)
        · exact instanceT_congrWithArgs I.arguments I.arguments_nonexp (fun p => Agree.mono (hre p) (by omega)) (fun S => Agree.mono (sets _ _ m hre S) (by omega)) W v

/-- One assignment-indexed fixed point for both value and argument
interpretations. The latter's agreement law supplies no extra delay. -/
noncomputable def qDenoteWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k) :
    ParameterAssignment k ι × ι → Fam := Tower.denote (fun X => qLayerWithArgs G I X)

theorem qDenoteWithArgs_unfold (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (ηi : ParameterAssignment k ι × ι) (n : Nat) (W : WorldT n) (v : Val) :
    qDenoteWithArgs G I ηi n W v ↔ qLayerWithArgs G I (qDenoteWithArgs G I) ηi n W v :=
  Tower.denote_unfold (qLayer_congrWithArgs G I) ηi n W v

theorem qDenoteWithArgs_adm (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (ηi : ParameterAssignment k ι × ι) : Adm (qDenoteWithArgs G I ηi) :=
  Tower.denote_adm_inv (qLayer_congrWithArgs G I) QInv
    ⟨fun _ => topF_adm, fun _ _ _ _ _ _ _ _ _ => Iff.rfl⟩
    (qLayer_invWithArgs G I) (fun _ h => h.1) ηi

/-- Changing an assignment only above a level cannot change a recursive
signature below it, including the signature's rest contract. -/
theorem qDenoteWithArgs_nonexp (G : NormalGraph ι) (I : ParameterInterpretation ι k) :
    NonExp (qDenoteWithArgs G I) := by
  intro η η' i m h k hk W v
  exact (Tower.approx_inv QInv
    ⟨fun _ => topF_adm, fun _ _ _ _ _ _ _ _ _ => Iff.rfl⟩
    (qLayer_invWithArgs G I) (k + 1)).2 η η' i m h k hk W v

/-- The production interpretation remains the legacy argument adapter until
sorted substitution and the certificate protocol migrate together. -/
noncomputable def qDenote (G : NormalGraph ι) : Assignment ι × ι → Fam :=
  qDenoteWithArgs G legacyParameters

theorem qDenote_unfold (G : NormalGraph ι) (ηi : Assignment ι × ι)
    (n : Nat) (W : WorldT n) (v : Val) :
    qDenote G ηi n W v ↔ qLayer G (qDenote G) ηi n W v :=
  qDenoteWithArgs_unfold G legacyParameters ηi n W v

theorem qDenote_adm (G : NormalGraph ι) (ηi : Assignment ι × ι) : Adm (qDenote G ηi) :=
  qDenoteWithArgs_adm G legacyParameters ηi

/-- A label list's meaning at an assignment. -/
noncomputable def qMeaning (G : NormalGraph ι) (η : Assignment ι) (S : List ι) : Fam :=
  setSem (fun l => qDenote G (η, l)) S

/-- A label's meaning, at the graph's own assignment. -/
noncomputable def normalDenote (G : NormalGraph ι) (i : ι) : Fam := qDenote G (G.env, i)

theorem normalDenote_adm (G : NormalGraph ι) (i : ι) : Adm (normalDenote G i) :=
  qDenote_adm G _

/-- A clause row means its clauses. -/
theorem unfold_plain {G : NormalGraph ι} {i : ι} (hi : G.plain i = true) (n W v) :
    normalDenote G i n W v ↔ semList (setSem (normalDenote G)) (G i) n W v := by
  simp only [NormalGraph.plain, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hi
  unfold normalDenote
  rw [qDenote_unfold]
  simp only [qLayer, qLayerWithArgs, hi.1, hi.2, Bool.false_eq_true, ite_false]
  rfl

/-- Every label means closed values only, whatever its kind. -/
theorem normalDenote_value {G : NormalGraph ι} {i : ι} {n W v}
    (h : normalDenote G i n W v) : isVal v = true ∧ Scoped 0 v := by
  unfold normalDenote at h
  rw [qDenote_unfold] at h
  unfold qLayer qLayerWithArgs at h
  by_cases hp : G.params i = true
  · simp only [hp, ite_true] at h
    exact (G.env.2 i).2 n W v h
  · simp only [hp] at h
    cases hq : G.schemes i with
    | some s =>
      simp only [hq] at h
      exact ⟨h.1.val, h.1.scoped⟩
    | none =>
      simp only [hq, normalLayer, semList] at h
      obtain ⟨c, -, hc⟩ := h
      exact sem_value hc

private theorem approx_plain (G : NormalGraph ι) (hG : G.Plain) (η : Assignment ι) :
    ∀ k, (fun i => Tower.approx (qLayer G) k (η, i)) = Tower.approx (normalLayer G) k
  | 0 => rfl
  | k + 1 => by
    funext i
    have ih := approx_plain G hG η k
    have hi := hG i
    simp only [NormalGraph.plain, Bool.and_eq_true, Bool.not_eq_true',
      Option.isNone_iff_eq_none] at hi
    show qLayer G (Tower.approx (qLayer G) k) (η, i) =
      normalLayer G (Tower.approx (normalLayer G) k) i
    rw [← ih]
    simp only [qLayer, qLayerWithArgs, hi.1, hi.2, Bool.false_eq_true, ite_false]
    rfl

/-- **Conservative.** A graph of clause rows means what its guarded fixed
point over clauses means. -/
theorem normalDenote_plain (G : NormalGraph ι) (hG : G.Plain) :
    normalDenote G = Tower.denote (normalLayer G) := by
  funext i n
  show Tower.approx (qLayer G) (n + 1) (G.env, i) n = Tower.approx (normalLayer G) (n + 1) i n
  rw [← approx_plain G hG G.env (n + 1)]

theorem normalizeGraph_plain (G : Graph ι) : (normalizeGraph G).Plain := fun _ => rfl

theorem normalize_recursive (G : Graph ι) : normalDenote (normalizeGraph G) = denote G := by
  rw [normalDenote_plain _ (normalizeGraph_plain G)]
  unfold denote
  rw [normalized_layer]

theorem unfolds (G : Graph ι) (i : ι) (n W v) :
    denote G i n W v ↔ layer G (denote G) i n W v :=
  Tower.denote_unfold (layer_congr G) i n W v

theorem admissible (G : Graph ι) (i : ι) : Adm (denote G i) :=
  Tower.denote_adm (layer_congr G) (layer_adm G) i

/-- Any sound check on normalized denotations transports to the original graph.
This is a normalization interface, not an assumption that the old subtype
checker already accepts the new reference-conjunction representation. -/
theorem transport_inclusion (G : Graph ι) (S T : List ι)
    (h : FamLe (setSem (normalDenote (normalizeGraph G)) S)
      (setSem (normalDenote (normalizeGraph G)) T)) :
    FamLe (setSem (denote G) S) (setSem (denote G) T) := by
  simpa only [normalize_recursive] using h

#print axioms graphArguments_valid
#print axioms boundedSem_adm
#print axioms qDenoteWithArgs_unfold
#print axioms qDenoteWithArgs_adm
#print axioms qDenoteWithArgs_nonexp
#print axioms normalize_recursive
#print axioms admissible
end Verification.Model.PositiveGraphs
