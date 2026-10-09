import Verification.Types.PositiveNormalization

/-! Normalize each body of a guarded recursive graph without unfolding cycles
or allocating new labels. A label names a whole positive formula; normalized
labels name finite unions of clauses. Operands remain lists of labels. -/
namespace Verification.PositiveGraphs
open CallEffects
open PositiveNormalization Tower

/-! ## Rows of a normal graph

A label's row is one of four kinds. A clause row means a finite union of
clauses. A parameter row is a binder of some scheme and means what the graph's
assignment gives it. A scheme row is a generic callable, such as `Promise<T>`'s
`then<R1, R2>`: a value meeting its signatures at every instantiation of its
binders. A meet row is a value parameter row intersected with clauses, such as
`V & DepSafe`: what the assignment gives the parameter, within the clauses.

The assignment is part of the graph. No check reads it; it enters only the
semantics. A theorem proved for every graph therefore holds at every
assignment, which is what typing a generic body once, for all of its
instances, needs. -/

/-- Semantic binders distinguish a runtime value from an argument list. -/
inductive ParameterKind where
  | value
  | arguments
  deriving DecidableEq, BEq, Repr, Inhabited

deriving instance ReflBEq for ParameterKind
deriving instance LawfulBEq for ParameterKind

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

/-- A binder observes only the component selected by its declared kind.
The other component of a mixed semantic family cannot constrain its meaning. -/
def selectParameter (kind : Option ParameterKind) (A : WorldFamily ParameterSpace.mixed.Carrier) :
    WorldFamily ParameterSpace.mixed.Carrier := fun n W x => match x with
  | .inl v => kind = some .value ∧ A n W (.inl v)
  | .inr vs => kind = some .arguments ∧ A n W (.inr vs)

theorem selectParameter_valid (kind : Option ParameterKind) {A : WorldFamily ParameterSpace.mixed.Carrier}
    (h : ParameterValid .mixed A) : ParameterValid .mixed (selectParameter kind A) := by
  constructor
  · constructor
    · intro n W x hx
      cases x <;> exact ⟨hx.1, h.1.down _ _ _ hx.2⟩
    · intro n W U hw x hx
      cases x <;> exact ⟨hx.1, h.1.mono _ _ _ hw _ hx.2⟩
  · intro n W x hx
    cases x <;> exact h.2 _ _ _ hx.2

@[simp] theorem selectParameter_idempotent (kind : Option ParameterKind)
    (A : WorldFamily ParameterSpace.mixed.Carrier) :
    selectParameter kind (selectParameter kind A) = selectParameter kind A := by
  funext n W x
  cases x <;> simp [selectParameter]

/-- Positions of a retained resolution input, literal observation and associated
result among a scheme's binders. Positions survive label renaming. -/
structure ResolutionSlots where
  input : Nat
  observation : Nat
  result : Nat
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A quantified callable: its binders, which are parameter rows, and the
signatures `(receiver, parameters, result)` each of its instances meets. -/
structure SchemeRow (ι : Type) where
  binders : List ι
  signatures : List (Arrow (List ι))
  /-- Upper bounds `(binder, type)`: an instance gives the binder a family below
  the type, read at the scheme's own assignment (a bound does not mention the
  scheme's binders). -/
  bounds : List (ι × List ι) := []
  /-- Variadic signatures `(receiver, parameters, rest, result)`, the rest an
  argument-list type; a binder may be one. -/
  variadic : List (RestArrow (List ι)) := []
  /-- Associated slots are part of the generic contract. -/
  resolution : List ResolutionSlots := []
  deriving DecidableEq, Repr

/-- Associated observation and result slots have no independent bounds.
Input bounds retain the associated contracts when narrowing a substitution. -/
def SchemeRow.protectedSlots (s : SchemeRow ι) : Prop :=
  ∀ g ∈ s.resolution, ∀ p ∈ [g.observation, g.result],
    ∀ b, s.binders[p]? = some b → ∀ B, (b, B) ∉ s.bounds

/-- Structural substitution retains the associated slot positions. -/
def SchemeRow.map (binding : ι → κ) (operand : List ι → List κ)
    (s : SchemeRow ι) : SchemeRow κ where
  binders := s.binders.map binding
  signatures := s.signatures.map (Arrow.map operand)
  bounds := s.bounds.map (fun b => (binding b.1, operand b.2))
  variadic := s.variadic.map (RestArrow.map operand)
  resolution := s.resolution

/-- The finite graph boundary checks position identity and all protected
bounds separately from semantic instance membership. -/
@[nospecialize] def SchemeRow.resolutionValid [DecidableEq ι] (s : SchemeRow ι) : Bool :=
  s.resolution.isEmpty ||
    (decide s.binders.Nodup &&
      decide (s.resolution.flatMap (fun g => [g.input, g.observation, g.result])).Nodup &&
      s.resolution.all (fun g =>
        g.input < s.binders.length && g.observation < s.binders.length && g.result < s.binders.length &&
        s.bounds.all (fun b => s.binders[g.observation]? != some b.1 && s.binders[g.result]? != some b.1)))

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

/-- An instance is bounded below `n`: each bounded binder's family lies below
its bound at every level under `n`. Only levels below `n` are read, which keeps
the fixed point contractive. -/
def Bounded (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier) (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (As : List (ParameterFamily k)) (n : Nat) : Prop :=
  ∀ b ∈ s.bounds, b.1 ∈ s.binders → ∀ j, j < n → ∀ (U : WorldT j) u,
    (assign η s.binders As).1 b.1 j U u → D η b.2 j U u

/-- A fixed universe of allowed substitutions. The universe reads no recursive
graph approximation or ambient assignment. -/
structure SchemeDomain (ι : Type) (k : ParameterSpace) where
  allowed : SchemeRow ι → List (ParameterFamily k) → Prop
  /-- Every unqualified row admits its ordinary substitutions. -/
  ordinary_allowed : ∀ s As, s.resolution = [] → allowed s As
  /-- Renaming labels preserves the positional qualification contract. -/
  congr : ∀ s t, s.resolution = t.resolution →
    (s.protectedSlots ↔ t.protectedSlots) → ∀ As, allowed s As ↔ allowed t As
/-- Ordinary quantification permits ordinary rows. A qualified row requires an
explicit domain whose substitutions retain its associated contracts. -/
def SchemeDomain.ordinary : SchemeDomain ι k where
  allowed s _ := s.resolution = []
  ordinary_allowed _ _ h := h
  congr s t h _ As := by rw [h]

/-- What the realm's arrays are, as a graph states it: the type of
`Array.prototype` (`ArrayProto`) and the keys that prototype provides, none
of which an array owns. It is what the array invariant (`arrayInvariant`)
reads. -/
structure ArrayRealm (ι : Type) where
  proto : List ι
  keys : List PropKey
  deriving DecidableEq, Repr

structure NormalGraph (ι : Type) where
  /-- A clause row's clauses. -/
  rows : ι → List (Clause (List ι))
  schemes : ι → Option (SchemeRow ι) := fun _ => none
  parameterKinds : ι → Option ParameterKind := fun _ => none
  /-- A meet row's value parameter row and the clauses it is intersected with
  (`V & DepSafe`). -/
  meets : ι → Option (ι × List (Clause (List ι))) := fun _ => none
  /-- A meet row's further value parameter rows: its value is what the
  assignment gives each of them as well (`U ⊓ T` for `U extends T`, `T & U`). -/
  meetParams : ι → List ι := fun _ => []
  /-- What the parameter rows mean. Semantic only. -/
  env : MixedAssignment ι := ParameterAssignment.empty .mixed
  /-- The reviewed substitution universe is fixed across the graph's tower. -/
  domain : SchemeDomain ι .mixed := .ordinary
  /-- The realm's arrays, where the graph states them: then every record and
  dictionary type is of objects meeting the array invariant
  (`realmInvariant`). A graph without arrays states none. -/
  realm : Option (ArrayRealm ι) := none

/-- Whether a row is a parameter is derived from its kind, never maintained
separately. -/
def NormalGraph.params (G : NormalGraph ι) (i : ι) : Bool :=
  (G.parameterKinds i).isSome

/-- A clause row: neither a parameter, a scheme nor a meet. -/
def NormalGraph.plain (G : NormalGraph ι) (i : ι) : Bool :=
  !G.params i && (G.schemes i).isNone && (G.meets i).isNone

/-- A clause row's three conditions. -/
theorem NormalGraph.plain_iff {G : NormalGraph ι} {i : ι} :
    G.plain i = true ↔ G.params i = false ∧ G.schemes i = none ∧ G.meets i = none := by
  simp [NormalGraph.plain, and_assoc]

/-- A label's clauses. A parameter, scheme or meet row has none: whatever
`rows` holds there is never read. -/
def NormalGraph.clauses (G : NormalGraph ι) (i : ι) : List (Clause (List ι)) :=
  if G.plain i then G.rows i else []

instance : CoeFun (NormalGraph ι) (fun _ => ι → List (Clause (List ι))) := ⟨NormalGraph.clauses⟩

/-- The sort of a type reference comes from its parameter or clause rows.
The empty union is bottom at either sort; a union cannot mix value and pack
rows. This checks only the outer sort, not recursive operand well-formedness. -/
def NormalGraph.hasKind (G : NormalGraph ι) (kind : ParameterKind) (S : List ι) : Bool :=
  S.all fun i => match G.parameterKinds i with
    | some k => k == kind
    | none => if (G.schemes i).isSome || (G.meets i).isSome then kind == .value else
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

/-- A graph of positive formulas, before normalization. -/
abbrev Graph (ι : Type) := ι → Formula (List ι)

/-- Normalize each body without unfolding cycles or allocating labels. -/
def normalizeGraph (G : Graph ι) : NormalGraph ι := { rows := fun i => normalize (G i) }

theorem normalizeGraph_plain (G : Graph ι) : (normalizeGraph G).Plain := fun _ => rfl

/-- A graph without parameter rows reads argument lists from its clauses: a
pack clause's tuple contracts, at the current level. -/
def plainArguments (G : NormalGraph ι) (X : List ι → Fam) (S : List ι) : ArgFam :=
  fun n W vs => ∃ i ∈ S, ∃ c ∈ G i, clauseArguments X c n W vs

/-! ## The array invariant

An object owning the array store key is an array of the realm: its store may have holes, it holds `Array.prototype` under the prototype key, and it owns no key
that prototype provides. Every array a program allocates is one; every object
it receives at a record or dictionary type is assumed to be one (the
environment premise, through `meaning`). The store key is a key no source
spells and no step adds, so the invariant is a fact of the object's identity:
it reads the world's contracts only, never the heap. -/

/-- The store every array holds, read at the weakest element type: a possibly sparse
store of values. -/
def anyStoreT : Fam := listT ⟨[], [], some topT, true, .sparse⟩

/-- A store under any tuple contract of values is a store of values. -/
theorem listT_anyStore {T : TupleF}
    (hT : ∀ A, (A ∈ T.required ∨ A ∈ T.optional ∨ T.rest = some A) →
      ∀ j (W : WorldT j) u, A j W u → topT j W u)
    {k : Nat} {W : WorldT k} {v : Val} (h : listT T k W v) : anyStoreT k W v := by
  obtain ⟨ls, rfl, hd, hlen, hbound, hreq, hopt, hrest⟩ := h
  refine ⟨ls, rfl, (by simp [StorePresence]), by simp, by simp, by simp, by simp, ?_⟩
  intro i l _ hl
  refine ⟨topT, ?_⟩
  simp only [true_and]
  by_cases hi : i < T.required.length
  · obtain ⟨l', c, hl', hw, hag⟩ := hreq i (T.required[i]) (List.getElem?_eq_getElem hi)
    rw [hl] at hl'
    cases hl'
    exact ⟨c, hw, fun j hj W' u => ⟨fun hu => hT _ (.inl (List.getElem_mem hi)) j W' u
      ((hag j hj W' u).1 hu), fun h => nomatch h⟩⟩
  · by_cases ho : i < T.required.length + T.optional.length
    · have hoi : i - T.required.length < T.optional.length := by omega
      have hl2 : ls[T.required.length + (i - T.required.length)]? = some (some l) := by
        rw [show T.required.length + (i - T.required.length) = i by omega]; exact hl
      obtain ⟨c, hw, hag⟩ := hopt (i - T.required.length) (T.optional[i - T.required.length])
        l (List.getElem?_eq_getElem hoi) hl2
      exact ⟨c, hw, fun j hj W' u => ⟨fun hu => hT _ (.inr (.inl (List.getElem_mem hoi))) j W' u
        ((hag j hj W' u).1 hu), fun h => nomatch h⟩⟩
    · obtain ⟨E, c, hE, hw, hag⟩ := hrest i l (by omega) hl
      exact ⟨c, hw, fun j hj W' u => ⟨fun hu => hT _ (.inr (.inr hE)) j W' u
        ((hag j hj W' u).1 hu), fun h => nomatch h⟩⟩

/-- **The array invariant**, with `P` the prototype's type and `N` the keys it
provides. -/
def arrayInvariant (P : Fam) (N : List PropKey) : Fam := fun k W v =>
  ∀ flds oid, v = .objAt flds .absent oid → (flds.lookup CallArguments.arrayStoreField).isSome = true →
    viewT [(CallArguments.arrayStoreField, anyStoreT), (CallArguments.protoField, P)] k W v ∧
      ownKeysT ⟨false, N⟩ k W v

/-- What a row asks of the members of one of its clauses beyond the clause:
the array invariant, where the graph states the realm and the clause is a
record's. -/
def realmInvariant (G : NormalGraph ι) (X : List ι → Fam) (c : Clause (List ι)) : Fam :=
  match G.realm with
  | some r => if c.record then arrayInvariant (X r.proto) r.keys else fun _ _ _ => True
  | none => fun _ _ _ => True

/-- **A clause, read in a row**: its members that meet the realm's invariant.
The operands are read by `X` and `P`; the realm's prototype type by `A`, at one
fixed assignment (`ParameterInterpretation.realmAt`). -/
def rowSem (G : NormalGraph ι) (A X : List ι → Fam) (P : List ι → ArgFam) (c : Clause (List ι)) : Fam :=
  fun n W v => semWithArgs X P c n W v ∧ realmInvariant G A c n W v

theorem arrayInvariant_adm (P : Fam) (N : List PropKey) : Adm (arrayInvariant P N) := by
  constructor
  · intro n W v h flds oid hv hs
    obtain ⟨h1, h2⟩ := h flds oid hv hs
    exact ⟨(viewT_adm _).down n W v h1, (ownKeysT_adm _).down n W v h2⟩
  · intro n W W' hx v h flds oid hv hs
    obtain ⟨h1, h2⟩ := h flds oid hv hs
    exact ⟨(viewT_adm _).mono n W W' hx v h1, (ownKeysT_adm _).mono n W W' hx v h2⟩

/-- The invariant reads the prototype's type only below the budget, through
the contract of the prototype key. -/
theorem arrayInvariant_congr {P Q : Fam} (N : List PropKey) {n : Nat} (h : Agree P Q n)
    (W : WorldT n) (v : Val) : arrayInvariant P N n W v ↔ arrayInvariant Q N n W v := by
  have side : ∀ (P Q : Fam), Agree P Q n → arrayInvariant P N n W v → arrayInvariant Q N n W v := by
    intro P Q h hv flds oid he hs
    obtain ⟨h1, h2⟩ := hv flds oid he hs
    refine ⟨fun f T hm => ?_, h2⟩
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1 CallArguments.arrayStoreField anyStoreT (by simp)
    · obtain ⟨flds', l, c, oid', he', hf, hl, hag⟩ := h1 CallArguments.protoField P (by simp)
      exact ⟨flds', l, c, oid', he', hf, hl, fun j hj W' u hu => (h j hj W' u).mp (hag j hj W' u hu)⟩
  exact ⟨side P Q h, side Q P fun j hj W' u => (h j hj W' u).symm⟩

theorem realmInvariant_adm (G : NormalGraph ι) (X : List ι → Fam) (c : Clause (List ι)) :
    Adm (realmInvariant G X c) := by
  unfold realmInvariant
  cases G.realm with
  | none => exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  | some r =>
    cases c.record
    · exact ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩
    · exact arrayInvariant_adm _ _

theorem realmInvariant_congr (G : NormalGraph ι) (X Y : List ι → Fam) (n : Nat)
    (h : ∀ a, Agree (X a) (Y a) n) (c : Clause (List ι)) (W : WorldT n) (v : Val) :
    realmInvariant G X c n W v ↔ realmInvariant G Y c n W v := by
  unfold realmInvariant
  cases G.realm with
  | none => exact Iff.rfl
  | some r =>
    cases c.record
    · exact Iff.rfl
    · exact arrayInvariant_congr _ (h _) W v

/-- Without a realm, a row asks nothing of its prototype type. -/
theorem rowSem_none {G : NormalGraph ι} (hR : G.realm = none) (A X : List ι → Fam)
    (P : List ι → ArgFam) : rowSem G A X P = rowSem G (fun _ _ _ _ => True) X P := by
  funext c n W v
  simp only [rowSem, realmInvariant, hR]

theorem rowSem_adm (G : NormalGraph ι) (A X : List ι → Fam) (P : List ι → ArgFam)
    (c : Clause (List ι)) : Adm (rowSem G A X P c) :=
  interT_adm _ _ (semWithArgs_adm X P c) (realmInvariant_adm G A c)

theorem rowSem_congr (G : NormalGraph ι) (A B X Y : List ι → Fam) (P Q : List ι → ArgFam) (n : Nat)
    (hA : ∀ a, Agree (A a) (B a) n)
    (h : ∀ a, Agree (X a) (Y a) n) (hP : ∀ a, Agree (P a) (Q a) n) (c : Clause (List ι))
    (W : WorldT n) (v : Val) : rowSem G A X P c n W v ↔ rowSem G B Y Q c n W v :=
  and_congr (semWithArgs_congr X Y P Q n h hP c W v) (realmInvariant_congr G A B n hA c W v)

/-- A clause that is not a record's asks nothing more in a row. -/
theorem realmInvariant_of_not_record {G : NormalGraph ι} {X : List ι → Fam} {c : Clause (List ι)}
    (hc : c.record = false) (n W v) : realmInvariant G X c n W v := by
  unfold realmInvariant
  cases G.realm with
  | none => trivial
  | some r => simp [hc]

/-- Clauses none of which is a record's mean in a row what they mean alone. -/
theorem setSem_row_plain {G : NormalGraph ι} {A X : List ι → Fam} {P : List ι → ArgFam}
    {cs : List (Clause (List ι))} (hc : ∀ c ∈ cs, c.record = false) (n W v) :
    setSem (rowSem G A X P) cs n W v ↔ semList X P cs n W v := by
  constructor
  · rintro ⟨c, hm, hv, -⟩; exact ⟨c, hm, hv⟩
  · rintro ⟨c, hm, hv⟩; exact ⟨c, hm, hv, realmInvariant_of_not_record (hc c hm) n W v⟩

/-- The same, as a rewrite: a clause that is not a record's asks nothing. -/
theorem realmInvariant_iff_of_not_record {G : NormalGraph ι} {X : List ι → Fam}
    {c : Clause (List ι)} (hc : c.record = false) (n W v) : realmInvariant G X c n W v ↔ True :=
  iff_true_intro (realmInvariant_of_not_record hc n W v)

/-- A graph without a realm asks nothing more. -/
theorem realmInvariant_of_none {G : NormalGraph ι} {X : List ι → Fam} {c : Clause (List ι)}
    (hr : G.realm = none) (n W v) : realmInvariant G X c n W v := by
  unfold realmInvariant
  rw [hr]
  trivial

/-- An object that does not own the store key meets the invariant. -/
theorem arrayInvariant_of_lookup {P : Fam} {N : List PropKey} {n W flds code}
    (h : flds.lookup CallArguments.arrayStoreField = none) :
    arrayInvariant P N n W (.objAt flds code oid) := by
  intro flds' oid' he hs
  cases he
  simp [h] at hs

/-- A value that is not a plain object meets the invariant. -/
theorem arrayInvariant_of_not_plain {P : Fam} {N : List PropKey} {n W v}
    (h : ∀ flds oid, v ≠ .objAt flds .absent oid) : arrayInvariant P N n W v :=
  fun flds oid he _ => absurd he (h flds oid)

/-- A row's clause without the store key, or not a plain object, asks nothing
it does not already have. -/
theorem realmInvariant_of_lookup {G : NormalGraph ι} {X : List ι → Fam} {c : Clause (List ι)}
    {n W flds code} (h : flds.lookup CallArguments.arrayStoreField = none) :
    realmInvariant G X c n W (.objAt flds code oid) := by
  unfold realmInvariant
  cases G.realm with
  | none => trivial
  | some r =>
    cases c.record
    · trivial
    · exact arrayInvariant_of_lookup h

theorem realmInvariant_of_not_plain {G : NormalGraph ι} {X : List ι → Fam} {c : Clause (List ι)}
    {n W v} (h : ∀ flds oid, v ≠ .objAt flds .absent oid) : realmInvariant G X c n W v := by
  unfold realmInvariant
  cases G.realm with
  | none => trivial
  | some r =>
    cases c.record
    · trivial
    · exact arrayInvariant_of_not_plain h

/-- Two record clauses of one graph ask the same of their members. -/
theorem realmInvariant_record {G : NormalGraph ι} {X : List ι → Fam} {c d : Clause (List ι)}
    (hc : c.record = true) (hd : d.record = true) {n W v} :
    realmInvariant G X c n W v ↔ realmInvariant G X d n W v := by
  unfold realmInvariant
  cases G.realm with
  | none => exact Iff.rfl
  | some r => simp [hc, hd]

/-- Renaming a clause's operands keeps what the realm asks of it. -/
theorem realmInvariant_map (G : NormalGraph ι) (X : List ι → Fam) (f : List ι → List ι)
    (c : Clause (List ι)) : realmInvariant G X (c.map f) = realmInvariant G X c := by
  unfold realmInvariant
  rw [Clause.record_map]

/-- A meet of rows, read in a row, is the meet of what each asks. -/
theorem meetLists_row (G : NormalGraph ι) (Z X : List ι → Fam) (P : List ι → ArgFam)
    (A B : List (Clause (List ι))) (n W v) :
    setSem (rowSem G Z X P) (meetLists A B) n W v ↔
      setSem (rowSem G Z X P) A n W v ∧ setSem (rowSem G Z X P) B n W v := by
  have side : ∀ {c d : Clause (List ι)}, d.record = true → c.record = true →
      realmInvariant G Z d n W v → realmInvariant G Z c n W v := fun hd hc h =>
    (realmInvariant_record hd hc).mp h
  constructor
  · rintro ⟨c, hc, hv, hinv⟩
    obtain ⟨a, ha, b, hb, hm⟩ : ∃ a ∈ A, ∃ b ∈ B, c ∈ meet a b := by
      simp only [meetLists, List.mem_flatMap, List.mem_filter] at hc
      obtain ⟨a, ha, b, hb, hm, -⟩ := hc
      exact ⟨a, ha, b, hb, hm⟩
    have hh := (meet_sound X P a b n W v).mp ⟨c, hm, hv⟩
    have hr := meet_record hm
    refine ⟨⟨a, ha, hh.1, ?_⟩, ⟨b, hb, hh.2, ?_⟩⟩
    · cases har : a.record
      · exact realmInvariant_of_not_record har n W v
      · exact side (by simp [hr, har]) har hinv
    · cases hbr : b.record
      · exact realmInvariant_of_not_record hbr n W v
      · exact side (by simp [hr, hbr]) hbr hinv
  · rintro ⟨⟨a, ha, hva, hia⟩, ⟨b, hb, hvb, hib⟩⟩
    obtain ⟨c, hc, hv⟩ := (meet_sound X P a b n W v).mpr ⟨hva, hvb⟩
    refine ⟨c, ?_, hv, ?_⟩
    · simp only [meetLists, List.mem_flatMap, List.mem_filter]
      exact ⟨a, ha, b, hb, hc, semWithArgs_consistent hv⟩
    · have hr := meet_record hc
      cases hcr : c.record
      · exact realmInvariant_of_not_record hcr n W v
      · rw [hcr] at hr
        cases har : a.record
        · have hbr : b.record = true := by simpa [har] using hr.symm
          exact side hbr hcr hib
        · exact side har hcr hia

def normalLayer (G : NormalGraph ι) (X : ι → Fam) (i : ι) : Fam :=
  setSem (rowSem G (setSem X) (setSem X) (plainArguments G (setSem X))) (G i)

/-! ## The denotation, at every assignment

The fixed point is over `(assignment, label)`: a scheme row reads its
signatures' rows at reassignments of its binders. -/

variable {k : ParameterSpace}

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

/-- Neither grouping arguments nor reading a pack assignment adds a guard.
Agreement must be preserved in both the assignment and recursive meanings. -/
def ArgumentNonExp {k : ParameterSpace} (P : ArgumentInterpreter ι k) : Prop :=
  ∀ η θ X Y n, (∀ p, Agree (η.1 p) (θ.1 p) n) →
    (∀ S, Agree (X S) (Y S) n) → ∀ S, Agree (P η X S) (P θ Y S) n

/-- Interpret argument rows from their shapes and parameter assignments.
Ordinary value rows and value parameters have no argument-list members.
Tuple positions use the recursive value meanings at the current level. -/
def graphArguments (G : NormalGraph ι) : ArgumentInterpreter ι .mixed :=
  fun η X S n W vs => ∃ i ∈ S,
    if G.parameterKinds i = some .arguments then η.1 i n W (.inr vs)
    else ∃ c ∈ G i, clauseArguments X c n W vs

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
  simp [graphArguments, clauseArguments, hp, h]

theorem graphArguments_nonexp (G : NormalGraph ι) : ArgumentNonExp (graphArguments G) := by
  intro η θ X Y n hη hX S j hj W vs
  unfold graphArguments
  apply exists_congr fun i => and_congr Iff.rfl ?_
  split
  · exact hη i j hj W (.inr vs)
  · apply exists_congr fun c => and_congr Iff.rfl ?_
    exact clauseArguments_congr X Y c j W (fun a v => hX a j hj W v) vs

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
    (s : SchemeRow ι) (As : List (ParameterFamily k)) : List (Arrow Fam) :=
  let η' := assign η s.binders As
  s.signatures.map (Arrow.map (D η'))

/-- One instance's variadic signatures, their rows read at the reassignment. -/
noncomputable def instanceRestsWithArgs (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι)
    (s : SchemeRow ι) (As : List (ParameterFamily k))
    (P : ArgumentInterpreter ι k) : List RestSignature :=
  let η' := assign η s.binders As
  s.variadic.map (RestArrow.mapWith (D η') (P η' (D η')))

/-- One instance's contract: its fixed and its variadic signatures, as a call
clause's are. -/
noncomputable def instanceTWithArgs (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι)
    (s : SchemeRow ι) (As : List (ParameterFamily k))
    (P : ArgumentInterpreter ι k) : Fam :=
  interT (CallEffects.callsT (instanceSigs D η s As)) (CallEffects.restsT (instanceRestsWithArgs D η s As (P := P)))

theorem instanceTWithArgs_adm (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (As : List (ParameterFamily k)) (P : ArgumentInterpreter ι k) :
    Adm (instanceTWithArgs D η s As (P := P)) :=
  interT_adm _ _ (CallEffects.callsT_adm _) (CallEffects.restsT_adm _)

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
    (CallEffects.callsT_congr s.signatures
      (Arrow.map (D (assign η s.binders As))) (Arrow.map (D' (assign η' s.binders As')))
      (fun _ _ => rfl) (fun p _ => ⟨h p.receiver, argsAgree_of h p.arguments, h p.result⟩) W v)
    (CallEffects.restsT_congr s.variadic
      (RestArrow.mapWith (D (assign η s.binders As)) (P (assign η s.binders As) (D (assign η s.binders As))))
      (RestArrow.mapWith (D' (assign η' s.binders As')) (P (assign η' s.binders As') (D' (assign η' s.binders As'))))
      (fun _ _ => rfl)
      (fun p _ => ⟨h p.receiver, argsAgree_of h p.arguments.1, hP _ _ _ _ m hη h p.arguments.2, h p.result⟩) W v)

/-- Universal quantification has one implementation for both semantic sorts.
The body still denotes a runtime callable; its parameters may denote lists. -/
noncomputable def boundedSem
    (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier)
    (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (body : List (ParameterFamily k) → Fam)
    (domain : SchemeDomain ι k := .ordinary) : Fam := fun n W v =>
  Invocable v ∧ ∀ j (hj : j ≤ n) As, As.length = s.binders.length →
    domain.allowed s As → Bounded D η s As j → body As j (trunc j hj W) v

/-- The assignment carrier is independent of recursive value outputs. A domain
projects parameter values and derives bounds from those outputs at the same
level. These laws are precisely what the shared guarded fixed point needs. -/
structure ParameterInterpretation (ι : Type) (k : ParameterSpace) where
  domain : SchemeDomain ι k := .ordinary
  parameter : ι → WorldFamily k.Carrier → WorldFamily k.Carrier
  arguments : ArgumentInterpreter ι k
  arguments_nonexp : ArgumentNonExp arguments
  value : ι → WorldFamily k.Carrier → Fam
  value_parameter : ∀ i A B, parameter i A = parameter i B → value i A = value i B
  value_adm : ∀ i A, Adm A → Adm (value i A)
  value_congr : ∀ i A B n, Agree A B n → Agree (value i A) (value i B) n
  bound : ParameterAssignment k ι → (List ι → Fam) → List ι → WorldFamily k.Carrier
  bound_adm : ∀ η X, (∀ S, Adm (X S)) → ∀ S, Adm (bound η X S)
  bound_congr : ∀ η θ X Y n, (∀ p, Agree (η.1 p) (θ.1 p) n) →
    (∀ S, Agree (X S) (Y S) n) → ∀ S, Agree (bound η X S) (bound θ Y S) n
  /-- The assignment the realm's prototype type is read at (`realmInvariant`).
  That type is `ArrayProto`'s, a declaration without parameters whose generic
  methods bind their own, so it reads no parameter row and means the same at
  every assignment; reading it at one fixed assignment keeps a graph's meaning
  independent of its own assignment, as every check is (`Parametricity`). -/
  realmAt : ParameterAssignment k ι

/-- Mixed bounds retain both components. Projecting only their value part would
make a pack bound vacuous. Argument rows are derived, never unfolded again. -/
def mixedParameters (G : NormalGraph ι) : ParameterInterpretation ι .mixed where
  domain := G.domain
  parameter := fun i A => selectParameter (G.parameterKinds i) A
  arguments := graphArguments G
  arguments_nonexp := graphArguments_nonexp G
  value := fun i A n W v => G.parameterKinds i = some .value ∧ A n W (.inl v)
  value_parameter := by
    intro i A B h
    funext n W v
    exact congrFun (congrFun (congrFun h n) W) (.inl v)
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
  realmAt := ParameterAssignment.empty .mixed

/-- **A scheme row.** A callable meeting its signatures at every instantiation
of its binders within their bounds: the same value, in the same world, at all
of them. -/
noncomputable def schemeSemWithArgs (I : ParameterInterpretation ι k) (D : ParameterAssignment k ι → List ι → Fam) (η : ParameterAssignment k ι)
    (s : SchemeRow ι) : Fam :=
  boundedSem (fun θ S => I.bound θ (D θ) S) η s (fun As => instanceTWithArgs D η s As I.arguments) I.domain

/-- A meet row's part, read at the meet's own level (RECURSIVE-EQUATIONS §3.3):
a parameter's family, a scheme row's instances, or a clause row's clauses. It
is the step's reading of a row that is not a meet row, so a meet reads its
parts by one unfolding: a part is never itself a meet row. -/
noncomputable def partSemWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (X : ParameterAssignment k ι × ι → Fam) (η : ParameterAssignment k ι) (q : ι) : Fam :=
  if G.params q then I.value q (η.1 q) else
  match G.schemes q with
  | some s => schemeSemWithArgs I (fun η' S => setSem (fun l => X (η', l)) S) η s
  | none => setSem (rowSem G (setSem fun l => X (I.realmAt, l)) (setSem fun l => X (η, l))
      (I.arguments η (setSem fun l => X (η, l)))) (G q)

/-- One step of the assignment-indexed denotation. -/
noncomputable def qLayerWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k) (X : ParameterAssignment k ι × ι → Fam) :
    ParameterAssignment k ι × ι → Fam := fun ηi =>
  if G.params ηi.2 then I.value ηi.2 (ηi.1.1 ηi.2) else
  match G.schemes ηi.2 with
  | some s => schemeSemWithArgs I (fun η' S => setSem (fun l => X (η', l)) S) ηi.1 s
  | none =>
    match G.meets ηi.2 with
    -- A meet row: each part's values, within the clauses.
    | some (p, cs) => fun n W v =>
        (partSemWithArgs G I X ηi.1 p n W v ∧
          ∀ q ∈ G.meetParams ηi.2, partSemWithArgs G I X ηi.1 q n W v) ∧
        setSem (rowSem G (setSem fun l => X (I.realmAt, l)) (setSem fun l => X (ηi.1, l))
          (I.arguments ηi.1 (setSem fun l => X (ηi.1, l)))) cs n W v
    | none => setSem (rowSem G (setSem fun l => X (I.realmAt, l)) (setSem fun l => X (ηi.1, l))
        (I.arguments ηi.1 (setSem fun l => X (ηi.1, l)))) (G ηi.2)

/-- A parameter part is its assigned family, as in a meet row of parameters. -/
@[simp] theorem partSemWithArgs_param {G : NormalGraph ι} {I : ParameterInterpretation ι k}
    {X : ParameterAssignment k ι × ι → Fam} {η : ParameterAssignment k ι} {q : ι}
    (h : G.params q = true) : partSemWithArgs G I X η q = I.value q (η.1 q) := by
  simp [partSemWithArgs, h]

/-- Outside a meet row, the step reads a row as a part. -/
theorem qLayer_part {G : NormalGraph ι} {I : ParameterInterpretation ι k}
    {X : ParameterAssignment k ι × ι → Fam} {η : ParameterAssignment k ι} {i : ι}
    (h : G.params i = true ∨ (G.schemes i).isSome = true ∨ G.meets i = none) :
    qLayerWithArgs G I X (η, i) = partSemWithArgs G I X η i := by
  unfold qLayerWithArgs partSemWithArgs
  by_cases hp : G.params i = true
  · simp [hp]
  · simp only [hp, Bool.false_eq_true, ite_false]
    cases hs : G.schemes i with
    | some s => rfl
    | none =>
      have hm : G.meets i = none := by simpa [hp, hs] using h
      simp only [hm]

theorem plainArguments_congr (G : NormalGraph ι) {X Y : List ι → Fam} {n : Nat}
    (h : ∀ S, Agree (X S) (Y S) n) (S : List ι) :
    Agree (plainArguments G X S) (plainArguments G Y S) n := by
  intro j hj W vs
  refine exists_congr fun i => and_congr Iff.rfl (exists_congr fun c => and_congr Iff.rfl ?_)
  exact clauseArguments_congr X Y c j W (fun a v => h a j hj W v) vs

theorem normalLayer_congr (G : NormalGraph ι) : LayerCongr (normalLayer G) := by
  intro X Y n h i W v
  have hs := fun a => setSem_congr n h a
  constructor <;> rintro ⟨c, hc, hv⟩ <;> refine ⟨c, hc, ?_⟩
  · exact (rowSem_congr G _ _ _ _ _ _ n hs hs (plainArguments_congr G hs) c W v).mp hv
  · exact (rowSem_congr G _ _ _ _ _ _ n hs hs (plainArguments_congr G hs) c W v).mpr hv

theorem Agree.mono {A B : WorldFamily α} {n m : Nat} (h : Agree A B n) (hm : m ≤ n) : Agree A B m :=
  fun k hk W v => h k (by omega) W v

theorem argsAgree_mono {As Bs : List Fam} {n m : Nat} (h : ArgsAgree n As Bs) (hm : m ≤ n) :
    ArgsAgree m As Bs := by
  induction h with
  | nil => exact .nil
  | cons hA _ ih => exact .cons (Agree.mono hA hm) ih

/-- A part reads its operands below the level. -/
theorem partSem_congrWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    {X Y : ParameterAssignment k ι × ι → Fam} {n : Nat} (h : ∀ ηi, Agree (X ηi) (Y ηi) n)
    (η : ParameterAssignment k ι) (i : ι) (W : WorldT n) (v : Val) :
    partSemWithArgs G I X η i n W v ↔ partSemWithArgs G I Y η i n W v := by
  unfold partSemWithArgs
  by_cases hp : G.params i = true
  · simp [hp]
  · simp only [hp]
    cases hq : G.schemes i with
    | none =>
      have hS := fun S => setSem_congr n (fun l => h (η, l)) S
      have hE := fun S => setSem_congr n (fun l => h (I.realmAt, l)) S
      constructor <;> rintro ⟨c, hc, hv⟩ <;> refine ⟨c, hc, ?_⟩
      · exact (rowSem_congr G _ _ _ _ _ _ n hE hS (I.arguments_nonexp η η _ _ n (fun _ _ _ _ _ => Iff.rfl) hS) c W v).mp hv
      · exact (rowSem_congr G _ _ _ _ _ _ n hE hS (I.arguments_nonexp η η _ _ n (fun _ _ _ _ _ => Iff.rfl) hS) c W v).mpr hv
    | some s =>
      refine and_congr Iff.rfl (forall_congr' fun q => forall_congr' fun hq => forall_congr' fun As => forall_congr' fun _ => forall_congr' fun _ => ?_)
      refine imp_congr ?_ ?_
      · unfold Bounded
        refine forall_congr' fun b => forall_congr' fun _ => forall_congr' fun _ =>
          forall_congr' fun j => forall_congr' fun hj => forall_congr' fun U =>
          forall_congr' fun u => imp_congr Iff.rfl ?_
        exact I.bound_congr _ _ _ _ n (fun _ _ _ _ _ => Iff.rfl)
          (fun S => setSem_congr n (fun l => h (_, l)) S) b.2 j (by omega) U u
      · exact instanceT_congrWithArgs I.arguments I.arguments_nonexp (fun _ _ _ _ _ => Iff.rfl) (fun S => Agree.mono (setSem_congr n (fun l => h (_, l)) S) hq) (trunc q hq W) v

theorem qLayer_congrWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    : LayerCongr (fun X => qLayerWithArgs G I X) := by
  intro X Y n h ηi W v
  obtain ⟨η, i⟩ := ηi
  by_cases hmeet : G.params i = true ∨ (G.schemes i).isSome = true ∨ G.meets i = none
  · dsimp only
    rw [qLayer_part hmeet, qLayer_part hmeet]
    exact partSem_congrWithArgs G I h η i W v
  · simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hmeet
    obtain ⟨hp, hq, hm⟩ := hmeet
    obtain ⟨⟨p, cs⟩, hm⟩ := Option.ne_none_iff_exists'.mp hm
    unfold qLayerWithArgs
    simp only [hp, hq, hm, Bool.false_eq_true, ite_false]
    have hS := fun S => setSem_congr n (fun l => h (η, l)) S
    have hE := fun S => setSem_congr n (fun l => h (I.realmAt, l)) S
    refine and_congr (and_congr (partSem_congrWithArgs G I h η p W v)
      (forall_congr' fun q => imp_congr_right fun _ => partSem_congrWithArgs G I h η q W v)) ?_
    constructor <;> rintro ⟨c, hc, hv⟩ <;> refine ⟨c, hc, ?_⟩
    · exact (rowSem_congr G _ _ _ _ _ _ n hE hS (I.arguments_nonexp η η _ _ n (fun _ _ _ _ _ => Iff.rfl) hS) c W v).mp hv
    · exact (rowSem_congr G _ _ _ _ _ _ n hE hS (I.arguments_nonexp η η _ _ n (fun _ _ _ _ _ => Iff.rfl) hS) c W v).mpr hv

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

/-- Each smaller approximation retains its own bounded instances. -/
theorem boundedSem_adm
    (D : ParameterAssignment k ι → List ι → WorldFamily k.Carrier)
    (η : ParameterAssignment k ι) (s : SchemeRow ι)
    (body : List (ParameterFamily k) → Fam)
    (_hD : ∀ S, Adm (D η S)) (hbody : ∀ As, Adm (body As))
    (_hcongr : ∀ As Bs m,
      (∀ p, Agree ((assign η s.binders As).1 p) ((assign η s.binders Bs).1 p) m) →
      ∀ W v, body As m W v ↔ body Bs m W v)
    (domain : SchemeDomain ι k := .ordinary) :
    Adm (boundedSem D η s body domain) := by
  constructor
  · intro n W v h
    refine ⟨h.1, fun j hj As hl ha hb => ?_⟩
    simpa only [trunc_trunc] using h.2 j (by omega) As hl ha hb
  · intro n W W' hx v h
    exact ⟨h.1, fun j hj As hl ha hb =>
      (hbody As).mono j _ _ (WExt_trunc hj hx) v (h.2 j hj As hl ha hb)⟩

/-- A part is admissible, and non-expansive in the assignment. -/
theorem partSem_invWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (X : ParameterAssignment k ι × ι → Fam) (hX : QInv X) :
    (∀ η i, Adm (partSemWithArgs G I X η i)) ∧
    ∀ η η' i m, (∀ p, Agree (η.1 p) (η'.1 p) m) →
      Agree (partSemWithArgs G I X η i) (partSemWithArgs G I X η' i) m := by
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
  refine ⟨fun η i => ?_, fun η η' i m h => ?_⟩
  · -- admissible
    unfold partSemWithArgs
    by_cases hp : G.params i = true
    · simpa [hp] using I.value_adm i (η.1 i) (η.2 i).1
    · simp only [hp]
      cases hq : G.schemes i with
      | none => exact setSem_adm (fun c => rowSem_adm G _ _ _ c) (G i)
      | some s =>
        exact boundedSem_adm _ η s _ (I.bound_adm η _ (hD η))
          (fun As => instanceTWithArgs_adm _ η s As I.arguments)
          (fun As Bs m h W v => instanceT_congrWithArgs I.arguments I.arguments_nonexp h (fun S => sets _ _ m h S) W v) I.domain
  · -- non-expansive
    intro k hk W v
    unfold partSemWithArgs
    by_cases hp : G.params i = true
    · simp only [hp, if_true]; exact I.value_congr i _ _ m (h i) k hk W v
    · simp only [hp]
      cases hq : G.schemes i with
      | none =>
        have cl : ∀ cs : List (Clause (List ι)),
            setSem (rowSem G (setSem fun l => X (I.realmAt, l)) (setSem fun l => X (η, l)) (I.arguments η (setSem fun l => X (η, l)))) cs k W v ↔
              setSem (rowSem G (setSem fun l => X (I.realmAt, l)) (setSem fun l => X (η', l)) (I.arguments η' (setSem fun l => X (η', l)))) cs k W v := by
          intro cs
          constructor
          · rintro ⟨c, hc, hv⟩
            exact ⟨c, hc, (rowSem_congr G _ _ _ _ _ _ k (fun _ _ _ _ _ => Iff.rfl)
              (fun a => Agree.mono (sets η η' m h a) (by omega))
              (I.arguments_nonexp η η' _ _ k (fun p => Agree.mono (h p) (by omega)) (fun a => Agree.mono (sets η η' m h a) (by omega))) c W v).mp hv⟩
          · rintro ⟨c, hc, hv⟩
            exact ⟨c, hc, (rowSem_congr G _ _ _ _ _ _ k (fun _ _ _ _ _ => Iff.rfl)
              (fun a => Agree.mono (sets η η' m h a) (by omega))
              (I.arguments_nonexp η η' _ _ k (fun p => Agree.mono (h p) (by omega)) (fun a => Agree.mono (sets η η' m h a) (by omega))) c W v).mpr hv⟩
        exact cl _
      | some s =>
        refine and_congr Iff.rfl (forall_congr' fun q => forall_congr' fun hq => forall_congr' fun As => forall_congr' fun _ => forall_congr' fun _ => ?_)
        have hre := reassign η η' s.binders As m h
        refine imp_congr ?_ ?_
        · unfold Bounded
          refine forall_congr' fun b => forall_congr' fun _ => forall_congr' fun _ =>
            forall_congr' fun j => forall_congr' fun hj => forall_congr' fun U =>
            forall_congr' fun u => imp_congr (hre b.1 j (by omega) U u)
              (I.bound_congr η η' _ _ m h (sets η η' m h) b.2 j (by omega) U u)
        · exact instanceT_congrWithArgs I.arguments I.arguments_nonexp (fun p => Agree.mono (hre p) (by omega)) (fun S => Agree.mono (sets _ _ m hre S) (by omega)) (trunc q hq W) v

theorem qLayer_invWithArgs (G : NormalGraph ι) (I : ParameterInterpretation ι k)
    (X : ParameterAssignment k ι × ι → Fam) (hX : QInv X) :
    QInv (qLayerWithArgs G I X) := by
  obtain ⟨hpa, hpn⟩ := partSem_invWithArgs G I X hX
  obtain ⟨hadm, hne⟩ := hX
  have sets : ∀ (η η' : ParameterAssignment k ι) m, (∀ p, Agree (η.1 p) (η'.1 p) m) → ∀ S,
      Agree (setSem (fun l => X (η, l)) S) (setSem (fun l => X (η', l)) S) m :=
    fun η η' m h S => setSem_congr m (fun l => hne η η' l m h) S
  refine ⟨fun ηi => ?_, fun η η' i m h => ?_⟩
  · obtain ⟨η, i⟩ := ηi
    by_cases hmeet : G.params i = true ∨ (G.schemes i).isSome = true ∨ G.meets i = none
    · rw [qLayer_part hmeet]; exact hpa η i
    · simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hmeet
      obtain ⟨hp, hq, hm⟩ := hmeet
      obtain ⟨⟨p, cs⟩, hm⟩ := Option.ne_none_iff_exists'.mp hm
      unfold qLayerWithArgs
      simp only [hp, hq, hm, Bool.false_eq_true, ite_false]
      have hqs : Adm (fun n W v => ∀ q ∈ G.meetParams i, partSemWithArgs G I X η q n W v) :=
        ⟨fun n W v h q hq => (hpa η q).down n W v (h q hq),
         fun n W U hx v h q hq => (hpa η q).mono n W U hx v (h q hq)⟩
      exact interT_adm _ _ (interT_adm _ _ (hpa η p) hqs)
        (setSem_adm (fun c => rowSem_adm G _ _ _ c) cs)
  · intro k hk W v
    by_cases hmeet : G.params i = true ∨ (G.schemes i).isSome = true ∨ G.meets i = none
    · rw [qLayer_part hmeet, qLayer_part hmeet]; exact hpn η η' i m h k hk W v
    · simp only [not_or, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hmeet
      obtain ⟨hp, hq, hm⟩ := hmeet
      obtain ⟨⟨p, cs⟩, hm⟩ := Option.ne_none_iff_exists'.mp hm
      unfold qLayerWithArgs
      simp only [hp, hq, hm, Bool.false_eq_true, ite_false]
      refine and_congr (and_congr (hpn η η' p m h k hk W v)
        (forall_congr' fun q => imp_congr_right fun _ => hpn η η' q m h k hk W v)) ?_
      constructor
      · rintro ⟨c, hc, hv⟩
        exact ⟨c, hc, (rowSem_congr G _ _ _ _ _ _ k (fun _ _ _ _ _ => Iff.rfl)
          (fun a => Agree.mono (sets η η' m h a) (by omega))
          (I.arguments_nonexp η η' _ _ k (fun p => Agree.mono (h p) (by omega)) (fun a => Agree.mono (sets η η' m h a) (by omega))) c W v).mp hv⟩
      · rintro ⟨c, hc, hv⟩
        exact ⟨c, hc, (rowSem_congr G _ _ _ _ _ _ k (fun _ _ _ _ _ => Iff.rfl)
          (fun a => Agree.mono (sets η η' m h a) (by omega))
          (I.arguments_nonexp η η' _ _ k (fun p => Agree.mono (h p) (by omega)) (fun a => Agree.mono (sets η η' m h a) (by omega))) c W v).mpr hv⟩

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

/-- Both semantic components of a type, derived from one recursive value
interpretation. Argument rows are evaluated at that same level. -/
noncomputable def mixedMeaning (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι) :
    WorldFamily ParameterSpace.mixed.Carrier :=
  (mixedParameters G).bound η
    (setSem fun i => qDenoteWithArgs G (mixedParameters G) (η, i)) S

/-- The shared fixed point still produces only closed runtime values. -/
theorem mixedDenote_value (G : NormalGraph ι) (η : MixedAssignment ι) (i : ι) {n W v}
    (h : qDenoteWithArgs G (mixedParameters G) (η, i) n W v) :
    isVal v = true ∧ Scoped 0 v := by
  rw [qDenoteWithArgs_unfold] at h
  unfold qLayerWithArgs at h
  split at h
  · exact (η.2 i).2 n W (.inl v) h.2
  · cases hs : G.schemes i with
    | some s => simp only [hs] at h; exact ⟨h.1.val, h.1.scoped⟩
    | none =>
      simp only [hs] at h
      cases hm : G.meets i with
      | none =>
        simp only [hm] at h
        obtain ⟨c, _, hc⟩ := h
        exact semWithArgs_value hc.1
      | some pc =>
        simp only [hm] at h
        obtain ⟨c, _, hc⟩ := h.2
        exact semWithArgs_value hc.1

theorem mixedMeaning_valid (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι) :
    ParameterValid .mixed (mixedMeaning G η S) := by
  let X := fun S => setSem (fun i => qDenoteWithArgs G (mixedParameters G) (η, i)) S
  have hX : ∀ S, ValueFam (X S) := fun S =>
    ⟨setSem_adm (fun i => qDenoteWithArgs_adm G (mixedParameters G) (η, i)) S,
     fun _ _ _ ⟨i, _, hi⟩ => mixedDenote_value G η i hi⟩
  refine ⟨(mixedParameters G).bound_adm η X (fun S => (hX S).1) S, ?_⟩
  intro n W x h
  cases x with
  | inl v => exact (hX S).2 n W v h
  | inr vs => exact (graphArguments_valid G η X hX S).2 n W vs h

/-- A parameter's two-component row meaning is exactly its selected component,
not the whole (potentially mixed) family assigned to that binder. -/
theorem mixedMeaning_parameter (G : NormalGraph ι) (η : MixedAssignment ι) (i : ι)
    (kind : ParameterKind) (hi : G.parameterKinds i = some kind) :
    mixedMeaning G η [i] = selectParameter (some kind) (η.1 i) := by
  have hp : G.params i = true := by simp [NormalGraph.params, hi]
  have hc : G i = [] := by simp [NormalGraph.clauses, NormalGraph.plain, hp]
  funext n W x
  apply propext
  cases x with
  | inl v =>
    change (∃ j ∈ [i], qDenoteWithArgs G (mixedParameters G) (η, j) n W v) ↔ _
    simp only [List.mem_singleton, exists_eq_left]
    rw [qDenoteWithArgs_unfold]
    simp [qLayerWithArgs, hp, mixedParameters, selectParameter, hi]
  | inr vs =>
    change graphArguments G η _ [i] n W vs ↔ _
    cases kind <;> simp [graphArguments, hc, hi, selectParameter]

/-- A plain pack row has list members only: no runtime value. -/
theorem mixedMeaning_pack_value (G : NormalGraph ι) (η : MixedAssignment ι) (i : ι)
    (a : Tuple (List ι)) (bs : List (Tuple (List ι))) (hi : G i = [.pack a bs])
    (n : Nat) (W : WorldT n) (v : Val) : ¬ mixedMeaning G η [i] n W (.inl v) := by
  have hp := NormalGraph.plain_of_clauses (G := G) (i := i)
    (show Clause.pack a bs ∈ G i by rw [hi]; simp)
  rw [NormalGraph.plain_iff] at hp
  change ¬ (∃ j ∈ [i], qDenoteWithArgs G (mixedParameters G) (η, j) n W v)
  simp only [List.mem_singleton, exists_eq_left]
  rw [qDenoteWithArgs_unfold]
  simp [qLayerWithArgs, hp.1, hp.2.1, hp.2.2, hi, setSem, rowSem, semWithArgs]

/-- A sorted pack type cannot contribute runtime-value members, including
unions of pack rows and pack parameters. -/
theorem mixedMeaning_noValues (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι)
    (hs : G.hasKind .arguments S = true) (n : Nat) (W : WorldT n) (v : Val) :
    ¬ mixedMeaning G η S n W (.inl v) := by
  rintro ⟨i, hi, hv⟩
  have hk := List.all_eq_true.mp hs i hi
  rw [qDenoteWithArgs_unfold] at hv
  unfold qLayerWithArgs at hv
  cases hp : G.parameterKinds i with
  | some k =>
    cases k <;> simp [hp] at hk
    simp [NormalGraph.params, hp, mixedParameters] at hv
  | none =>
    cases hq : G.schemes i with
    | some sch => simp [hp, hq] at hk
    | none =>
      cases hm : G.meets i with
      | some pc => simp [hp, hq, hm] at hk
      | none =>
      simp only [NormalGraph.params, hp, Option.isSome_none, Bool.false_eq_true, ite_false, hq, hm] at hv
      obtain ⟨c, hc, hcv⟩ := hv
      have hplain : G.plain i = true := by simp [NormalGraph.plain, NormalGraph.params, hp, hq, hm]
      have hr : c ∈ G.rows i := by simpa [NormalGraph.clauses, hplain] using hc
      have ht := List.all_eq_true.mp (show (G.rows i).all
        (fun c => match c with | .pack .. => true | _ => false) = true by simpa [hp, hq, hm, (show (ParameterKind.arguments == ParameterKind.value) = false from rfl)] using hk) c hr
      cases c <;> simp_all [rowSem, semWithArgs]

/-- A sorted value type cannot contribute argument-list members. -/
theorem mixedMeaning_noArguments (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι)
    (hs : G.hasKind .value S = true) (n : Nat) (W : WorldT n) (vs : List Val) :
    ¬ mixedMeaning G η S n W (.inr vs) := by
  rintro ⟨i, hi, hv⟩
  have hk := List.all_eq_true.mp hs i hi
  by_cases hp : G.parameterKinds i = some .arguments
  · simp [hp] at hk
  · simp only [hp, ite_false] at hv
    obtain ⟨c, hc, hv⟩ := hv
    have hplain := NormalGraph.plain_of_clauses hc
    have hparts := NormalGraph.plain_iff.mp hplain
    have hn : G.parameterKinds i = none := by
      simpa [NormalGraph.params] using hparts.1
    have hr : c ∈ G.rows i := by simpa [NormalGraph.clauses, hplain] using hc
    have ht := List.all_eq_true.mp (show (G.rows i).all
      (fun c => match c with | .pack .. => false | _ => true) = true by
        simpa [hn, hparts.2.1, hparts.2.2, (show (ParameterKind.value == ParameterKind.arguments) = false from rfl)] using hk) c hr
    cases c <;> simp_all [clauseArguments]

/-- The existing sort check guarantees that a type image equals its selected
component. This connects the wire's kind check to semantic correspondence. -/
theorem mixedMeaning_selected (G : NormalGraph ι) (η : MixedAssignment ι) (S : List ι)
    (kind : ParameterKind) (hs : G.hasKind kind S = true) :
    selectParameter (some kind) (mixedMeaning G η S) = mixedMeaning G η S := by
  funext n W x
  apply propext
  cases kind <;> cases x
  · simp [selectParameter]
  · simp [selectParameter, mixedMeaning_noArguments G η S hs]
  · simp [selectParameter, mixedMeaning_noValues G η S hs]
  · simp [selectParameter]

/-- A graph's meaning reads its parameter rows at its own assignment. -/
noncomputable def normalDenote (G : NormalGraph ι) (i : ι) : Fam :=
  qDenoteWithArgs G (mixedParameters G) (G.env, i)

theorem normalDenote_adm (G : NormalGraph ι) (i : ι) : Adm (normalDenote G i) :=
  qDenoteWithArgs_adm G (mixedParameters G) _

/-- The argument lists a type admits: a pack parameter's assigned contract, or
a pack clause's tuple contracts, at the current level. -/
noncomputable def argMeaning (G : NormalGraph ι) (S : List ι) : ArgFam :=
  graphArguments G G.env (setSem (normalDenote G)) S

/-- A clause row means its clauses. -/
theorem unfold_plain {G : NormalGraph ι} {i : ι} (hi : G.plain i = true) (n W v) :
    normalDenote G i n W v ↔ setSem (rowSem G (setSem fun l => qDenoteWithArgs G (mixedParameters G)
      (ParameterAssignment.empty .mixed, l)) (setSem (normalDenote G)) (argMeaning G)) (G i) n W v := by
  simp only [NormalGraph.plain, Bool.and_eq_true, Bool.not_eq_true',
    Option.isNone_iff_eq_none] at hi
  unfold normalDenote
  rw [qDenoteWithArgs_unfold]
  simp only [qLayerWithArgs, hi.1, hi.2, Bool.false_eq_true, ite_false]
  rfl

/-- Every label means closed values only, whatever its kind. -/
theorem normalDenote_value {G : NormalGraph ι} {i : ι} {n W v}
    (h : normalDenote G i n W v) : isVal v = true ∧ Scoped 0 v :=
  mixedDenote_value G G.env i h

/-- Without parameter or scheme rows, a graph's argument lists are its
clauses'. -/
theorem graphArguments_plainGraph (G : NormalGraph ι) (hG : G.Plain) (η : MixedAssignment ι)
    (X : List ι → Fam) : graphArguments G η X = plainArguments G X := by
  funext S n W vs
  apply propext
  unfold graphArguments plainArguments
  refine exists_congr fun i => and_congr Iff.rfl ?_
  have hk : G.parameterKinds i ≠ some .arguments := by
    intro h
    have := hG i
    simp [NormalGraph.plain, NormalGraph.params, h] at this
  simp only [hk, ↓reduceIte]

private theorem approx_plain (G : NormalGraph ι) (hG : G.Plain) :
    ∀ k (η : MixedAssignment ι), (fun i => Tower.approx (qLayerWithArgs G (mixedParameters G)) k (η, i)) =
      Tower.approx (normalLayer G) k
  | 0, _ => rfl
  | k + 1, η => by
    funext i
    have ih := approx_plain G hG k η
    have ihE := approx_plain G hG k (ParameterAssignment.empty .mixed)
    have hi := hG i
    simp only [NormalGraph.plain, Bool.and_eq_true, Bool.not_eq_true',
      Option.isNone_iff_eq_none] at hi
    show qLayerWithArgs G (mixedParameters G)
        (Tower.approx (qLayerWithArgs G (mixedParameters G)) k) (η, i) =
      normalLayer G (Tower.approx (normalLayer G) k) i
    simp only [qLayerWithArgs, hi.1, hi.2, Bool.false_eq_true, ite_false]
    rw [show (mixedParameters G).realmAt = ParameterAssignment.empty .mixed from rfl, ih, ihE]
    unfold normalLayer
    rw [show (mixedParameters G).arguments = graphArguments G from rfl,
      graphArguments_plainGraph G hG]

/-- **Conservative.** A graph of clause rows means what its guarded fixed
point over clauses means. -/
theorem normalDenote_plain (G : NormalGraph ι) (hG : G.Plain) :
    normalDenote G = Tower.denote (normalLayer G) := by
  funext i n
  show Tower.approx (qLayerWithArgs G (mixedParameters G)) (n + 1) (G.env, i) n =
    Tower.approx (normalLayer G) (n + 1) i n
  rw [← approx_plain G hG (n + 1) G.env]

#print axioms mixedMeaning_selected
#print axioms mixedMeaning_valid
#print axioms mixedMeaning_parameter
#print axioms mixedMeaning_pack_value
#print axioms graphArguments_valid
#print axioms boundedSem_adm
#print axioms qDenoteWithArgs_unfold
#print axioms qDenoteWithArgs_adm
#print axioms qDenoteWithArgs_nonexp
#print axioms normalDenote_plain
end Verification.PositiveGraphs
