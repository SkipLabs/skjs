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

/-- A family a parameter row may mean: admissible, and of closed values only, as
every type's meaning is. -/
def ValueFam (A : Fam) : Prop := Adm A ∧ ∀ n W v, A n W v → isVal v = true ∧ Scoped 0 v

/-- An assignment of families to the parameter rows. -/
abbrev Assignment (ι : Type) := { η : ι → Fam // ∀ i, ValueFam (η i) }

/-- What a binder may be instantiated at. -/
abbrev ValueFamily := { A : Fam // ValueFam A }

def emptyFam : Fam := fun _ _ _ => False

theorem emptyFam_value : ValueFam emptyFam :=
  ⟨⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩, fun _ _ _ h => h.elim⟩

/-- The assignment of a graph without parameter rows: none is read. -/
def Assignment.empty : Assignment ι := ⟨fun _ => emptyFam, fun _ => emptyFam_value⟩

/-- A quantified callable: its binders, which are parameter rows, and the
signatures `(receiver, parameters, result)` each of its instances meets. -/
structure SchemeRow (ι : Type) where
  binders : List ι
  signatures : List (List ι × List (List ι) × List ι)

structure NormalGraph (ι : Type) where
  /-- A clause row's clauses. -/
  rows : ι → List (Clause (List ι))
  schemes : ι → Option (SchemeRow ι) := fun _ => none
  params : ι → Bool := fun _ => false
  /-- What the parameter rows mean. Semantic only. -/
  env : Assignment ι := Assignment.empty

/-- A clause row: neither a parameter nor a scheme. -/
def NormalGraph.plain (G : NormalGraph ι) (i : ι) : Bool := !G.params i && (G.schemes i).isNone

/-- A label's clauses. A parameter or scheme row has none: whatever `rows`
holds there is never read. -/
def NormalGraph.clauses (G : NormalGraph ι) (i : ι) : List (Clause (List ι)) :=
  if G.plain i then G.rows i else []

instance : CoeFun (NormalGraph ι) (fun _ => ι → List (Clause (List ι))) := ⟨NormalGraph.clauses⟩

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

open Classical in
/-- The assignment with each binder given the family at its position. -/
noncomputable def assign (η : Assignment ι) (bs : List ι) (As : List ValueFamily) :
    Assignment ι :=
  ⟨fun i => match (bs.zip As).lookup i with
      | some A => A.1
      | none => η.1 i,
   fun i => by
      cases h : (bs.zip As).lookup i with
      | some A => simpa [h] using A.2
      | none => simpa [h] using η.2 i⟩

open Classical in
/-- A binder is given the family at its position. -/
theorem assign_map_mem (η : Assignment ι) (bs : List ι) (F : ι → ValueFamily) {i : ι}
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
theorem assign_map_nmem (η : Assignment ι) (bs : List ι) (F : ι → ValueFamily) {i : ι}
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
theorem assign_nmem (η : Assignment ι) (bs : List ι) (As : List ValueFamily) {i : ι}
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

/-- Two assignments differing at most on `bs`. -/
def AgreeOff (bs : List ι) (η η' : Assignment ι) : Prop := ∀ p, p ∉ bs → η.1 p = η'.1 p

open Classical in
theorem agreeOff_assign {bs : List ι} {η η' : Assignment ι} (h : AgreeOff bs η η')
    (cs : List ι) (As : List ValueFamily) : AgreeOff bs (assign η cs As) (assign η' cs As) := by
  intro p hp
  simp only [assign]
  split <;> simp [h p hp]

/-- One instance's signatures, their rows read at the reassignment. -/
noncomputable def instanceSigs (D : Assignment ι → List ι → Fam) (η : Assignment ι)
    (s : SchemeRow ι) (As : List ValueFamily) : List (Fam × List Fam × Fam) :=
  let η' := assign η s.binders As
  s.signatures.map fun p => (D η' p.1, p.2.1.map (D η'), D η' p.2.2)

/-- **A scheme row.** A callable meeting its signatures at every instantiation
of its binders: the same value, in the same world, at all of them. -/
noncomputable def schemeSem (D : Assignment ι → List ι → Fam) (η : Assignment ι)
    (s : SchemeRow ι) : Fam := fun n W v =>
  Invocable v ∧ ∀ As : List ValueFamily, As.length = s.binders.length →
    callsT (instanceSigs D η s As) n W v

/-- One step of the assignment-indexed denotation. -/
noncomputable def qLayer (G : NormalGraph ι) (X : Assignment ι × ι → Fam) :
    Assignment ι × ι → Fam := fun ηi =>
  if G.params ηi.2 then ηi.1.1 ηi.2 else
  match G.schemes ηi.2 with
  | some s => schemeSem (fun η' S => setSem (fun l => X (η', l)) S) ηi.1 s
  | none => normalLayer G (fun l => X (ηi.1, l)) ηi.2

theorem normalLayer_congr (G : NormalGraph ι) : LayerCongr (normalLayer G) := by
  intro X Y n h i W v
  constructor <;> rintro ⟨c, hc, hv⟩ <;> refine ⟨c, hc, ?_⟩
  · exact (sem_congr _ _ n (fun a => setSem_congr n h a) c W v).mp hv
  · exact (sem_congr _ _ n (fun a => setSem_congr n h a) c W v).mpr hv

private theorem argsAgree_map {n : Nat} (X Y : ι → Fam) (h : ∀ l, Agree (X l) (Y l) n) :
    ∀ Ss : List (List ι), ArgsAgree n (Ss.map (setSem X)) (Ss.map (setSem Y))
  | [] => .nil
  | S :: Ss => .cons (setSem_congr n h S) (argsAgree_map X Y h Ss)

theorem qLayer_congr (G : NormalGraph ι) : LayerCongr (qLayer G) := by
  intro X Y n h ηi W v
  obtain ⟨η, i⟩ := ηi
  unfold qLayer
  by_cases hp : G.params i = true
  · simp [hp]
  · simp only [hp]
    cases hq : G.schemes i with
    | none => exact normalLayer_congr G _ _ n (fun l => h (η, l)) i W v
    | some s =>
      refine and_congr Iff.rfl (forall_congr' fun As => forall_congr' fun _ => ?_)
      unfold instanceSigs
      exact callsT_congr s.signatures _ _ (fun p _ =>
        ⟨setSem_congr n (fun l => h (_, l)) p.1,
         argsAgree_map _ _ (fun l => h (_, l)) p.2.1,
         setSem_congr n (fun l => h (_, l)) p.2.2⟩) W v

theorem schemeSem_adm (D : Assignment ι → List ι → Fam) (η : Assignment ι) (s : SchemeRow ι) :
    Adm (schemeSem D η s) := by
  constructor
  · intro n W v h
    exact ⟨h.1, fun As hl => (callsT_adm _).down n W v (h.2 As hl)⟩
  · intro n W W' hx v h
    exact ⟨h.1, fun As hl => (callsT_adm _).mono n W W' hx v (h.2 As hl)⟩

theorem qLayer_adm (G : NormalGraph ι) : LayerAdm (qLayer G) := by
  intro X _ ηi
  obtain ⟨η, i⟩ := ηi
  unfold qLayer
  by_cases hp : G.params i = true
  · simpa [hp] using (η.2 i).1
  · simp only [hp]
    cases hq : G.schemes i with
    | none => simpa [normalLayer, semList] using
        setSem_adm (fun c => sem_adm (setSem fun l => X (η, l)) c) (G i)
    | some s => exact schemeSem_adm _ _ s

/-- The denotation at every assignment. -/
noncomputable def qDenote (G : NormalGraph ι) : Assignment ι × ι → Fam :=
  Tower.denote (qLayer G)

theorem qDenote_unfold (G : NormalGraph ι) (ηi : Assignment ι × ι)
    (n : Nat) (W : WorldT n) (v : Val) :
    qDenote G ηi n W v ↔ qLayer G (qDenote G) ηi n W v :=
  Tower.denote_unfold (qLayer_congr G) ηi n W v

theorem qDenote_adm (G : NormalGraph ι) (ηi : Assignment ι × ι) : Adm (qDenote G ηi) :=
  Tower.denote_adm (qLayer_congr G) (qLayer_adm G) ηi

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
  simp [qLayer, hi.1, hi.2, normalLayer, NormalGraph.clauses, NormalGraph.plain]

/-- Every label means closed values only, whatever its kind. -/
theorem normalDenote_value {G : NormalGraph ι} {i : ι} {n W v}
    (h : normalDenote G i n W v) : isVal v = true ∧ Scoped 0 v := by
  unfold normalDenote at h
  rw [qDenote_unfold] at h
  unfold qLayer at h
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
    simp [qLayer, hi.1, hi.2]

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

#print axioms normalize_recursive
#print axioms admissible
end Verification.Model.PositiveGraphs
