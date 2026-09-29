import Verification.Model.Types.PositiveRules

/-! Executable certificates for PositiveRules. Completeness concerns existence
of accepted evidence for a declarative derivation, not semantic completeness or
automatic proof search. -/
namespace Verification.Model.PositiveCertificates
open PositiveNormalization PositiveGraphs PositiveRules CallEffects

inductive ArrowCert (ι : Type) where
  | empty
  | source (p : Arrow (List ι))
  /-- A variadic source signature covers the target arrow. -/
  | rest (s : RestArrow (List ι))
  | union (pre : List (List ι)) (a b : List ι) (suffix : List (List ι))
      (left right : ArrowCert ι)
  | combine (b b' : List ι) (effect other : Effect) (left right : ArrowCert ι)
  /-- The target's receiver admits no value: it names no call. -/
  | emptyRecv
  /-- The target's receiver is a union: each part is covered separately. -/
  | recvUnion (a b : List ι) (left right : ArrowCert ι)
  deriving Repr, DecidableEq

def checkDomainsWith (R : List ι → List ι → Prop) [DecidableRel R] : List (List ι) → List (List ι) → Bool
  | [], [] => true
  | a :: As, b :: Bs => decide (R a b) && checkDomainsWith R As Bs
  | _, _ => false

theorem checkDomainsWith_iff {R : List ι → List ι → Prop} [DecidableRel R] (As Bs : List (List ι)) :
    checkDomainsWith R As Bs = true ↔ Domains R As Bs := by
  induction As generalizing Bs with
  | nil => cases Bs <;> simp [checkDomainsWith, Domains]
  | cons a As ih => cases Bs <;> simp [checkDomainsWith, Domains, ih]

instance {elem : List ι → Option (List ι)} {R : List ι → List ι → Prop} [DecidableRel R]
    (As : List (List ι)) (E : List ι) : Decidable (ElemRest elem R As E) := by
  unfold ElemRest; split <;> infer_instance

instance [DecidableEq ι] {elem : List ι → Option (List ι)} {R : List ι → List ι → Prop}
    [DecidableRel R] (As : List (List ι)) (E : List ι) : Decidable (IntoRest elem R As E) := by
  unfold IntoRest; infer_instance

/-- A variadic source signature covering a fixed arrow, decided. -/
def checkRestFixedWith [DecidableEq ι] (G : NormalGraph ι) (R : List ι → List ι → Prop) [DecidableRel R]
    (s : RestArrow (List ι)) (q : Arrow (List ι)) : Bool :=
  decide (R q.receiver s.receiver) &&
    checkDomainsWith R (q.arguments.take s.arguments.1.length) s.arguments.1 &&
    decide (ElemRest (restElem G) (R) (q.arguments.drop s.arguments.1.length) s.arguments.2 ∧
      (s.result = [] ∨ R s.result q.result)) && s.effect.covers q.effect

theorem checkRestFixedWith_iff [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R] {s q} :
    checkRestFixedWith G R s q = true ↔ RestFixed (restElem G) R s q := by
  simp [checkRestFixedWith, RestFixed, checkDomainsWith_iff, and_assoc]

/-- Every recursive premise retains the target contract. Splitting a domain
changes only that domain; combining results states and checks both effects. -/
def checkArrowWith [DecidableEq ι] (G : NormalGraph ι) (R : List ι → List ι → Prop) [DecidableRel R]
    (L : Ops ι) (S : List (RestArrow (List ι))) (q : Arrow (List ι)) : ArrowCert ι → Bool
  | .empty => decide ([] ∈ q.arguments)
  | .emptyRecv => decide (q.receiver = [])
  | .source p => decide (p ∈ L ∧ R q.receiver p.receiver ∧
      (p.result = [] ∨ R p.result q.result)) &&
      checkDomainsWith R q.arguments p.arguments && p.effect.covers q.effect
  | .rest s => decide (s ∈ S) && checkRestFixedWith G R s q
  | .union pre a b suffix left right => decide (q.arguments = pre ++ (a ++ b) :: suffix) &&
      checkArrowWith G R L S { q with arguments := pre ++ a :: suffix } left &&
      checkArrowWith G R L S { q with arguments := pre ++ b :: suffix } right
  | .recvUnion a b left right => decide (q.receiver = a ++ b) &&
      checkArrowWith G R L S { q with receiver := a } left &&
      checkArrowWith G R L S { q with receiver := b } right
  | .combine b b' effect other left right =>
      checkArrowWith G R L S { q with result := b, effect := effect } left &&
      checkArrowWith G R L S { q with result := b', effect := other } right &&
      decide (∀ i ∈ b, ∀ k ∈ b', compatible G i k = true → R [i] q.result) &&
      (effect.meet other).covers q.effect

theorem checkArrowWith_sound [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R] {L S q cert}
    (h : checkArrowWith G R L S q cert = true) :
    CallArrow (compatible G) (restElem G) R L S q := by
  induction cert generalizing q with
  | empty => exact .empty (of_decide_eq_true h)
  | emptyRecv => exact .emptyRecv (of_decide_eq_true h)
  | source p =>
    simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq, checkDomainsWith_iff] at h
    exact .source h.1.1.1 h.1.1.2.1 h.1.2 h.1.1.2.2 h.2
  | rest s =>
    simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq, checkRestFixedWith_iff] at h
    exact .rest h.1 h.2
  | union pre a b suffix left right ih ih' =>
    simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .union h.1.1 (ih h.1.2) (ih' h.2)
  | recvUnion a b left right ih ih' =>
    simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .recvUnion h.1.1 (ih h.1.2) (ih' h.2)
  | combine b b' effect other left right ih ih' =>
    simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .combine (ih h.1.1.1) (ih' h.1.1.2) h.1.2 h.2

theorem checkArrowWith_complete [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R] {L S q}
    (h : CallArrow (compatible G) (restElem G) R L S q) :
    ∃ cert, checkArrowWith G R L S q cert = true := by
  induction h with
  | emptyRecv he => exact ⟨.emptyRecv, by simpa [checkArrowWith] using he⟩
  | empty he => exact ⟨.empty, by simpa [checkArrowWith] using he⟩
  | @source p q hp hrecv hd hc he =>
    exact ⟨.source p, by simp [checkArrowWith, hp, hrecv, hd, hc, he, checkDomainsWith_iff]⟩
  | @rest s q hs hr =>
    exact ⟨.rest s, by simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq,
      checkRestFixedWith_iff]; exact ⟨hs, hr⟩⟩
  | @union pre a b suffix q he ha hb ih ih' =>
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    exact ⟨.union pre a b suffix left right, by simp [checkArrowWith, he, hl, hr]⟩
  | @recvUnion a b q he ha hb ih ih' =>
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    exact ⟨.recvUnion a b left right, by simp [checkArrowWith, he, hl, hr]⟩
  | @combine q b b' e e' ha hb hg he ih ih' =>
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    refine ⟨.combine b b' e e' left right, ?_⟩
    simp only [checkArrowWith, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hl, hr⟩, hg⟩, he⟩

/-- The finite checker reads premises through a table. -/
abbrev checkArrow [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) :=
  checkArrowWith G (Rel table)

theorem checkArrow_sound [DecidableEq ι] {G : NormalGraph ι} {table L S q cert}
    (h : checkArrow G table L S q cert = true) :
    CallArrow (compatible G) (restElem G) (Rel table) L S q := checkArrowWith_sound h

theorem checkArrow_complete [DecidableEq ι] {G : NormalGraph ι} {table L S q}
    (h : CallArrow (compatible G) (restElem G) (Rel table) L S q) :
    ∃ cert, checkArrow G table L S q cert = true := checkArrowWith_complete h

abbrev Evidence (ι : Type) := List (Ops ι × ((Arrow (List ι)) × ArrowCert ι))

instance {R : List ι → List ι → Prop} [DecidableRel R] (a b : Option (List ι)) :
    Decidable (CoversRest R readonly a b) := by
  cases a <;> cases b <;> simp only [CoversRest] <;> infer_instance

instance {R : List ι → List ι → Prop} [DecidableRel R] (p q : Tuple (List ι)) :
    Decidable (CoversShape R p q) := by
  unfold CoversShape; infer_instance

instance {R : List ι → List ι → Prop} [DecidableRel R] (p q : Tuple (List ι)) :
    Decidable (CoversPack R p q) := by
  unfold CoversPack; infer_instance

instance {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R] (p q : Tuple (List ι)) :
    Decidable (CoversTuple G R p q) := by
  unfold CoversTuple; infer_instance

instance {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (p : List (List ι) × List ι) (t : List (List ι) × List ι × List ι) :
    Decidable (FixedCoversPack G R p t) := by
  unfold FixedCoversPack; split <;> infer_instance

instance {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (p : Arrow (List ι)) (t : RestArrow (List ι)) :
    Decidable (FixedCallsPack G R p t) := by
  unfold FixedCallsPack; split <;> infer_instance

/-- Every target arrow has checked evidence from the source's signatures. -/
abbrev ArrowsCheckedWith [DecidableEq ι] (G : NormalGraph ι) (R : List ι → List ι → Prop)
    [DecidableRel R] (proofs : Evidence ι)
    (L : Ops ι) (S : List (RestArrow (List ι))) (M : Ops ι) : Prop :=
  ∀ p ∈ M, ∃ e ∈ proofs, e.1 = L ∧ e.2.1 = p ∧
    checkArrowWith G R L S p e.2.2 = true

/-- Premises read through a table. -/
abbrev ArrowsChecked [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (proofs : Evidence ι) :=
  ArrowsCheckedWith G (Rel table) proofs

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] (G : NormalGraph ι) (R : List ι → List ι → Prop) [DecidableRel R]
    (proofs : Evidence ι) :
    ∀ L S M, Decidable (ArrowsCheckedWith G R proofs L S M) := by
  intro L S M
  unfold ArrowsCheckedWith
  infer_instance

instance {R : List ι → List ι → Prop} [DecidableRel R]
    {elem : List ι → Option (List ι)} [DecidableEq ι] (p q) :
    Decidable (RestCovers elem R p q) := by
  unfold RestCovers; infer_instance

instance {R : List ι → List ι → Prop} [DecidableRel R]
    {elem : List ι → Option (List ι)} [DecidableEq ι] (p q) :
    Decidable (CoversSig elem R p q) := by
  unfold CoversSig; infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (self : List ι) (L S q) : Decidable (CoversArrows G R self L S q) := by
  unfold CoversArrows; infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (s : SchemeRow ι) (S' : List ι) : Decidable (SchemeBinds G R s S') := by
  unfold SchemeBinds; split
  · split <;> infer_instance
  · infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (self F : List ι) (q) : Decidable (CoversByScheme G R self F q) := by
  unfold CoversByScheme; split
  · split <;> infer_instance
  · infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (self F : List ι) (q) : Decidable (CoversByFunction G R self F q) := by
  unfold CoversByFunction; split <;> infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} (P : List ι) (k : PropKey) :
    Decidable (lacksKey G P k) := by
  unfold lacksKey; split <;> infer_instance

instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (known : Known ι) (self : List ι) (q P) : Decidable (FoundOn G R known self q P) := by
  unfold FoundOn; infer_instance

instance instDecidableProtoHolds [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop}
    [DecidableRel R] (known : Known ι) (self : List ι) (q) :
    (d : Nat) → (P : List ι) → Decidable (ProtoHolds G R known self q d P)
  | 0, P => decidable_of_iff (FoundOn G R known self q P) (by rw [ProtoHolds])
  | d + 1, P =>
    have := instDecidableProtoHolds (G := G) (R := R) known self q d
    decidable_of_iff (FoundOn G R known self q P ∨ (lacksKey G P q.key ∧
        ∃ P' ∈ (viewOf G P CallArguments.protoField).toList, ProtoHolds G R known self q d P'))
      (by rw [ProtoHolds])

instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (known : Known ι) (self : List ι) (fields bounds q) :
    Decidable (CoversByProto G R known self fields bounds q) := by
  unfold CoversByProto; infer_instance

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    [∀ L S M, Decidable (arrows L S M)] (self a b) :
    Decidable (CoversWith G R known arrows self a b) := by
  cases a <;> cases b <;> unfold CoversWith <;> infer_instance

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    [∀ L S M, Decidable (arrows L S M)] (i j : ι) :
    Decidable (SchemeCoversWith G R known arrows i j) := by
  unfold SchemeCoversWith; split <;> infer_instance

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] {G : NormalGraph ι} {sc : ι → ι → Prop} [DecidableRel sc]
    {cover : Clause (List ι) → Prop} [DecidablePred cover] (T : List ι) (i : ι) :
    Decidable (MeetOpaque G sc cover T i) := by
  unfold MeetOpaque MeetSource MeetTarget; infer_instance

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    [∀ L S M, Decidable (arrows L S M)] (S T : List ι) :
    Decidable (OpaqueWith G R known arrows S T) := by
  unfold OpaqueWith; infer_instance

set_option synthInstance.maxSize 1024 in
/-- The executable checker is the shared coverage rule interpreted with checked
arrow evidence, premises read through `R`. Adding a coverage condition changes
the checker automatically. -/
def checkClauseWith [DecidableEq ι] (G : NormalGraph ι) (R : List ι → List ι → Prop) [DecidableRel R]
    (known : Known ι) (proofs : Evidence ι) (self : List ι) (a b : Clause (List ι)) : Bool :=
  decide (CoversWith G R known (ArrowsCheckedWith G R proofs) self a b)

theorem checkClauseWith_sound [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop}
    [DecidableRel R] {known proofs self a b}
    (h : checkClauseWith G R known proofs self a b = true) : Covers G R known self a b := by
  apply CoversWith.mono (h := of_decide_eq_true h)
  intro L S M hs p hp
  obtain ⟨e, _, _, _, he⟩ := hs p hp
  exact checkArrowWith_sound he

/-- Finite evidence collection is proof-only; the checker itself makes no
classical choices. Monotonicity allows witnesses to share one evidence list. -/
theorem collect {α β : Type} (xs : List α) (P : α → List β → Prop)
    (mono : ∀ x es es', (∀ e ∈ es, e ∈ es') → P x es → P x es')
    (h : ∀ x ∈ xs, ∃ es, P x es) : ∃ es, ∀ x ∈ xs, P x es := by
  induction xs with
  | nil => exact ⟨[], by simp⟩
  | cons x xs ih =>
    obtain ⟨es, he⟩ := h x (by simp)
    obtain ⟨rest, hr⟩ := ih (fun a ha => h a (by simp [ha]))
    refine ⟨es ++ rest, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with heq | hm
    · subst a; exact mono x es _ (fun e he => List.mem_append_left rest he) he
    · exact mono a rest _ (fun e he => List.mem_append_right es he) (hr a hm)

theorem checkClauseWith_mono [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop}
    [DecidableRel R] {known self a b es es'}
    (hm : ∀ e ∈ es, e ∈ es') (h : checkClauseWith G R known es self a b = true) :
    checkClauseWith G R known es' self a b = true := by
  have h := of_decide_eq_true h
  apply decide_eq_true
  apply CoversWith.mono (h := h)
  intro L S M hs p hp
  obtain ⟨e, he, hL, hP, hc⟩ := hs p hp
  exact ⟨e, hm e he, hL, hP, hc⟩

private theorem arrow_evidence_complete [DecidableEq ι] {G : NormalGraph ι}
    {R : List ι → List ι → Prop} [DecidableRel R] {L M : Ops ι}
    {S : List (RestArrow (List ι))}
    (h : ∀ p ∈ M, CallArrow (compatible G) (restElem G) R L S p) :
    ∃ es : Evidence ι, ∀ p ∈ M, ∃ e ∈ es,
      e.1 = L ∧ e.2.1 = p ∧ checkArrowWith G R L S p e.2.2 = true := by
  have hx : ∀ p ∈ M, ∃ es : Evidence ι, ∃ e ∈ es,
      e.1 = L ∧ e.2.1 = p ∧ checkArrowWith G R L S p e.2.2 = true := by
    intro p hp
    obtain ⟨pc, hc⟩ := checkArrowWith_complete (h p hp)
    exact ⟨[(L, (p, pc))], (L, (p, pc)), by simp, rfl, rfl, hc⟩
  obtain ⟨es, he⟩ := collect M _ (fun p es es' hm ⟨e, he, hL, hp, hc⟩ =>
    ⟨e, hm e he, hL, hp, hc⟩) hx
  exact ⟨es,he⟩

set_option synthInstance.maxSize 1024 in
theorem checkClauseWith_complete [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop}
    [DecidableRel R] {known self a b}
    (h : Covers G R known self a b) : ∃ es, checkClauseWith G R known es self a b = true := by
  simp only [checkClauseWith, decide_eq_true_eq]
  cases a <;> cases b <;> simp only [Covers, CoversWith] at *
  all_goals try contradiction
  all_goals first
    | exact ⟨[], h⟩
    | (obtain ⟨es, he⟩ := arrow_evidence_complete h.1
       exact ⟨es, he, h.2⟩)
    | (obtain ⟨es, he⟩ := arrow_evidence_complete h.2.1
       exact ⟨es, h.1, he, h.2.2⟩)

/-- Premises read through a table. -/
abbrev checkClause [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) :=
  checkClauseWith G (Rel table)

theorem checkClause_sound [DecidableEq ι] {G : NormalGraph ι} {table known proofs self a b}
    (h : checkClause G table known proofs self a b = true) : Covers G (Rel table) known self a b :=
  checkClauseWith_sound h

theorem checkClause_mono [DecidableEq ι] {G : NormalGraph ι} {table known self a b es es'}
    (hm : ∀ e ∈ es, e ∈ es') (h : checkClause G table known es self a b = true) :
    checkClause G table known es' self a b = true := checkClauseWith_mono hm h

theorem checkClause_complete [DecidableEq ι] {G : NormalGraph ι} {table known self a b}
    (h : Covers G (Rel table) known self a b) : ∃ es, checkClause G table known es self a b = true :=
  checkClauseWith_complete h

/-- Checked arrows stay checked with more evidence. -/
theorem arrowsChecked_mono [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop}
    [DecidableRel R] {es es' : Evidence ι} (hm : ∀ e ∈ es, e ∈ es') :
    ∀ L S M, ArrowsCheckedWith G R es L S M → ArrowsCheckedWith G R es' L S M := by
  intro L S M hs p hp
  obtain ⟨e, he, hL, hP, hc⟩ := hs p hp
  exact ⟨e, hm e he, hL, hP, hc⟩

/-- Declarative quantified coverage has checked evidence. -/
theorem schemeCoversWith_complete [DecidableEq ι] {G : NormalGraph ι}
    {R : List ι → List ι → Prop} [DecidableRel R] {known : Known ι} {i j : ι}
    (hc : SchemeCoversWith G R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) i j) :
    ∃ es, SchemeCoversWith G R known (ArrowsCheckedWith G R es) i j := by
  unfold SchemeCoversWith at hc
  split at hc
  · rename_i s s' hs hs'
    obtain ⟨es, he⟩ := checkClauseWith_complete (R := R) (self := []) hc.2.2.2.2
    refine ⟨es, ?_⟩
    simp only [SchemeCoversWith, hs, hs']
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, of_decide_eq_true he⟩
  · exact hc.elim

/-- Declarative quantified coverage up to renaming has checked evidence. -/
theorem schemeCoversAlpha_complete [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} [DecidableRel R] {known : Known ι} {i j : ι}
    (hc : SchemeCoversAlpha G sub R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) i j) :
    ∃ es, SchemeCoversAlpha G sub R known (ArrowsCheckedWith G R es) i j := by
  rcases hc with hc | hc
  · obtain ⟨es, he⟩ := schemeCoversWith_complete hc
    exact ⟨es, .inl he⟩
  · unfold SchemeRenames at hc
    split at hc
    · rename_i r s s' hs hs'
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hc
      obtain ⟨es, he⟩ := checkClauseWith_complete (R := R) (self := []) h9
      refine ⟨es, .inr ?_⟩
      simp only [SchemeRenames, hs, hs']
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, of_decide_eq_true he⟩
    · exact hc.elim

/-- Declarative clause coverage has checked evidence. -/
theorem coversWith_complete [DecidableEq ι] {G : NormalGraph ι}
    {R : List ι → List ι → Prop} [DecidableRel R] {known : Known ι} {T self : List ι}
    {a : Clause (List ι)}
    (hc : ∃ b ∈ clausesOf G T, CoversWith G R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) self a b) :
    ∃ es, ∃ b ∈ clausesOf G T, CoversWith G R known (ArrowsCheckedWith G R es) self a b := by
  obtain ⟨b, hb, hc⟩ := hc
  obtain ⟨es, he⟩ := checkClauseWith_complete (R := R) hc
  exact ⟨es, b, hb, of_decide_eq_true he⟩

/-- An opaque meet read with one relation has evidence for another, given
evidence for each premise the rule reads. -/
theorem MeetOpaque.evidence [DecidableEq ι] {G : NormalGraph ι} {E : Type} {T : List ι} {i : ι}
    {sc : ι → ι → Prop} {cover : Clause (List ι) → Prop}
    {sc' : List E → ι → ι → Prop} {cover' : List E → Clause (List ι) → Prop}
    (msc : ∀ es es', (∀ e ∈ es, e ∈ es') → ∀ a b, sc' es a b → sc' es' a b)
    (mcov : ∀ es es', (∀ e ∈ es, e ∈ es') → ∀ a, cover' es a → cover' es' a)
    (hsc : ∀ a b, sc a b → ∃ es, sc' es a b) (hcov : ∀ a, cover a → ∃ es, cover' es a)
    (h : MeetOpaque G sc cover T i) : ∃ es, MeetOpaque G (sc' es) (cover' es) T i := by
  rcases h with ⟨hm, h | h | ⟨q, hq, hp, j, hj, h⟩ | h⟩ | ⟨j, hj, hm, hq, hcl⟩
  · exact ⟨[], .inl ⟨hm, .inl h⟩⟩
  · exact ⟨[], .inl ⟨hm, .inr (.inl h)⟩⟩
  · obtain ⟨es, he⟩ := hsc q j h
    exact ⟨es, .inl ⟨hm, .inr (.inr (.inl ⟨q, hq, hp, j, hj, he⟩))⟩⟩
  · obtain ⟨es, he⟩ := collect _ (fun a es => cover' es a) (fun a es es' hm h => mcov es es' hm a h)
      (fun a ha => hcov a (h a ha))
    exact ⟨es, .inl ⟨hm, .inr (.inr (.inr he))⟩⟩
  · obtain ⟨es, he⟩ := collect (meetParts G j) (fun q es => G.partRow q = true ∧
        (q = i ∨ (G.meetRow i = true ∧ q ∈ meetParts G i) ∨ sc' es i q ∨
          (G.meetRow i = true ∧ ∃ s ∈ meetParts G i, G.partRow s = true ∧ sc' es s q)))
      (fun q es es' hm ⟨hp, h⟩ => ⟨hp, by
        rcases h with h | h | h | ⟨hi, s, hs, hsp, h⟩
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl (msc es es' hm _ _ h)))
        · exact .inr (.inr (.inr ⟨hi, s, hs, hsp, msc es es' hm _ _ h⟩))⟩)
      (fun q hqm => by
        obtain ⟨hp, h | h | h | ⟨hi, s, hs, hsp, h⟩⟩ := hq q hqm
        · exact ⟨[], hp, .inl h⟩
        · exact ⟨[], hp, .inr (.inl h)⟩
        · obtain ⟨es, he⟩ := hsc i q h
          exact ⟨es, hp, .inr (.inr (.inl he))⟩
        · obtain ⟨es, he⟩ := hsc s q h
          exact ⟨es, hp, .inr (.inr (.inr ⟨hi, s, hs, hsp, he⟩))⟩)
    exact ⟨es, .inr ⟨j, hj, hm, he, hcl⟩⟩

structure Certificate (ι : Type) where
  table : Table ι
  arrows : Evidence ι
  deriving Repr

set_option synthInstance.maxSize 1024 in
def checkCore [DecidableEq ι] (G : NormalGraph ι) (known : Known ι) (S T : List ι)
    (cert : Certificate ι) : Bool :=
  decide ((S, T) ∈ cert.table ∧ ∀ p ∈ cert.table, SameKind G p.1 p.2 = true ∧
    OpaqueWith G (Rel cert.table) known (ArrowsChecked G cert.table cert.arrows) p.1 p.2 ∧
    ∀ a ∈ sourceClauses G p.1 ++ meetSources G p.1 p.2, ∃ b ∈ clausesOf G p.2,
      checkClause G cert.table known cert.arrows p.1 a b = true)


theorem checkCore_sound [DecidableEq ι] {G : NormalGraph ι} {known S T cert}
    (h : checkCore G known S T cert = true) : Core G known S T := by
  simp only [checkCore, decide_eq_true_eq] at h
  refine ⟨cert.table, h.1, ?_⟩
  intro p hp
  refine ⟨(h.2 p hp).1, OpaqueWith.mono (fun L S M hs q hq => ?_) (h.2 p hp).2.1, fun a ha => ?_⟩
  · obtain ⟨e, _, _, _, he⟩ := hs q hq
    exact checkArrow_sound he
  obtain ⟨b, hb, hc⟩ := (h.2 p hp).2.2 a ha
  exact ⟨b, hb, checkClause_sound hc⟩

/-- Opaque rows checked with one evidence list stay checked with a larger one. -/
theorem opaque_mono [DecidableEq ι] {G : NormalGraph ι} {table known S T es es'}
    (hm : ∀ e ∈ es, e ∈ es')
    (h : OpaqueWith G (Rel table) known (ArrowsChecked G table es) S T) :
    OpaqueWith G (Rel table) known (ArrowsChecked G table es') S T :=
  OpaqueWith.mono (fun L S M hs p hp => by
    obtain ⟨e, he, hL, hP, hc⟩ := hs p hp
    exact ⟨e, hm e he, hL, hP, hc⟩) h

set_option synthInstance.maxSize 1024 in
/-- Declarative opaque rows have checked evidence: each quantified signature
coverage is an arrow coverage, whose evidence `checkClause_complete` finds. -/
theorem opaque_complete [DecidableEq ι] {G : NormalGraph ι} {table known S T}
    (h : Opaque G (Rel table) known S T) :
    ∃ es, OpaqueWith G (Rel table) known (ArrowsChecked G table es) S T := by
  have each : ∀ i ∈ S, ∃ es : Evidence ι, G.plain i = true ∨ i ∈ T ∨ .top ∈ clausesOf G T ∨
      MeetOpaque G (SchemeCoversWith G (Rel table) known (ArrowsChecked G table es))
        (fun a => ∃ b ∈ clausesOf G T, CoversWith G (Rel table) known (ArrowsChecked G table es) S a b) T i ∨
      ∃ j ∈ T, SchemeCoversWith G (Rel table) known (ArrowsChecked G table es) i j := by
    intro i hi
    rcases h i hi with h | h | h | h | ⟨j, hj, hc⟩
    · exact ⟨[], .inl h⟩
    · exact ⟨[], .inr (.inl h)⟩
    · exact ⟨[], .inr (.inr (.inl h))⟩
    · obtain ⟨es, he⟩ := MeetOpaque.evidence (h := h)
        (sc' := fun es => SchemeCoversWith G (Rel table) known (ArrowsChecked G table es))
        (cover' := fun es a => ∃ b ∈ clausesOf G T,
          CoversWith G (Rel table) known (ArrowsChecked G table es) S a b)
        (fun es es' hm a b h => SchemeCoversWith.mono (arrowsChecked_mono hm) h)
        (fun es es' hm a ⟨b, hb, hc⟩ => ⟨b, hb, CoversWith.mono (arrowsChecked_mono hm) hc⟩)
        (fun a b h => schemeCoversWith_complete h) (fun a h => coversWith_complete h)
      exact ⟨es, .inr (.inr (.inr (.inl he)))⟩
    · unfold SchemeCoversWith at hc
      split at hc
      · rename_i s s' hs hs'
        obtain ⟨es, he⟩ := checkClause_complete (self := []) hc.2.2.2.2
        refine ⟨es, .inr (.inr (.inr (.inr ⟨j, hj, ?_⟩)))⟩
        simp only [SchemeCoversWith, hs, hs']
        exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, of_decide_eq_true he⟩
      · exact hc.elim
  obtain ⟨es, he⟩ := collect S _ (fun i es es' hm h => by
    rcases h with h | h | h | h | ⟨j, hj, hc⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl (h.mono (fun _ _ => SchemeCoversWith.mono (arrowsChecked_mono hm))
        fun a ⟨b, hb, hc⟩ => ⟨b, hb, CoversWith.mono (arrowsChecked_mono hm) hc⟩))))
    · refine .inr (.inr (.inr (.inr ⟨j, hj, ?_⟩)))
      unfold SchemeCoversWith at hc ⊢
      split at hc
      · exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, of_decide_eq_true
          (checkClause_mono hm (decide_eq_true hc.2.2.2.2))⟩
      · exact hc.elim) each
  exact ⟨es, fun i hi => he i hi⟩

theorem checkCore_complete [DecidableEq ι] {G : NormalGraph ι} {known S T}
    (h : Core G known S T) : ∃ cert, checkCore G known S T cert = true := by
  obtain ⟨table, hm, hv⟩ := h
  have rows : ∀ p ∈ table, ∃ es : Evidence ι,
      OpaqueWith G (Rel table) known (ArrowsChecked G table es) p.1 p.2 ∧
      ∀ a ∈ sourceClauses G p.1 ++ meetSources G p.1 p.2, ∃ b ∈ clausesOf G p.2,
        checkClause G table known es p.1 a b = true := by
    intro p hp
    obtain ⟨es₀, ho⟩ := opaque_complete (hv p hp).2.1
    obtain ⟨es₁, hc⟩ := collect (sourceClauses G p.1 ++ meetSources G p.1 p.2)
      (fun a es => ∃ b ∈ clausesOf G p.2, checkClause G table known es p.1 a b = true)
      (fun a es es' hm ⟨b, hb, hc⟩ => ⟨b, hb, checkClause_mono hm hc⟩)
      (fun a ha => by
        obtain ⟨b, hb, hc⟩ := (hv p hp).2.2 a ha
        obtain ⟨es, he⟩ := checkClause_complete hc
        exact ⟨es, b, hb, he⟩)
    refine ⟨es₀ ++ es₁, opaque_mono (fun e he => List.mem_append_left _ he) ho, fun a ha => ?_⟩
    obtain ⟨b, hb, hc⟩ := hc a ha
    exact ⟨b, hb, checkClause_mono (fun e he => List.mem_append_right _ he) hc⟩
  obtain ⟨es, he⟩ := collect table _ (fun p es es' hm h => by
    refine ⟨opaque_mono hm h.1, fun a ha => ?_⟩
    obtain ⟨b, hb, hc⟩ := h.2 a ha
    exact ⟨b, hb, checkClause_mono hm hc⟩) rows
  exact ⟨⟨table, es⟩, by
    simp only [checkCore, decide_eq_true_eq]
    exact ⟨hm, fun p hp => ⟨(hv p hp).1, (he p hp).1, (he p hp).2⟩⟩⟩

/-- A checked instance of a scheme row's signatures: the instance table, the
types the binders are instantiated at, a certificate per bound, the table's
domain and the domain's free parameter rows. -/
structure Instance (ι : Type) where
  table : InstTable ι
  instances : List (List ι)
  bounds : List (Option (Certificate ι))
  domain : List ι
  free : FreeMap ι
  deriving Repr

inductive Proof (ι : Type) where
  /-- A checked table, and the instances its coverage uses as known rows:
  each a scheme row, the arrows it is below and the instance proving it. -/
  | core (certificate : Certificate ι)
      (instances : List (List ι × Ops ι × List (RestArrow (List ι)) ×
        Instance ι) := [])
  | subset
  | trans (middle : List ι) (left right : Proof ι)
  /-- A scheme row below a checked instance of its signatures. -/
  | inst (inst : Instance ι)
  /-- A type below one holding its rows' images under an instance table with
  the empty context: the table, its domain and its free-variable certificate. -/
  | table (table : InstTable ι) (domain : List ι) (free : FreeMap ι)
  /-- A type below a scheme: a domain holding it, the domain's free parameter
  rows, none of them a binder of the type, the type stating the scheme's
  signatures with its binders opaque, and the proof of the inclusion in it. -/
  | gen (domain : List ι) (free : FreeMap ι) (body : List ι) (proof : Proof ι)
  deriving Repr

/-- The syntactic conditions of `Sub.gen`, other than its subproof. -/
def genOk [DecidableEq ι] (G : NormalGraph ι) (S T D : List ι) (V : FreeMap ι) (U : List ι) :
    Bool :=
  match T with
  | [j] =>
    match G.schemes j with
    | some s => !G.params j && expand G U == [.arrs s.signatures s.variadic] && FreeOk G D V &&
        S.all (fun l => decide (l ∈ D ∧ ∀ p ∈ fv V l, p ∉ s.binders))
    | none => false
  | _ => false

theorem genOk_sound [DecidableEq ι] {G : NormalGraph ι} {S T D V U}
    (h : genOk G S T D V U = true) (hs : Sub G S U) : Sub G S T := by
  unfold genOk at h
  split at h
  · rename_i j
    split at h
    · rename_i s hq
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
        decide_eq_true_eq] at h
      exact .gen h.1.1.1 hq h.1.1.2 h.1.2 h.2 hs
    · cases h
  · cases h

/-- An instance type within one bound: plain inclusion (no certificate) or a
core certificate. A bound whose binder has no instance is vacuous. -/
def boundOk [DecidableEq ι] (G : NormalGraph ι) (binders : List ι) (θs : List (List ι))
    (b : ι × List ι) (c : Option (Certificate ι)) : Bool :=
  match (binders.zip θs).lookup b.1 with
  | none => true
  | some U => match c with
    | none => decide (∀ l ∈ U, l ∈ b.2)
    | some cert => checkCore G [] U b.2 cert

theorem boundOk_sound [DecidableEq ι] {G : NormalGraph ι} {binders θs b c}
    (h : boundOk G binders θs b c = true) :
    ∀ U, (binders.zip θs).lookup b.1 = some U → Core G [] U b.2 ∨ ∀ l ∈ U, l ∈ b.2 := by
  intro U hU
  unfold boundOk at h
  rw [hU] at h
  cases c with
  | none => exact .inr (by simpa using h)
  | some cert => exact .inl (checkCore_sound h)

theorem exists_mem_zip {xs : List α} {ys : List β} (hl : ys.length = xs.length) :
    ∀ x ∈ xs, ∃ y, (x, y) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => intro x hx; cases hx
  | cons a xs ih =>
    cases ys with
    | nil => simp at hl
    | cons b ys =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, by simp⟩
      · obtain ⟨y, hy⟩ := ih (by simpa using hl) x hx
        exact ⟨y, by simp [hy]⟩

theorem bound_certs [DecidableEq ι] {G : NormalGraph ι} {binders : List ι} {θs : List (List ι)} :
    ∀ bs : List (ι × List ι), (∀ b ∈ bs, ∀ U, (binders.zip θs).lookup b.1 = some U →
      Core G [] U b.2 ∨ ∀ l ∈ U, l ∈ b.2) →
    ∃ certs : List (Option (Certificate ι)), certs.length = bs.length ∧
      (bs.zip certs).all (fun bc => boundOk G binders θs bc.1 bc.2) = true
  | [], _ => ⟨[], rfl, rfl⟩
  | b :: bs, h => by
    obtain ⟨certs, hl, hall⟩ := bound_certs bs fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    have : ∃ c, boundOk G binders θs b c = true := by
      cases hk : (binders.zip θs).lookup b.1 with
      | none => exact ⟨none, by simp [boundOk, hk]⟩
      | some U =>
        rcases h b List.mem_cons_self U hk with hc | hsub
        · obtain ⟨cert, hcert⟩ := checkCore_complete hc
          exact ⟨some cert, by simp [boundOk, hk, hcert]⟩
        · exact ⟨none, by simpa [boundOk, hk] using hsub⟩
    obtain ⟨c, hc⟩ := this
    exact ⟨c :: certs, by simp [hl], by simp [hc, hall]⟩

/-- The representation-specific image check, with its semantic obligation.
The checker is supplied by verified code, not read from a certificate. Bound,
kind, signature and effect checks remain in the shared instance checker. -/
structure InstanceImageCheck [DecidableEq ι] (G : NormalGraph ι) where
  check : List ι → Instance ι → Bool
  sound : ∀ bs c, c.instances.length = bs.length → instKinds G bs c.instances = true →
    check bs c = true → ∀ η, InstanceImages G η bs c.instances c.table

/-- The original finite closed-table implementation. -/
def finiteInstanceImages [DecidableEq ι] (G : NormalGraph ι) : InstanceImageCheck G where
  check := fun _ c => TableOk G c.table c.domain c.free
  sound := fun _ _ hlen hkinds hok η => table_instanceImages η hlen hkinds hok

/-- The same check at a reassignment of the graph's parameter rows. Its
obligation quantifies over every assignment and reads no `env`, so one proof
serves every reassignment (`Parametricity`). -/
def InstanceImageCheck.reassign [DecidableEq ι] {G : NormalGraph ι} (images : InstanceImageCheck G)
    (η : MixedAssignment ι) : InstanceImageCheck (PositiveRules.reassign G η) where
  check := images.check
  sound := images.sound

/-- `S` is one scheme row, and `L`, `M` arrows whose every signature is an
image of one of the scheme's under the instance table, each instance within
its binder's bounds. Only validation of that image table depends on its
representation; every other obligation is shared. -/
def checkInstArrsUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (S : List ι) (L : Ops ι) (M : List (RestArrow (List ι))) (c : Instance ι) : Bool :=
  match S with
  | [i] =>
    match G.schemes i with
    | some s => !G.params i && c.instances.length == s.binders.length &&
        instKinds G s.binders c.instances &&
        c.bounds.length == s.bounds.length &&
        (s.bounds.zip c.bounds).all (fun bc => boundOk G s.binders c.instances bc.1 bc.2) &&
        images.check s.binders c &&
        (L.all fun q => s.signatures.any fun p => instSig G c.table (s.binders.zip c.instances) p q) &&
        M.all fun q => s.variadic.any fun p => instRest G c.table (s.binders.zip c.instances) p q
    | none => false
  | _ => false

/-- Keep the finite checker as the existing default, with identical checks. -/
def checkInstArrs [DecidableEq ι] (G : NormalGraph ι) (S : List ι) (L : Ops ι)
    (M : List (RestArrow (List ι))) (c : Instance ι) : Bool :=
  checkInstArrsUsing G (finiteInstanceImages G) S L M c

/-- Every representation discharges the same semantic elimination rule. -/
theorem checkInstArrsUsing_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {S L M c}
    (h : checkInstArrsUsing G images S L M c = true) :
    ∀ η, FamLe (mixedValues G η S) (mixedSem G η (.arrs L M)) := by
  unfold checkInstArrsUsing at h
  split at h
  · rename_i i
    split at h
    · rename_i s hs
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_true,
        beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hp, hlen⟩, hkinds⟩, hcl⟩, hbs⟩, hok⟩, hL⟩, hM⟩ := h
      intro η n W v hv
      refine ⟨inst_images_sound η hp hs hlen ?_
        (images.sound s.binders c hlen hkinds hok η) hL hM n W v hv,
        realmInvariant_of_not_record rfl n W v⟩
      intro b hb U hU
      obtain ⟨cert, hc⟩ := exists_mem_zip hcl b hb
      rcases boundOk_sound (hbs _ hc) U hU with hcore | hsubset
      · exact Core.mixed_sound hcore (fun _ => by simp) η
      · exact (Sub.subset hsubset).mixed_sound η
    · cases h
  · cases h

theorem checkInstArrs_sound [DecidableEq ι] {G : NormalGraph ι} {S L M c}
    (h : checkInstArrs G S L M c = true) : InstArrs G S L M := by
  obtain ⟨tbl, θs, certs, D, V⟩ := c
  unfold checkInstArrs checkInstArrsUsing finiteInstanceImages at h
  split at h
  · rename_i i
    split at h
    · rename_i s hs
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_true,
        beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hp, hlen⟩, hkinds⟩, hcl⟩, hbs⟩, hok⟩, hL⟩, hM⟩ := h
      refine ⟨i, s, tbl, θs, D, V, rfl, hp, hs, hlen, hkinds, fun b hb => ?_, hok, hL, hM⟩
      obtain ⟨c, hc⟩ := exists_mem_zip hcl b hb
      exact boundOk_sound (hbs _ hc)
    · cases h
  · cases h

theorem checkInstArrs_complete [DecidableEq ι] {G : NormalGraph ι} {S L M}
    (h : InstArrs G S L M) : ∃ c, checkInstArrs G S L M c = true := by
  obtain ⟨i, s, tbl, θs, D, V, rfl, hp, hq, hlen, hkinds, hbnd, hok, hL, hM⟩ := h
  obtain ⟨certs, hcl, hcs⟩ := bound_certs s.bounds hbnd
  refine ⟨⟨tbl, θs, certs, D, V⟩, ?_⟩
  simp only [checkInstArrs, checkInstArrsUsing, finiteInstanceImages, hq, hp, hok, hlen, hkinds,
    hcl, hcs, Bool.not_false, Bool.true_and, beq_self_eq_true, List.all_eq_true,
    List.any_eq_true, Bool.and_eq_true]
  exact ⟨fun q hq => hL q hq, fun q hq => hM q hq⟩

/-- The shared instance rule against an explicit target arrow type. -/
def checkInstUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (S T : List ι) (c : Instance ι) : Bool :=
  match expand G T with
  | [.arrs L M] => checkInstArrsUsing G images S L M c
  | _ => false

theorem checkInstUsing_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {S T c}
    (h : checkInstUsing G images S T c = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  unfold checkInstUsing at h
  split at h
  · rename_i L M hT
    have values := checkInstArrsUsing_sound h
    unfold checkInstArrsUsing at h
    split at h
    · rename_i i
      split at h
      · rename_i s hs
        have hp : G.params i = false := by
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
          exact h.1.1.1.1.1.1.1
        intro η n W x hx
        cases x with
        | inl v => exact mixed_of_expand hT (values η n W v hx)
        | inr vs =>
          have hk : G.parameterKinds i = none := by simpa [NormalGraph.params] using hp
          have hc : G i = [] := by simp [NormalGraph.clauses, NormalGraph.plain, hs]
          simp [mixedMeaning, mixedParameters, graphArguments, hk, hc] at hx
      · cases h
    · cases h
  · cases h

/-- `T` is one arrow clause, an instance of the scheme row `S`. -/
def checkInst [DecidableEq ι] (G : NormalGraph ι) (S T : List ι) (c : Instance ι) : Bool :=
  checkInstUsing G (finiteInstanceImages G) S T c

theorem checkInst_sound [DecidableEq ι] {G : NormalGraph ι} {S T c}
    (h : checkInst G S T c = true) : Inst G S T := by
  unfold checkInst checkInstUsing at h
  split at h
  · rename_i L M hT
    exact ⟨L, M, checkInstArrs_sound h, hT⟩
  · cases h

theorem checkInst_complete [DecidableEq ι] {G : NormalGraph ι} {S T}
    (h : Inst G S T) : ∃ c, checkInst G S T c = true := by
  obtain ⟨L, M, hi, hT⟩ := h
  obtain ⟨c, hc⟩ := checkInstArrs_complete hi
  change checkInstArrsUsing G (finiteInstanceImages G) S L M c = true at hc
  exact ⟨c, by simp only [checkInst, checkInstUsing, hT, hc]⟩

/-- The rows a core certificate's instances prove. -/
def knownOf (ks : List (List ι × Ops ι × List (RestArrow (List ι)) × Instance ι)) :
    Known ι := ks.map fun k => (k.1, k.2.1, k.2.2.1)

theorem instances_complete [DecidableEq ι] {G : NormalGraph ι} :
    ∀ known : Known ι, (∀ k ∈ known, InstArrs G k.1 k.2.1 k.2.2) →
      ∃ ks, knownOf ks = known ∧
        ks.all (fun k => checkInstArrs G k.1 k.2.1 k.2.2.1 k.2.2.2) = true
  | [], _ => ⟨[], rfl, rfl⟩
  | k :: known, h => by
    obtain ⟨ks, hr, ha⟩ := instances_complete known fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨c, hc⟩ := checkInstArrs_complete (h k List.mem_cons_self)
    exact ⟨(k.1, k.2.1, k.2.2, c) :: ks, by simp [knownOf] at hr ⊢; exact hr, by simp [hc, ha]⟩

/-- One proof traversal for every proved image-check implementation. Other
rules retain their original checks, including closure and free-variable checks. -/
def checkUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (S T : List ι) : Proof ι → Bool
  | .core cert ks => checkCore G (knownOf ks) S T cert &&
      ks.all fun k => checkInstArrsUsing G images k.1 k.2.1 k.2.2.1 k.2.2.2
  | .subset => decide (∀ i ∈ S, i ∈ T)
  | .trans middle left right => checkUsing G images S middle left && checkUsing G images middle T right
  | .inst c => checkInstUsing G images S T c
  | .gen D V U p => genOk G S T D V U && checkUsing G images S U p
  | .table tbl D V => TableOk G tbl D V &&
      S.all fun l => match entryImg tbl [] l with
        | some U => U.all (· ∈ T)
        | none => false

/-- Existing certificates use the finite image checker. -/
def check [DecidableEq ι] (G : NormalGraph ι) (S T : List ι) (proof : Proof ι) : Bool :=
  checkUsing G (finiteInstanceImages G) S T proof

/-- The shared proof traversal is sound for any proved image checker. This is
semantic soundness; completeness for the original finite declarative rules is
still stated separately by `derivable_iff_checked`. -/
theorem checkUsing_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {S T proof}
    (h : checkUsing G images S T proof = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  induction proof generalizing S T with
  | core cert ks =>
    simp only [checkUsing, Bool.and_eq_true, List.all_eq_true] at h
    apply Core.mixed_sound (checkCore_sound h.1)
    intro η k hk
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hk
    exact checkInstArrsUsing_sound (h.2 q hq) η
  | subset => exact (Sub.subset (of_decide_eq_true h)).mixed_sound
  | trans middle left right ih ih' =>
    simp only [checkUsing, Bool.and_eq_true] at h
    exact fun η n W x hx => ih' h.2 η n W x (ih h.1 η n W x hx)
  | inst c => exact checkInstUsing_sound h
  | gen D V U p ih =>
    simp only [checkUsing, Bool.and_eq_true] at h
    have body := ih h.2
    have valid := h.1
    unfold genOk at valid
    split at valid
    · rename_i j
      split at valid
      · rename_i s hq
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
          decide_eq_true_eq] at valid
        exact gen_mixed_sound valid.1.1.1 hq valid.1.1.2 valid.1.2 valid.2 body
      · cases valid
    · cases valid
  | table tbl D V =>
    simp only [checkUsing, Bool.and_eq_true, List.all_eq_true] at h
    apply (Sub.table h.1 ?_).mixed_sound
    intro l hl
    have hl' := h.2 l hl
    cases hU : entryImg tbl [] l with
    | none => simp [hU] at hl'
    | some U =>
      simp only [hU, List.all_eq_true, decide_eq_true_eq] at hl'
      exact ⟨U, rfl, hl'⟩

theorem check_sound [DecidableEq ι] {G : NormalGraph ι} {S T proof}
    (h : check G S T proof = true) : Sub G S T := by
  induction proof generalizing S T with
  | core cert ks =>
    simp only [check, checkUsing, Bool.and_eq_true, List.all_eq_true] at h
    refine .core (fun p hp => ?_) (checkCore_sound h.1)
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact checkInstArrs_sound (h.2 k hk)
  | subset => exact .subset (of_decide_eq_true h)
  | trans middle left right ih ih' =>
    simp only [check, checkUsing, Bool.and_eq_true] at h
    exact .trans (ih h.1) (ih' h.2)
  | inst c => exact .inst (checkInst_sound h)
  | gen D V U p ih =>
    simp only [check, checkUsing, Bool.and_eq_true] at h
    exact genOk_sound h.1 (ih h.2)
  | table tbl D V =>
    simp only [check, checkUsing, Bool.and_eq_true, List.all_eq_true] at h
    refine .table h.1 fun l hl => ?_
    have hl' := h.2 l hl
    cases hU : entryImg tbl [] l with
    | none => simp [hU] at hl'
    | some U =>
      simp only [hU, List.all_eq_true, decide_eq_true_eq] at hl'
      exact ⟨U, rfl, hl'⟩

theorem check_complete [dec : DecidableEq ι] {G : NormalGraph ι} {S T}
    (h : Sub G S T) : ∃ proof, check G S T proof = true := by
  induction h with
  | @core S T inst known hk h =>
    have he : inst = dec := Subsingleton.elim _ _
    subst he
    obtain ⟨ks, hr, ha⟩ := instances_complete known hk
    simp only [checkInstArrs] at ha
    obtain ⟨cert, hc⟩ := checkCore_complete h
    exact ⟨.core cert ks, by simp only [check, checkUsing, hr, hc, ha, Bool.and_self]⟩
  | subset h => exact ⟨.subset, by simpa only [check, checkUsing, decide_eq_true_eq] using h⟩
  | trans h1 h2 ih ih' =>
    rename_i S U T
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    simp only [check] at hl hr
    exact ⟨.trans U left right, by simp [check, checkUsing, hl, hr]⟩
  | @inst S T inst h =>
    have he : inst = dec := Subsingleton.elim _ _
    subst he
    obtain ⟨c, hc⟩ := checkInst_complete h
    exact ⟨.inst c, hc⟩
  | @table S T inst tbl D V hok hS =>
    have he : inst = dec := Subsingleton.elim _ _
    subst he
    refine ⟨.table tbl D V, ?_⟩
    simp only [check, checkUsing, hok, Bool.true_and, List.all_eq_true]
    intro l hl
    obtain ⟨U, hU, hUT⟩ := hS l hl
    simp only [hU, List.all_eq_true, decide_eq_true_eq]
    exact hUT
  | @gen S inst j s D U V hp hq hU hF hS _ ih =>
    have he : inst = dec := Subsingleton.elim _ _
    subst he
    obtain ⟨p, hpc⟩ := ih
    simp only [check] at hpc
    refine ⟨.gen D V U p, ?_⟩
    simp only [check, checkUsing, genOk, hq, hp, hU, hF, hpc, Bool.not_false, Bool.true_and, Bool.and_true,
      beq_self_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact hS

/-- Certificate completeness for the independent declarative rules. No claim
of completeness with respect to arbitrary semantic inclusion is made. -/
theorem derivable_iff_checked [DecidableEq ι] {G : NormalGraph ι} {S T} :
    Sub G S T ↔ ∃ proof, check G S T proof = true :=
  ⟨check_complete, fun ⟨_, h⟩ => check_sound h⟩

/-- A proved image checker supplies ordinary value subsumption as well as
mixed inclusion. Program typing uses this interface. -/
theorem acceptedUsing [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {S T proof}
    (h : checkUsing G images S T proof = true) : FamLe (meaning G S) (meaning G T) :=
  fun n W v hv => checkUsing_sound h G.env n W (.inl v) hv

/-- A formula graph is checked through its normalization. -/
def checkSource [DecidableEq ι] (G : PositiveGraphs.Graph ι) (S T : List ι)
    (proof : Proof ι) : Bool := check (normalizeGraph G) S T proof

theorem accepted [DecidableEq ι] {G : NormalGraph ι} {S T proof}
    (h : check G S T proof = true) : FamLe (meaning G S) (meaning G T) :=
  (check_sound h).sound

theorem accepted_subsumption [DecidableEq ι] {G : NormalGraph ι} {S T proof}
    (h : check G S T proof = true) (n : Nat) (W : WorldT n) (heap : Heap) (t : Tm)
    (hs : Safe (meaning G S) n W heap t) : Safe (meaning G T) n W heap t := by
  apply Safe_mono n _ W heap t hs
  intro j _ U v hv
  exact accepted h j U v hv

/-! ## Family certificates

Family entries (RECURSIVE-EQUATIONS §4.2) are checked by the core
conditions with premises read in each entry, decided with checked arrow
evidence. The premise judgment is decided by `premB`, recursion on a size
that `Inst`'s premises decrease (`prem_iff`). The checker is complete for
the declarative rule (`familyValid_iff_checked`); a claim is a pair of a
variable-free entry (`checkFamilyUsing_sound`). -/

instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {e : Entry ι}
    {l : ι} {B : List ι} {xs : List (List ι)} : Decidable (InstanceAt G sub e l B xs) := by
  unfold InstanceAt; infer_instance

/-- `Mem`, `Hyp` and `MeetHyp`, decided. -/
def premBase [DecidableEq ι] (G : NormalGraph ι) (f : Entry ι) (l : ι) (B : List ι) : Bool :=
  decide (l ∈ B) || f.hypotheses.any (fun h => decide (h.1 = l) && decide (h.2 ∈ B)) ||
    (G.meetRow l && B.any fun y => meetBelow G l y f.hypotheses)

/-- `Tab` and `TabRen`, decided: the renaming is the representation's own
proposal, checked. -/
def premTable [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (f : Entry ι)
    (A B : List ι) : Bool :=
  decide ((A, B) ∈ f.table) || match sub with
    | some r => f.table.any fun p => decide (RenamesBound G r (r.rename p A B)) &&
        A.all (fun l => decide (l ∈ r.substitute (r.rename p A B) p.1)) &&
        (r.substitute (r.rename p A B) p.2).all (fun b => decide (b ∈ B))
    | none => false

/-- `Inst` at the instance `w`, its hypotheses decided by `prem` on strictly
smaller types. -/
def instanceB [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (look : Lookup ι)
    (prem : List ι → List ι → Bool) (l : ι) (B : List ι) (w : Nat × List (List ι)) : Bool :=
  match look w.1 with
  | some e => decide (InstanceAt G sub e l B w.2) && e.hypotheses.all fun h =>
      decide (typeSize sub (replace (e.variables.zip w.2) h.1) +
        typeSize sub (replace (e.variables.zip w.2) h.2) < labelSize sub l + typeSize sub B) &&
      prem (replace (e.variables.zip w.2) h.1) (replace (e.variables.zip w.2) h.2)
  | none => false

/-- A label's premise, decided with `k` levels of nested instances. -/
def premLabelB [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (look : Lookup ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (f : Entry ι) : Nat → ι → List ι → Bool
  | 0, l, B => premBase G f l B
  | k + 1, l, B => premBase G f l B || (f.instances ++ gen l B).any fun w =>
      instanceB G sub look (fun X Y => premTable G sub f X Y || X.all fun l' =>
        premLabelB G sub look gen f k l' Y) l B w

/-- A premise, decided with `k` levels of nested instances. -/
def premB [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (look : Lookup ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (f : Entry ι) (k : Nat) (A B : List ι) : Bool :=
  premTable G sub f A B || A.all fun l => premLabelB G sub look gen f k l B

theorem premLabelB_succ [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} {k : Nat}
    {l : ι} {B : List ι} :
    premLabelB G sub look gen f (k + 1) l B = (premBase G f l B || (f.instances ++ gen l B).any
      fun w => instanceB G sub look (premB G sub look gen f k) l B w) := rfl

theorem premBase_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι}
    {l : ι} {B : List ι} (h : premBase G f l B = true) : PremLabel G sub look gen f l B := by
  simp only [premBase, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with (h | ⟨q, hq, rfl, hy⟩) | ⟨hm, y, hy, hb⟩
  · exact .mem h
  · exact .hyp hq hy
  · exact .meetHyp hm hy hb

theorem premTable_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι}
    {A B : List ι} (h : premTable G sub f A B = true) : Prem G sub look gen f A B := by
  unfold premTable at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · exact .tab h
  · cases sub with
    | none => cases h
    | some r =>
      simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
      obtain ⟨p, hp, ⟨hren, hA⟩, hB⟩ := h
      exact .tabRen r p rfl hp hren hA hB

theorem prem_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} :
    ∀ k, (∀ l B, premLabelB G sub look gen f k l B = true → PremLabel G sub look gen f l B) ∧
      ∀ A B, premB G sub look gen f k A B = true → Prem G sub look gen f A B := by
  intro k
  induction k with
  | zero =>
    have hl : ∀ l B, premLabelB G sub look gen f 0 l B = true → PremLabel G sub look gen f l B :=
      fun l B h => premBase_sound h
    refine ⟨hl, fun A B h => ?_⟩
    simp only [premB, Bool.or_eq_true, List.all_eq_true] at h
    rcases h with h | h
    · exact premTable_sound h
    · exact .union fun l hl' => hl l B (h l hl')
  | succ k ih =>
    have hl : ∀ l B, premLabelB G sub look gen f (k + 1) l B = true →
        PremLabel G sub look gen f l B := by
      intro l B h
      rw [premLabelB_succ] at h
      simp only [Bool.or_eq_true, List.any_eq_true] at h
      rcases h with h | ⟨w, hw, h⟩
      · exact premBase_sound h
      · unfold instanceB at h
        split at h
        · rename_i e he
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
          obtain ⟨hi, hh⟩ := h
          exact .inst w e hw he hi (fun h' hh' => (hh h' hh').1)
            (fun h' hh' => ih.2 _ _ (hh h' hh').2)
        · cases h
    refine ⟨hl, fun A B h => ?_⟩
    simp only [premB, Bool.or_eq_true, List.all_eq_true] at h
    rcases h with h | h
    · exact premTable_sound h
    · exact .union fun l hl' => hl l B (h l hl')

theorem le_typeSize [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {l : ι} :
    ∀ {A : List ι}, l ∈ A → labelSize sub l ≤ typeSize sub A
  | a :: A, h => by
    simp only [typeSize, List.map_cons, List.sum_cons] at *
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_typeSize (sub := sub) h
      simp only [typeSize] at this
      omega

theorem premBase_of_label [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι}
    {l : ι} {B : List ι} (h : premBase G f l B = true) :
    ∀ k, premLabelB G sub look gen f k l B = true
  | 0 => h
  | _ + 1 => by rw [premLabelB_succ, h, Bool.true_or]

/-- **Completeness of the decision.** A derivation fits the size of its
conclusion: each `Inst` decreases it. -/
theorem prem_complete [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} :
    (∀ {A B}, Prem G sub look gen f A B →
      ∀ k, typeSize sub A + typeSize sub B < k → premB G sub look gen f k A B = true) ∧
    ∀ {l B}, PremLabel G sub look gen f l B →
      ∀ k, labelSize sub l + typeSize sub B < k → premLabelB G sub look gen f k l B = true := by
  let motive_1 := fun (A B : List ι) (_ : Prem G sub look gen f A B) =>
    ∀ k, typeSize sub A + typeSize sub B < k → premB G sub look gen f k A B = true
  let motive_2 := fun (l : ι) (B : List ι) (_ : PremLabel G sub look gen f l B) =>
    ∀ k, labelSize sub l + typeSize sub B < k → premLabelB G sub look gen f k l B = true
  have tab : ∀ {A B} (h : (A, B) ∈ f.table), motive_1 A B (.tab h) := fun h k _ => by
    simp [premB, premTable, h]
  have ren : ∀ {A B} r p hs hp hren hA hB, motive_1 A B (.tabRen r p hs hp hren hA hB) := by
    intro A B r p hs hp hren hA hB k _
    subst hs
    have : premTable G (some r) f A B = true := by
      simp only [premTable, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true]
      exact .inr ⟨p, hp, ⟨hren, hA⟩, hB⟩
    simp [premB, this]
  have union : ∀ {A B} (h : ∀ l ∈ A, PremLabel G sub look gen f l B),
      (∀ l hl, motive_2 l B (h l hl)) → motive_1 A B (.union h) := by
    intro A B _ ih k hk
    simp only [premB, Bool.or_eq_true, List.all_eq_true]
    exact .inr fun l hl => ih l hl k (by have := le_typeSize (sub := sub) hl; omega)
  have mem : ∀ {l B} (h : l ∈ B), motive_2 l B (.mem h) := fun h k _ =>
    premBase_of_label (by simp [premBase, h]) k
  have hyp : ∀ {l y B} (hh : (l, y) ∈ f.hypotheses) (hy : y ∈ B), motive_2 l B (.hyp hh hy) := by
    intro l y B hh hy k _
    refine premBase_of_label ?_ k
    simp only [premBase, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact .inl (.inr ⟨(l, y), hh, rfl, hy⟩)
  have meetHyp : ∀ {l y B} (hm : G.meetRow l = true) (hy : y ∈ B)
      (hb : meetBelow G l y f.hypotheses = true), motive_2 l B (.meetHyp hm hy hb) := by
    intro l y B hm hy hb k _
    refine premBase_of_label ?_ k
    simp only [premBase, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true]
    exact .inr ⟨hm, y, hy, hb⟩
  have inst : ∀ {l B} (w : Nat × List (List ι)) (e : Entry ι) hw hl hi hdec
      (hps : ∀ h ∈ e.hypotheses, Prem G sub look gen f (replace (e.variables.zip w.2) h.1)
        (replace (e.variables.zip w.2) h.2)),
      (∀ h hh, motive_1 _ _ (hps h hh)) → motive_2 l B (.inst w e hw hl hi hdec hps) := by
    intro l B w e hw hl hi hdec _ ih k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [premLabelB_succ]
    simp only [Bool.or_eq_true, List.any_eq_true]
    refine .inr ⟨w, hw, ?_⟩
    simp only [instanceB, hl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨hi, fun h hh => ⟨hdec h hh, ih h hh k (by have := hdec h hh; omega)⟩⟩
  exact ⟨fun h => Prem.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h,
    fun h => PremLabel.rec (motive_1 := motive_1) (motive_2 := motive_2)
      tab ren union mem hyp meetHyp inst h⟩

/-- The premise judgment is decided by its checker at its conclusion's size. -/
theorem prem_iff [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {look : Lookup ι} {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι}
    {A B : List ι} :
    Prem G sub look gen f A B ↔
      premB G sub look gen f (typeSize sub A + typeSize sub B + 1) A B = true :=
  ⟨fun h => prem_complete.1 h _ (by omega), fun h => (prem_sound _).2 _ _ h⟩

instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)} {look : Lookup ι}
    {gen : ι → List ι → List (Nat × List (List ι))} {f : Entry ι} :
    DecidableRel (Prem G sub look gen f) := fun _ _ => decidable_of_iff _ prem_iff.symm

/-- Entries already sound, which instances may cite by index below `size`:
a representation's checked variances (§4.3), or none. Supplied by verified
code with its proof, never by a certificate. -/
structure Base [DecidableEq ι] (G : NormalGraph ι) where
  size : Nat := 0
  entry : Nat → Option (Entry ι) := fun _ => none
  sound : ∀ k e, entry k = some e → EntrySound G e ∧ HypParams G e := by
    intro _ _ h; cases h

/-- The entries a family certificate's instances cite: the base's, then its
own after them. -/
def Base.lookup [DecidableEq ι] {G : NormalGraph ι} (base : Base G) (F : List (Entry ι)) :
    Lookup ι := fun k =>
  if k < base.size then base.entry k else F[k - base.size]?

theorem Base.lookup_cases [DecidableEq ι] {G : NormalGraph ι} (base : Base G) (F : List (Entry ι))
    (k : Nat) (e : Entry ι) (h : base.lookup F k = some e) :
    e ∈ F ∨ (EntrySound G e ∧ HypParams G e) := by
  unfold Base.lookup at h
  split at h
  · exact .inr (base.sound k e h)
  · exact .inl (List.mem_of_getElem? h)

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} [DecidableRel R] {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    [∀ L S M, Decidable (arrows L S M)] (i j : ι) :
    Decidable (SchemeRenames G sub R known arrows i j) := by
  unfold SchemeRenames; split <;> infer_instance

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} [DecidableRel R] {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    [∀ L S M, Decidable (arrows L S M)] (hyps : List (ι × ι)) (S T : List ι) :
    Decidable (OpaqueFamily G sub R known arrows hyps S T) := by
  unfold OpaqueFamily PartCovers SchemeCoversAlpha; infer_instance

set_option synthInstance.maxSize 1024 in
/-- The entries' core conditions, premises read in each entry, arrows by
checked evidence. -/
def checkEntries [DecidableEq ι] (G : NormalGraph ι) (sub : Option (Renaming G)) (known : Known ι)
    (gen : ι → List ι → List (Nat × List (List ι))) (look : Lookup ι) (F : List (Entry ι))
    (arrows : Evidence ι) : Bool :=
  decide (∀ f ∈ F, ∀ p ∈ f.pairs, SameKind G p.1 p.2 = true ∧
    OpaqueFamily G sub (Prem G sub look gen f) known
      (ArrowsCheckedWith G (Prem G sub look gen f) arrows) f.hypotheses p.1 p.2 ∧
    ∀ a ∈ sourceClauses G p.1 ++ meetSources G p.1 p.2 f.hypotheses, ∃ b ∈ clausesOf G p.2,
      checkClauseWith G (Prem G sub look gen f) known arrows p.1 a b = true)

theorem checkEntries_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)}
    {arrows : Evidence ι} (h : checkEntries G sub known gen look F arrows = true) :
    FamilyValid G sub known gen look F := by
  simp only [checkEntries, decide_eq_true_eq] at h
  intro f hf p hp
  obtain ⟨hk, ho, hc⟩ := h f hf p hp
  refine ⟨hk, OpaqueFamily.mono (fun L S M hs q hq => ?_) ho, fun a ha => ?_⟩
  · obtain ⟨e, _, _, _, he⟩ := hs q hq
    exact checkArrowWith_sound he
  · obtain ⟨b, hb, hcb⟩ := hc a ha
    exact ⟨b, hb, checkClauseWith_sound hcb⟩

theorem opaqueFamily_mono [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} [DecidableRel R] {known : Known ι} {hyps : List (ι × ι)}
    {S T : List ι} {es es' : Evidence ι} (hm : ∀ e ∈ es, e ∈ es')
    (h : OpaqueFamily G sub R known (ArrowsCheckedWith G R es) hyps S T) :
    OpaqueFamily G sub R known (ArrowsCheckedWith G R es') hyps S T :=
  OpaqueFamily.mono (fun L S M hs p hp => by
    obtain ⟨e, he, hL, hP, hc⟩ := hs p hp
    exact ⟨e, hm e he, hL, hP, hc⟩) h

set_option synthInstance.maxSize 1024 in
/-- Declarative opaque rows of a family pair have checked evidence: each
quantified coverage, renamed or not, is an arrow coverage. -/
theorem opaqueFamily_complete [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {R : List ι → List ι → Prop} [DecidableRel R] {known : Known ι} {hyps : List (ι × ι)}
    {S T : List ι}
    (h : OpaqueFamily G sub R known (fun L S M => ∀ p ∈ M,
      CallArrow (compatible G) (restElem G) R L S p) hyps S T) :
    ∃ es, OpaqueFamily G sub R known (ArrowsCheckedWith G R es) hyps S T := by
  have each : ∀ i ∈ S, ∃ es : Evidence ι, G.plain i = true ∨ i ∈ T ∨ .top ∈ clausesOf G T ∨
      MeetOpaque G (PartCovers G sub R known (ArrowsCheckedWith G R es) hyps)
        (fun a => ∃ b ∈ clausesOf G T, CoversWith G R known (ArrowsCheckedWith G R es) S a b) T i ∨
      (∃ y ∈ T, (i, y) ∈ hyps) ∨
      ∃ j ∈ T, SchemeCoversAlpha G sub R known (ArrowsCheckedWith G R es) i j := by
    intro i hi
    rcases h i hi with h | h | h | h | h | ⟨j, hj, hc | hc⟩
    · exact ⟨[], .inl h⟩
    · exact ⟨[], .inr (.inl h)⟩
    · exact ⟨[], .inr (.inr (.inl h))⟩
    · obtain ⟨es, he⟩ := MeetOpaque.evidence (h := h)
        (sc' := fun es => PartCovers G sub R known (ArrowsCheckedWith G R es) hyps)
        (cover' := fun es a => ∃ b ∈ clausesOf G T,
          CoversWith G R known (ArrowsCheckedWith G R es) S a b)
        (fun es es' hm a b h => Or.imp_left (SchemeCoversAlpha.mono (arrowsChecked_mono hm)) h)
        (fun es es' hm a ⟨b, hb, hc⟩ => ⟨b, hb, CoversWith.mono (arrowsChecked_mono hm) hc⟩)
        (fun a b h => h.elim (fun h => (schemeCoversAlpha_complete h).imp fun _ => .inl)
          fun h => ⟨[], .inr h⟩) (fun a h => coversWith_complete h)
      exact ⟨es, .inr (.inr (.inr (.inl he)))⟩
    · exact ⟨[], .inr (.inr (.inr (.inr (.inl h))))⟩
    · unfold SchemeCoversWith at hc
      split at hc
      · rename_i s s' hs hs'
        obtain ⟨es, he⟩ := checkClauseWith_complete (R := R) (self := []) hc.2.2.2.2
        refine ⟨es, .inr (.inr (.inr (.inr (.inr ⟨j, hj, .inl ?_⟩))))⟩
        simp only [SchemeCoversWith, hs, hs']
        exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, of_decide_eq_true he⟩
      · exact hc.elim
    · unfold SchemeRenames at hc
      split at hc
      · rename_i r s s' hs hs'
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hc
        obtain ⟨es, he⟩ := checkClauseWith_complete (R := R) (self := []) h9
        refine ⟨es, .inr (.inr (.inr (.inr (.inr ⟨j, hj, .inr ?_⟩))))⟩
        simp only [SchemeRenames, hs, hs']
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, of_decide_eq_true he⟩
      · exact hc.elim
  obtain ⟨es, he⟩ := collect S _ (fun i es es' hm h => by
    rcases h with h | h | h | h | h | ⟨j, hj, hc⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl (h.mono
        (fun _ _ => Or.imp_left (SchemeCoversAlpha.mono (arrowsChecked_mono hm)))
        fun a ⟨b, hb, hc⟩ => ⟨b, hb, CoversWith.mono (arrowsChecked_mono hm) hc⟩))))
    · exact .inr (.inr (.inr (.inr (.inl h))))
    · refine .inr (.inr (.inr (.inr (.inr ⟨j, hj, SchemeCoversAlpha.mono (fun L S M hs p hp => ?_) hc⟩))))
      obtain ⟨e, he, hL, hP, hc⟩ := hs p hp
      exact ⟨e, hm e he, hL, hP, hc⟩) each
  exact ⟨es, fun i hi => he i hi⟩

theorem checkEntries_complete [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)}
    (h : FamilyValid G sub known gen look F) : ∃ arrows, checkEntries G sub known gen look F arrows = true := by
  have rows : ∀ fp ∈ F.flatMap (fun f => f.pairs.map (f, ·)), ∃ es : Evidence ι,
      OpaqueFamily G sub (Prem G sub look gen fp.1) known
        (ArrowsCheckedWith G (Prem G sub look gen fp.1) es) fp.1.hypotheses fp.2.1 fp.2.2 ∧
      ∀ a ∈ sourceClauses G fp.2.1 ++ meetSources G fp.2.1 fp.2.2 fp.1.hypotheses,
        ∃ b ∈ clausesOf G fp.2.2,
        checkClauseWith G (Prem G sub look gen fp.1) known es fp.2.1 a b = true := by
    intro fp hfp
    obtain ⟨f, hf, hfp⟩ := List.mem_flatMap.mp hfp
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hfp
    have hv := h f hf p hp
    obtain ⟨es₀, ho⟩ := opaqueFamily_complete hv.2.1
    obtain ⟨es₁, hc⟩ := collect (sourceClauses G p.1 ++ meetSources G p.1 p.2 f.hypotheses)
      (fun a es => ∃ b ∈ clausesOf G p.2,
        checkClauseWith G (Prem G sub look gen f) known es p.1 a b = true)
      (fun a es es' hm ⟨b, hb, hc⟩ => ⟨b, hb, checkClauseWith_mono hm hc⟩)
      (fun a ha => by
        obtain ⟨b, hb, hc⟩ := hv.2.2 a ha
        obtain ⟨es, he⟩ := checkClauseWith_complete hc
        exact ⟨es, b, hb, he⟩)
    refine ⟨es₀ ++ es₁, opaqueFamily_mono (fun e he => List.mem_append_left _ he) ho, fun a ha => ?_⟩
    obtain ⟨b, hb, hc⟩ := hc a ha
    exact ⟨b, hb, checkClauseWith_mono (fun e he => List.mem_append_right _ he) hc⟩
  obtain ⟨es, he⟩ := collect _ _ (fun fp es es' hm h => by
    refine ⟨opaqueFamily_mono hm h.1, fun a ha => ?_⟩
    obtain ⟨b, hb, hc⟩ := h.2 a ha
    exact ⟨b, hb, checkClauseWith_mono hm hc⟩) rows
  refine ⟨es, ?_⟩
  simp only [checkEntries, decide_eq_true_eq]
  intro f hf p hp
  have hfp : (f, p) ∈ F.flatMap (fun f => f.pairs.map (f, ·)) :=
    List.mem_flatMap.mpr ⟨f, hf, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
  exact ⟨(h f hf p hp).1, (he _ hfp).1, (he _ hfp).2⟩

/-- The checker decides the declarative family rule, given arrow evidence. -/
theorem familyValid_iff_checked [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {known : Known ι} {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι}
    {F : List (Entry ι)} :
    FamilyValid G sub known gen look F ↔ ∃ arrows, checkEntries G sub known gen look F arrows = true :=
  ⟨checkEntries_complete, fun ⟨_, h⟩ => checkEntries_sound h⟩

/-- The variable discipline, decided. -/
def variablesOk [DecidableEq ι] {G : NormalGraph ι} (sub : Option (Renaming G))
    (F : List (Entry ι)) : Bool :=
  match sub with
  | some r => decide ((∀ f ∈ F, ∀ h ∈ f.hypotheses, h.1 ∈ f.variables ∧ h.2 ∈ f.variables) ∧
      ∀ f ∈ F, ∀ x ∈ f.variables, r.familyVar x = true)
  | none => F.all fun f => f.variables.isEmpty && f.hypotheses.isEmpty

theorem variablesOk_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {F : List (Entry ι)} (h : variablesOk sub F = true) : VariablesOk sub F := by
  cases sub with
  | some r =>
    simp only [variablesOk, decide_eq_true_eq] at h
    exact ⟨h.1, fun f hf x hx => h.2 f hf x hx⟩
  | none =>
    simp only [variablesOk, List.all_eq_true, Bool.and_eq_true, List.isEmpty_iff] at h
    refine ⟨fun f hf p hp => ?_, fun f hf x hx => ?_⟩
    · rw [(h f hf).2] at hp; cases hp
    · rw [(h f hf).1] at hx; cases hx

/-- A family certificate: its entries, the arrow evidence their coverage
uses, and the known rows, each with the instance proving it. -/
structure FamilyCertificate (ι : Type) where
  entries : List (Entry ι)
  arrows : Evidence ι := []
  instances : List (List ι × Ops ι × List (RestArrow (List ι)) × Instance ι) := []
  deriving Repr

/-- The claim is a pair of one of the certificate's variable-free entries,
and mentions none of its entries' family variables. -/
def claimOk [DecidableEq ι] {G : NormalGraph ι} (sub : Option (Renaming G))
    (F : List (Entry ι)) (S T : List ι) : Bool :=
  F.any (fun f => f.variables.isEmpty && f.hypotheses.isEmpty && f.pairs.contains (S, T)) &&
    match sub with
    | some r => F.all fun f => f.variables.all fun x => !r.mentions (S ++ T) x
    | none => true

/-- **Family subtyping, checked.** Instances of the known rows by the given
image checker, the variable discipline, the entries' conditions, and the
claim among the certificate's variable-free entries. Instances cite the
`base` entries, already sound (such as computed variances), by index below
`base.size`, and the certificate's own after them. -/
def checkFamilyUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (sub : Option (Renaming G)) (gen : ι → List ι → List (Nat × List (List ι)))
    (base : Base G) (S T : List ι) (c : FamilyCertificate ι) : Bool :=
  variablesOk sub c.entries &&
    c.instances.all (fun k => checkInstArrsUsing G images k.1 k.2.1 k.2.2.1 k.2.2.2) &&
    checkEntries G sub (knownOf c.instances) gen (base.lookup c.entries) c.entries c.arrows &&
    claimOk sub c.entries S T

theorem checkFamilyUsing_sound [DecidableEq ι] {G : NormalGraph ι} {images : InstanceImageCheck G}
    {sub : Option (Renaming G)} {gen : ι → List ι → List (Nat × List (List ι))}
    {base : Base G} {S T : List ι} {c : FamilyCertificate ι}
    (h : checkFamilyUsing G images sub gen base S T c = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  simp only [checkFamilyUsing, claimOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.isEmpty_iff, List.contains_iff_mem] at h
  obtain ⟨⟨⟨hvars, hinst⟩, hentries⟩, ⟨f, hf, ⟨⟨_, hhyp⟩, hp⟩⟩, -⟩ := h
  exact family_closed_sound (checkEntries_sound hentries) (variablesOk_sound hvars)
    (base.lookup_cases c.entries)
    (fun η k hk => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hk
      exact checkInstArrsUsing_sound (hinst q hq) η)
    hf hhyp hp

/-- Entries checked on their own, such as a component of variances citing
the ones computed before it, are sound. -/
theorem checkEntries_entries_sound [DecidableEq ι] {G : NormalGraph ι} {sub : Option (Renaming G)}
    {gen : ι → List ι → List (Nat × List (List ι))} {look : Lookup ι} {F : List (Entry ι)}
    {arrows : Evidence ι} (h : checkEntries G sub [] gen look F arrows = true)
    (hv : variablesOk sub F = true)
    (hlook : ∀ k e, look k = some e → e ∈ F ∨ (EntrySound G e ∧ HypParams G e)) :
    ∀ e ∈ F, EntrySound G e :=
  family_entries_sound (checkEntries_sound h) (variablesOk_sound hv) hlook
    (fun _ _ h => by simp at h)

/-- **An instance of a sound entry, checked**: the base entry at `w`'s index,
its variables at `w`'s types of their kinds, the claim's source within the
substituted source, the substituted target within the claim's target, and one
checked proof per hypothesis, in order, between the replacements. `Var` is
the case of a variance (§4.3). -/
def checkEntryInstanceUsing [DecidableEq ι] (G : NormalGraph ι) (images : InstanceImageCheck G)
    (r : Renaming G) (base : Base G) (w : Nat × List (List ι)) (S T : List ι)
    (proofs : List (Proof ι)) : Bool :=
  match base.entry w.1 with
  | some e =>
    w.2.length == e.variables.length && instKinds G e.variables w.2 &&
      S.all (fun l => decide (l ∈ r.substitute (e.variables.zip w.2) e.source)) &&
      (r.substitute (e.variables.zip w.2) e.target).all (fun l => decide (l ∈ T)) &&
      e.hypotheses.length == proofs.length &&
      (e.hypotheses.zip proofs).all fun hp =>
        checkUsing G images (replace (e.variables.zip w.2) hp.1.1)
          (replace (e.variables.zip w.2) hp.1.2) hp.2
  | none => false

theorem checkEntryInstanceUsing_sound [DecidableEq ι] {G : NormalGraph ι}
    {images : InstanceImageCheck G} {r : Renaming G} {base : Base G}
    {w : Nat × List (List ι)} {S T : List ι} {proofs : List (Proof ι)}
    (h : checkEntryInstanceUsing G images r base w S T proofs = true) :
    ∀ η, FamLe (mixedMeaning G η S) (mixedMeaning G η T) := by
  unfold checkEntryInstanceUsing at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hlen, hkinds⟩, hS⟩, hT⟩, hplen⟩, hproofs⟩ := h
    have hsound := base.sound _ e he
    have inst := entry_instance_sound r hsound.1 hsound.2 hlen hkinds (fun h hh => by
        obtain ⟨p, hp⟩ := exists_mem_zip hplen.symm h hh
        exact checkUsing_sound (hproofs _ hp))
    intro η
    exact fun n W x hx => (Sub.subset hT).mixed_sound η n W x
      (inst η n W x ((Sub.subset hS).mixed_sound η n W x hx))
  · cases h

#print axioms checkArrow_sound
#print axioms checkArrow_complete
#print axioms checkInstUsing_sound
#print axioms checkUsing_sound
#print axioms check_sound
#print axioms check_complete
#print axioms accepted
#print axioms checkEntries_sound
#print axioms checkEntries_complete
#print axioms familyValid_iff_checked
#print axioms checkFamilyUsing_sound
#print axioms checkEntries_entries_sound
#print axioms checkEntryInstanceUsing_sound
#print axioms prem_iff
end Verification.Model.PositiveCertificates
