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

def checkDomains [DecidableEq ι] (table : Table ι) : List (List ι) → List (List ι) → Bool
  | [], [] => true
  | a :: As, b :: Bs => decide (Rel table a b) && checkDomains table As Bs
  | _, _ => false

theorem checkDomains_iff [DecidableEq ι] {table} (As Bs : List (List ι)) :
    checkDomains table As Bs = true ↔ Domains (Rel table) As Bs := by
  induction As generalizing Bs with
  | nil => cases Bs <;> simp [checkDomains, Domains]
  | cons a As ih => cases Bs <;> simp [checkDomains, Domains, ih]

instance {elem : List ι → Option (List ι)} {R : List ι → List ι → Prop} [DecidableRel R]
    (As : List (List ι)) (E : List ι) : Decidable (ElemRest elem R As E) := by
  unfold ElemRest; split <;> infer_instance

instance [DecidableEq ι] {elem : List ι → Option (List ι)} {R : List ι → List ι → Prop}
    [DecidableRel R] (As : List (List ι)) (E : List ι) : Decidable (IntoRest elem R As E) := by
  unfold IntoRest; infer_instance

/-- A variadic source signature covering a fixed arrow, decided. -/
def checkRestFixed [DecidableEq ι] (G : NormalGraph ι) (table : Table ι)
    (s : RestArrow (List ι)) (q : Arrow (List ι)) : Bool :=
  decide (Rel table q.receiver s.receiver) &&
    checkDomains table (q.arguments.take s.arguments.1.length) s.arguments.1 &&
    decide (ElemRest (restElem G) (Rel table) (q.arguments.drop s.arguments.1.length) s.arguments.2 ∧
      (s.result = [] ∨ Rel table s.result q.result)) && s.effect.covers q.effect

theorem checkRestFixed_iff [DecidableEq ι] {G : NormalGraph ι} {table : Table ι} {s q} :
    checkRestFixed G table s q = true ↔ RestFixed (restElem G) (Rel table) s q := by
  simp [checkRestFixed, RestFixed, checkDomains_iff, and_assoc]

/-- Every recursive premise retains the target contract. Splitting a domain
changes only that domain; combining results states and checks both effects. -/
def checkArrow [DecidableEq ι] (G : NormalGraph ι) (table : Table ι)
    (L : Ops ι) (S : List (RestArrow (List ι))) (q : Arrow (List ι)) : ArrowCert ι → Bool
  | .empty => decide ([] ∈ q.arguments)
  | .emptyRecv => decide (q.receiver = [])
  | .source p => decide (p ∈ L ∧ Rel table q.receiver p.receiver ∧
      (p.result = [] ∨ Rel table p.result q.result)) &&
      checkDomains table q.arguments p.arguments && p.effect.covers q.effect
  | .rest s => decide (s ∈ S) && checkRestFixed G table s q
  | .union pre a b suffix left right => decide (q.arguments = pre ++ (a ++ b) :: suffix) &&
      checkArrow G table L S { q with arguments := pre ++ a :: suffix } left &&
      checkArrow G table L S { q with arguments := pre ++ b :: suffix } right
  | .recvUnion a b left right => decide (q.receiver = a ++ b) &&
      checkArrow G table L S { q with receiver := a } left &&
      checkArrow G table L S { q with receiver := b } right
  | .combine b b' effect other left right =>
      checkArrow G table L S { q with result := b, effect := effect } left &&
      checkArrow G table L S { q with result := b', effect := other } right &&
      decide (∀ i ∈ b, ∀ k ∈ b', compatible G i k = true → Rel table [i] q.result) &&
      (effect.meet other).covers q.effect

theorem checkArrow_sound [DecidableEq ι] {G : NormalGraph ι} {table L S q cert}
    (h : checkArrow G table L S q cert = true) :
    CallArrow (compatible G) (restElem G) (Rel table) L S q := by
  induction cert generalizing q with
  | empty => exact .empty (of_decide_eq_true h)
  | emptyRecv => exact .emptyRecv (of_decide_eq_true h)
  | source p =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq, checkDomains_iff] at h
    exact .source h.1.1.1 h.1.1.2.1 h.1.2 h.1.1.2.2 h.2
  | rest s =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq, checkRestFixed_iff] at h
    exact .rest h.1 h.2
  | union pre a b suffix left right ih ih' =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .union h.1.1 (ih h.1.2) (ih' h.2)
  | recvUnion a b left right ih ih' =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .recvUnion h.1.1 (ih h.1.2) (ih' h.2)
  | combine b b' effect other left right ih ih' =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .combine (ih h.1.1.1) (ih' h.1.1.2) h.1.2 h.2

theorem checkArrow_complete [DecidableEq ι] {G : NormalGraph ι} {table L S q}
    (h : CallArrow (compatible G) (restElem G) (Rel table) L S q) :
    ∃ cert, checkArrow G table L S q cert = true := by
  induction h with
  | emptyRecv he => exact ⟨.emptyRecv, by simpa [checkArrow] using he⟩
  | empty he => exact ⟨.empty, by simpa [checkArrow] using he⟩
  | @source p q hp hrecv hd hc he =>
    exact ⟨.source p, by simp [checkArrow, hp, hrecv, hd, hc, he, checkDomains_iff]⟩
  | @rest s q hs hr =>
    exact ⟨.rest s, by simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq,
      checkRestFixed_iff]; exact ⟨hs, hr⟩⟩
  | @union pre a b suffix q he ha hb ih ih' =>
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    exact ⟨.union pre a b suffix left right, by simp [checkArrow, he, hl, hr]⟩
  | @recvUnion a b q he ha hb ih ih' =>
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    exact ⟨.recvUnion a b left right, by simp [checkArrow, he, hl, hr]⟩
  | @combine q b b' e e' ha hb hg he ih ih' =>
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    refine ⟨.combine b b' e e' left right, ?_⟩
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hl, hr⟩, hg⟩, he⟩

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
abbrev ArrowsChecked [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (proofs : Evidence ι)
    (L : Ops ι) (S : List (RestArrow (List ι))) (M : Ops ι) : Prop :=
  ∀ p ∈ M, ∃ e ∈ proofs, e.1 = L ∧ e.2.1 = p ∧
    checkArrow G table L S p e.2.2 = true

set_option synthInstance.maxSize 1024 in
instance [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (proofs : Evidence ι) :
    ∀ L S M, Decidable (ArrowsChecked G table proofs L S M) := by
  intro L S M
  unfold ArrowsChecked
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
instance [DecidableEq ι] {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    {known : Known ι}
    {arrows : Ops ι → List (RestArrow (List ι)) → Ops ι → Prop}
    [∀ L S M, Decidable (arrows L S M)] (S T : List ι) :
    Decidable (OpaqueWith G R known arrows S T) := by
  unfold OpaqueWith; infer_instance

set_option synthInstance.maxSize 1024 in
/-- The executable checker is the shared coverage rule interpreted with checked
arrow evidence. Adding a coverage condition changes the checker automatically. -/
def checkClause [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (known : Known ι)
    (proofs : Evidence ι) (self : List ι) (a b : Clause (List ι)) : Bool :=
  decide (CoversWith G (Rel table) known (ArrowsChecked G table proofs) self a b)

theorem checkClause_sound [DecidableEq ι] {G : NormalGraph ι} {table known proofs self a b}
    (h : checkClause G table known proofs self a b = true) : Covers G (Rel table) known self a b := by
  apply CoversWith.mono (h := of_decide_eq_true h)
  intro L S M hs p hp
  obtain ⟨e, _, _, _, he⟩ := hs p hp
  exact checkArrow_sound he

/-- Finite evidence collection is proof-only; the checker itself makes no
classical choices. Monotonicity allows witnesses to share one evidence list. -/
private theorem collect {α β : Type} (xs : List α) (P : α → List β → Prop)
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

theorem checkClause_mono [DecidableEq ι] {G : NormalGraph ι} {table known self a b es es'}
    (hm : ∀ e ∈ es, e ∈ es') (h : checkClause G table known es self a b = true) :
    checkClause G table known es' self a b = true := by
  have h := of_decide_eq_true h
  apply decide_eq_true
  apply CoversWith.mono (h := h)
  intro L S M hs p hp
  obtain ⟨e, he, hL, hP, hc⟩ := hs p hp
  exact ⟨e, hm e he, hL, hP, hc⟩

private theorem arrow_evidence_complete [DecidableEq ι] {G : NormalGraph ι} {table} {L M : Ops ι}
    {S : List (RestArrow (List ι))}
    (h : ∀ p ∈ M, CallArrow (compatible G) (restElem G) (Rel table) L S p) :
    ∃ es : Evidence ι, ∀ p ∈ M, ∃ e ∈ es,
      e.1 = L ∧ e.2.1 = p ∧ checkArrow G table L S p e.2.2 = true := by
  have hx : ∀ p ∈ M, ∃ es : Evidence ι, ∃ e ∈ es,
      e.1 = L ∧ e.2.1 = p ∧ checkArrow G table L S p e.2.2 = true := by
    intro p hp
    obtain ⟨pc, hc⟩ := checkArrow_complete (h p hp)
    exact ⟨[(L, (p, pc))], (L, (p, pc)), by simp, rfl, rfl, hc⟩
  obtain ⟨es, he⟩ := collect M _ (fun p es es' hm ⟨e, he, hL, hp, hc⟩ =>
    ⟨e, hm e he, hL, hp, hc⟩) hx
  exact ⟨es,he⟩

set_option synthInstance.maxSize 1024 in
theorem checkClause_complete [DecidableEq ι] {G : NormalGraph ι} {table known self a b}
    (h : Covers G (Rel table) known self a b) : ∃ es, checkClause G table known es self a b = true := by
  simp only [checkClause, decide_eq_true_eq]
  cases a <;> cases b <;> simp only [Covers, CoversWith] at *
  all_goals try contradiction
  all_goals first
    | exact ⟨[], h⟩
    | (obtain ⟨es, he⟩ := arrow_evidence_complete h.1
       exact ⟨es, he, h.2⟩)
    | (obtain ⟨es, he⟩ := arrow_evidence_complete h.2.1
       exact ⟨es, h.1, he, h.2.2⟩)

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
      G.meetRow i = true ∨ ∃ j ∈ T, SchemeCoversWith G (Rel table) known (ArrowsChecked G table es) i j := by
    intro i hi
    rcases h i hi with h | h | h | h | ⟨j, hj, hc⟩
    · exact ⟨[], .inl h⟩
    · exact ⟨[], .inr (.inl h)⟩
    · exact ⟨[], .inr (.inr (.inl h))⟩
    · exact ⟨[], .inr (.inr (.inr (.inl h)))⟩
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
    · exact .inr (.inr (.inr (.inl h)))
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

#print axioms checkArrow_sound
#print axioms checkArrow_complete
#print axioms checkInstUsing_sound
#print axioms checkUsing_sound
#print axioms check_sound
#print axioms check_complete
#print axioms accepted
end Verification.Model.PositiveCertificates
