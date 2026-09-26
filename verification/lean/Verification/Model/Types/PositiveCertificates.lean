import Verification.Model.Types.PositiveRules

/-! Executable certificates for PositiveRules. Completeness concerns existence
of accepted evidence for a declarative derivation, not semantic completeness or
automatic proof search. -/
namespace Verification.Model.PositiveCertificates
open PositiveNormalization PositiveGraphs PositiveRules

inductive ArrowCert (ι : Type) where
  | empty
  | source (p : List ι × List (List ι) × List ι)
  /-- A variadic source signature covers the target arrow. -/
  | rest (s : List ι × List (List ι) × List ι × List ι)
  | union (pre : List (List ι)) (a b : List ι) (suffix : List (List ι))
      (left right : ArrowCert ι)
  | combine (b b' : List ι) (left right : ArrowCert ι)
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
    (s : List ι × List (List ι) × List ι × List ι)
    (Rt : List ι) (As : List (List ι)) (d : List ι) : Bool :=
  decide (Rel table Rt s.1) && checkDomains table (As.take s.2.1.length) s.2.1 &&
    decide (ElemRest (restElem G) (Rel table) (As.drop s.2.1.length) s.2.2.1 ∧
      (s.2.2.2 = [] ∨ Rel table s.2.2.2 d))

theorem checkRestFixed_iff [DecidableEq ι] {G : NormalGraph ι} {table : Table ι} {s Rt As d} :
    checkRestFixed G table s Rt As d = true ↔ RestFixed (restElem G) (Rel table) s Rt As d := by
  simp [checkRestFixed, RestFixed, checkDomains_iff, and_assoc]

/-- One checker for ordered argument-list coverage; every union certificate
identifies the unchanged positions as well as the position being split. -/
def checkArrow [DecidableEq ι] (G : NormalGraph ι) (table : Table ι)
    (L : Ops ι) (S : List (List ι × List (List ι) × List ι × List ι))
    (Rt : List ι) (As : List (List ι)) (d : List ι) : ArrowCert ι → Bool
  | .empty => decide ([] ∈ As)
  | .emptyRecv => decide (Rt = [])
  | .source p => decide (p ∈ L ∧ Rel table Rt p.1 ∧ (p.2.2 = [] ∨ Rel table p.2.2 d)) &&
      checkDomains table As p.2.1
  | .rest s => decide (s ∈ S) && checkRestFixed G table s Rt As d
  | .union pre a b suffix left right => decide (As = pre ++ (a ++ b) :: suffix) &&
      checkArrow G table L S Rt (pre ++ a :: suffix) d left &&
      checkArrow G table L S Rt (pre ++ b :: suffix) d right
  | .recvUnion a b left right => decide (Rt = a ++ b) &&
      checkArrow G table L S a As d left && checkArrow G table L S b As d right
  | .combine b b' left right =>
      checkArrow G table L S Rt As b left && checkArrow G table L S Rt As b' right &&
      decide (∀ i ∈ b, ∀ k ∈ b', compatible G i k = true → Rel table [i] d)

theorem checkArrow_sound [DecidableEq ι] {G : NormalGraph ι} {table L S Rt As d cert}
    (h : checkArrow G table L S Rt As d cert = true) : CallArrow (compatible G) (restElem G) (Rel table) L S Rt As d := by
  induction cert generalizing Rt As d with
  | empty => exact .empty (of_decide_eq_true h)
  | emptyRecv =>
    have := of_decide_eq_true h
    subst this
    exact .emptyRecv
  | source p =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq, checkDomains_iff] at h
    exact .source h.1.1 h.1.2.1 h.2 h.1.2.2
  | rest s =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq, checkRestFixed_iff] at h
    exact .rest h.1 h.2
  | union pre a b suffix left right ih ih' =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1]
    exact .union (ih h.1.2) (ih' h.2)
  | recvUnion a b left right ih ih' =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1]
    exact .recvUnion (ih h.1.2) (ih' h.2)
  | combine b b' left right ih ih' =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .combine (ih h.1.1) (ih' h.1.2) h.2

theorem checkArrow_complete [DecidableEq ι] {G : NormalGraph ι} {table L S Rt As d}
    (h : CallArrow (compatible G) (restElem G) (Rel table) L S Rt As d) :
    ∃ cert, checkArrow G table L S Rt As d cert = true := by
  induction h with
  | emptyRecv => exact ⟨.emptyRecv, by simp [checkArrow]⟩
  | empty he => exact ⟨.empty, by simpa [checkArrow] using he⟩
  | source hp hrecv hd hc =>
    rename_i p Rt As d
    exact ⟨.source p, by simp [checkArrow, hp, hrecv, hd, hc, checkDomains_iff]⟩
  | rest hs hr =>
    rename_i s Rt As d
    exact ⟨.rest s, by simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq,
      checkRestFixed_iff]; exact ⟨hs, hr⟩⟩
  | @union Rt pre a suffix d b ha hb ih ih' =>
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    exact ⟨.union pre a b suffix left right, by simp [checkArrow, hl, hr]⟩
  | @recvUnion a As d b ha hb ih ih' =>
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    exact ⟨.recvUnion a b left right, by simp [checkArrow, hl, hr]⟩
  | combine ha hb hg ih ih' =>
    rename_i Rt As b b' d
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    refine ⟨.combine b b' left right, ?_⟩
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hl, hr⟩, hg⟩

abbrev Evidence (ι : Type) := List (Ops ι × ((List ι × List (List ι) × List ι) × ArrowCert ι))

instance {R : List ι → List ι → Prop} [DecidableRel R] (a b : Option (List ι)) :
    Decidable (CoversRest R readonly a b) := by
  cases a <;> cases b <;> simp only [CoversRest] <;> infer_instance

instance {R : List ι → List ι → Prop} [DecidableRel R] (p q : Tuple (List ι)) :
    Decidable (CoversShape R p q) := by
  unfold CoversShape; infer_instance

instance {R : List ι → List ι → Prop} [DecidableRel R] (p q : Tuple (List ι)) :
    Decidable (CoversPack R p q) := by
  unfold CoversPack; infer_instance

instance {R : List ι → List ι → Prop} [DecidableRel R] (p q : Tuple (List ι)) :
    Decidable (CoversTuple R p q) := by
  unfold CoversTuple; infer_instance

instance {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (p : List (List ι) × List ι) (t : List (List ι) × List ι × List ι) :
    Decidable (FixedCoversPack G R p t) := by
  unfold FixedCoversPack; split <;> infer_instance

instance {G : NormalGraph ι} {R : List ι → List ι → Prop} [DecidableRel R]
    (p : List ι × List (List ι) × List ι) (t : List ι × List (List ι) × List ι × List ι) :
    Decidable (FixedCallsPack G R p t) := by
  unfold FixedCallsPack; split <;> infer_instance

/-- Every target arrow has checked evidence from the source's signatures. -/
abbrev ArrowsChecked [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (proofs : Evidence ι)
    (L : Ops ι) (S : List (List ι × List (List ι) × List ι × List ι)) (M : Ops ι) : Prop :=
  ∀ p ∈ M, ∃ e ∈ proofs, e.1 = L ∧ e.2.1 = p ∧
    checkArrow G table L S p.1 p.2.1 p.2.2 e.2.2 = true

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
    {arrows : Ops ι → List (List ι × List (List ι) × List ι × List ι) → Ops ι → Prop}
    [∀ L S M, Decidable (arrows L S M)] (self a b) :
    Decidable (CoversWith G R known arrows self a b) := by
  cases a <;> cases b <;> unfold CoversWith <;> infer_instance

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
    {S : List (List ι × List (List ι) × List ι × List ι)}
    (h : ∀ p ∈ M, CallArrow (compatible G) (restElem G) (Rel table) L S p.1 p.2.1 p.2.2) :
    ∃ es : Evidence ι, ∀ p ∈ M, ∃ e ∈ es,
      e.1 = L ∧ e.2.1 = p ∧ checkArrow G table L S p.1 p.2.1 p.2.2 e.2.2 = true := by
  have hx : ∀ p ∈ M, ∃ es : Evidence ι, ∃ e ∈ es,
      e.1 = L ∧ e.2.1 = p ∧ checkArrow G table L S p.1 p.2.1 p.2.2 e.2.2 = true := by
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
  decide ((S, T) ∈ cert.table ∧ ∀ p ∈ cert.table, SameKind G p.1 p.2 = true ∧ Opaque G p.1 p.2 ∧
    ∀ a ∈ sourceClauses G p.1 ++ meetSources G p.1 p.2, ∃ b ∈ clausesOf G p.2,
      checkClause G cert.table known cert.arrows p.1 a b = true)


theorem checkCore_sound [DecidableEq ι] {G : NormalGraph ι} {known S T cert}
    (h : checkCore G known S T cert = true) : Core G known S T := by
  simp only [checkCore, decide_eq_true_eq] at h
  refine ⟨cert.table, h.1, ?_⟩
  intro p hp
  refine ⟨(h.2 p hp).1, (h.2 p hp).2.1, fun a ha => ?_⟩
  obtain ⟨b, hb, hc⟩ := (h.2 p hp).2.2 a ha
  exact ⟨b, hb, checkClause_sound hc⟩

theorem checkCore_complete [DecidableEq ι] {G : NormalGraph ι} {known S T}
    (h : Core G known S T) : ∃ cert, checkCore G known S T cert = true := by
  obtain ⟨table, hm, hv⟩ := h
  have rows : ∀ p ∈ table, ∃ es : Evidence ι,
      ∀ a ∈ sourceClauses G p.1 ++ meetSources G p.1 p.2, ∃ b ∈ clausesOf G p.2,
        checkClause G table known es p.1 a b = true := by
    intro p hp
    apply collect (sourceClauses G p.1 ++ meetSources G p.1 p.2)
      (fun a es => ∃ b ∈ clausesOf G p.2, checkClause G table known es p.1 a b = true)
    · intro a es es' hm ⟨b, hb, hc⟩
      exact ⟨b, hb, checkClause_mono hm hc⟩
    · intro a ha
      obtain ⟨b, hb, hc⟩ := (hv p hp).2.2 a ha
      obtain ⟨es, he⟩ := checkClause_complete hc
      exact ⟨es, b, hb, he⟩
  obtain ⟨es, he⟩ := collect table _ (fun p es es' hm h a ha => by
    obtain ⟨b, hb, hc⟩ := h a ha
    exact ⟨b, hb, checkClause_mono hm hc⟩) rows
  exact ⟨⟨table, es⟩, by
    simp only [checkCore, decide_eq_true_eq]
    exact ⟨hm, fun p hp => ⟨(hv p hp).1, (hv p hp).2.1, he p hp⟩⟩⟩

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
      (instances : List (List ι × Ops ι × List (List ι × List (List ι) × List ι × List ι) ×
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

/-- `S` is one scheme row, and `L`, `M` arrows whose every signature is an
image of one of the scheme's under the instance table, each instance within
its binder's bounds. -/
def checkInstArrs [DecidableEq ι] (G : NormalGraph ι) (S : List ι) (L : Ops ι)
    (M : List (List ι × List (List ι) × List ι × List ι)) (c : Instance ι) : Bool :=
  match S with
  | [i] =>
    match G.schemes i with
    | some s => !G.params i && c.instances.length == s.binders.length &&
        instKinds G s.binders c.instances &&
        c.bounds.length == s.bounds.length &&
        (s.bounds.zip c.bounds).all (fun bc => boundOk G s.binders c.instances bc.1 bc.2) &&
        TableOk G c.table c.domain c.free &&
        (L.all fun q => s.signatures.any fun p => sigMatch c.table (s.binders.zip c.instances) p q) &&
        M.all fun q => s.variadic.any fun p => restMatch c.table (s.binders.zip c.instances) p q
    | none => false
  | _ => false

theorem checkInstArrs_sound [DecidableEq ι] {G : NormalGraph ι} {S L M c}
    (h : checkInstArrs G S L M c = true) : InstArrs G S L M := by
  obtain ⟨tbl, θs, certs, D, V⟩ := c
  unfold checkInstArrs at h
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
  simp only [checkInstArrs, hq, hp, hok, hlen, hkinds, hcl, hcs, Bool.not_false, Bool.true_and,
    beq_self_eq_true, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  exact ⟨fun q hq => hL q hq, fun q hq => hM q hq⟩

/-- `T` is one arrow clause, an instance of the scheme row `S`. -/
def checkInst [DecidableEq ι] (G : NormalGraph ι) (S T : List ι) (c : Instance ι) : Bool :=
  match expand G T with
  | [.arrs L M] => checkInstArrs G S L M c
  | _ => false

theorem checkInst_sound [DecidableEq ι] {G : NormalGraph ι} {S T c}
    (h : checkInst G S T c = true) : Inst G S T := by
  unfold checkInst at h
  split at h
  · rename_i L M hT
    exact ⟨L, M, checkInstArrs_sound h, hT⟩
  · cases h

theorem checkInst_complete [DecidableEq ι] {G : NormalGraph ι} {S T}
    (h : Inst G S T) : ∃ c, checkInst G S T c = true := by
  obtain ⟨L, M, hi, hT⟩ := h
  obtain ⟨c, hc⟩ := checkInstArrs_complete hi
  exact ⟨c, by simp only [checkInst, hT, hc]⟩

/-- The rows a core certificate's instances prove. -/
def knownOf (ks : List (List ι × Ops ι × List (List ι × List (List ι) × List ι × List ι) × Instance ι)) :
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

def check [DecidableEq ι] (G : NormalGraph ι) (S T : List ι) : Proof ι → Bool
  | .core cert ks => checkCore G (knownOf ks) S T cert &&
      ks.all fun k => checkInstArrs G k.1 k.2.1 k.2.2.1 k.2.2.2
  | .subset => decide (∀ i ∈ S, i ∈ T)
  | .trans middle left right => check G S middle left && check G middle T right
  | .inst c => checkInst G S T c
  | .gen D V U p => genOk G S T D V U && check G S U p
  | .table tbl D V => TableOk G tbl D V &&
      S.all fun l => match entryImg tbl [] l with
        | some U => U.all (· ∈ T)
        | none => false

theorem check_sound [DecidableEq ι] {G : NormalGraph ι} {S T proof}
    (h : check G S T proof = true) : Sub G S T := by
  induction proof generalizing S T with
  | core cert ks =>
    simp only [check, Bool.and_eq_true, List.all_eq_true] at h
    refine .core (fun p hp => ?_) (checkCore_sound h.1)
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact checkInstArrs_sound (h.2 k hk)
  | subset => exact .subset (of_decide_eq_true h)
  | trans middle left right ih ih' =>
    simp only [check, Bool.and_eq_true] at h
    exact .trans (ih h.1) (ih' h.2)
  | inst c => exact .inst (checkInst_sound h)
  | gen D V U p ih =>
    simp only [check, Bool.and_eq_true] at h
    exact genOk_sound h.1 (ih h.2)
  | table tbl D V =>
    simp only [check, Bool.and_eq_true, List.all_eq_true] at h
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
    obtain ⟨cert, hc⟩ := checkCore_complete h
    exact ⟨.core cert ks, by simp only [check, hr, hc, ha, Bool.and_self]⟩
  | subset h => exact ⟨.subset, by simpa only [check, decide_eq_true_eq] using h⟩
  | trans h1 h2 ih ih' =>
    rename_i S U T
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    exact ⟨.trans U left right, by simp [check, hl, hr]⟩
  | @inst S T inst h =>
    have he : inst = dec := Subsingleton.elim _ _
    subst he
    obtain ⟨c, hc⟩ := checkInst_complete h
    exact ⟨.inst c, hc⟩
  | @table S T inst tbl D V hok hS =>
    have he : inst = dec := Subsingleton.elim _ _
    subst he
    refine ⟨.table tbl D V, ?_⟩
    simp only [check, hok, Bool.true_and, List.all_eq_true]
    intro l hl
    obtain ⟨U, hU, hUT⟩ := hS l hl
    simp only [hU, List.all_eq_true, decide_eq_true_eq]
    exact hUT
  | @gen S inst j s D U V hp hq hU hF hS _ ih =>
    have he : inst = dec := Subsingleton.elim _ _
    subst he
    obtain ⟨p, hpc⟩ := ih
    refine ⟨.gen D V U p, ?_⟩
    simp only [check, genOk, hq, hp, hU, hF, hpc, Bool.not_false, Bool.true_and, Bool.and_true,
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
#print axioms check_sound
#print axioms check_complete
#print axioms accepted
end Verification.Model.PositiveCertificates
