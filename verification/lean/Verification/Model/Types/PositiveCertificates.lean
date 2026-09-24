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

/-- A variadic source signature covering a fixed arrow, decided. -/
def checkRestFixed [DecidableEq ι] (table : Table ι)
    (s : List ι × List (List ι) × List ι × List ι)
    (Rt : List ι) (As : List (List ι)) (d : List ι) : Bool :=
  decide (Rel table Rt s.1) && checkDomains table (As.take s.2.1.length) s.2.1 &&
    decide ((∀ A ∈ As.drop s.2.1.length, Rel table A s.2.2.1) ∧
      (s.2.2.2 = [] ∨ Rel table s.2.2.2 d))

theorem checkRestFixed_iff [DecidableEq ι] {table : Table ι} {s Rt As d} :
    checkRestFixed table s Rt As d = true ↔ RestFixed (Rel table) s Rt As d := by
  simp [checkRestFixed, RestFixed, checkDomains_iff, and_assoc]

/-- One variadic signature covering another, decided. -/
def checkRestCovers [DecidableEq ι] (table : Table ι)
    (p q : List ι × List (List ι) × List ι × List ι) : Bool :=
  decide (Rel table q.1 p.1) && checkDomains table (q.2.1.take p.2.1.length) p.2.1 &&
    decide ((∀ A ∈ q.2.1.drop p.2.1.length, Rel table A p.2.2.1) ∧ Rel table q.2.2.1 p.2.2.1 ∧
      Rel table p.2.2.2 q.2.2.2)

theorem checkRestCovers_iff [DecidableEq ι] {table : Table ι} {p q} :
    checkRestCovers table p q = true ↔ RestCovers (Rel table) p q := by
  simp [checkRestCovers, RestCovers, checkDomains_iff, and_assoc]

/-- One checker for ordered argument-list coverage; every union certificate
identifies the unchanged positions as well as the position being split. -/
def checkArrow [DecidableEq ι] (G : NormalGraph ι) (table : Table ι)
    (L : Ops ι) (S : List (List ι × List (List ι) × List ι × List ι))
    (Rt : List ι) (As : List (List ι)) (d : List ι) : ArrowCert ι → Bool
  | .empty => decide ([] ∈ As)
  | .emptyRecv => decide (Rt = [])
  | .source p => decide (p ∈ L ∧ Rel table Rt p.1 ∧ (p.2.2 = [] ∨ Rel table p.2.2 d)) &&
      checkDomains table As p.2.1
  | .rest s => decide (s ∈ S) && checkRestFixed table s Rt As d
  | .union pre a b suffix left right => decide (As = pre ++ (a ++ b) :: suffix) &&
      checkArrow G table L S Rt (pre ++ a :: suffix) d left &&
      checkArrow G table L S Rt (pre ++ b :: suffix) d right
  | .recvUnion a b left right => decide (Rt = a ++ b) &&
      checkArrow G table L S a As d left && checkArrow G table L S b As d right
  | .combine b b' left right =>
      checkArrow G table L S Rt As b left && checkArrow G table L S Rt As b' right &&
      decide (∀ i ∈ b, ∀ k ∈ b', compatible G i k = true → Rel table [i] d)

theorem checkArrow_sound [DecidableEq ι] {G : NormalGraph ι} {table L S Rt As d cert}
    (h : checkArrow G table L S Rt As d cert = true) : CallArrow (compatible G) (Rel table) L S Rt As d := by
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
    (h : CallArrow (compatible G) (Rel table) L S Rt As d) :
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
    Decidable (CoversTuple R p q) := by
  unfold CoversTuple; infer_instance

/-- Every target arrow has checked evidence from the source's signatures. -/
abbrev ArrowsChecked [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (proofs : Evidence ι)
    (L : Ops ι) (S : List (List ι × List (List ι) × List ι × List ι)) (M : Ops ι) : Prop :=
  ∀ p ∈ M, ∃ e ∈ proofs, e.1 = L ∧ e.2.1 = p ∧
    checkArrow G table L S p.1 p.2.1 p.2.2 e.2.2 = true

set_option synthInstance.maxSize 1024 in
def checkClause [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (proofs : Evidence ι) :
    Clause (List ι) → Clause (List ι) → Bool
  | _, .top => true
  | .list a bs, .list c ds => decide (∀ q ∈ c :: ds, ∃ p ∈ a :: bs, CoversTuple (Rel table) p q)
  | .nul, .nul => true
  | .undef, .undef => true
  | .bool, .bool => true
  | .boolLit _, .bool => true
  | .boolLit a, .boolLit b => decide (a = b)
  | .num, .num => true
  | .numLit _, .num => true
  | .numLit a, .numLit b => decide (a = b)
  | .str, .str => true
  | .strLit _, .str => true
  | .strLit a, .strLit b => decide (a = b)
  | .refs a bs vs os, .refs c ds ws ps =>
      decide (CoversFields (Rel table) (a :: bs) (c :: ds) ∧ CoversViews (Rel table) (a :: bs) vs ws ∧
        CoversOptional (Rel table) (a :: bs) os ps)
  | .dict a bs vs ix os, .dict c ds ws iy ps =>
      decide (CoversFields (Rel table) (a :: bs) (c :: ds) ∧
        CoversViews (Rel table) (a :: bs) vs ws ∧ (∀ y ∈ iy, ∃ x ∈ ix, Rel table x y) ∧
        CoversOptional (Rel table) (a :: bs) os ps)
  | .arrs L S, .arrs M T | .callable _ _ L S, .arrs M T => decide
      (ArrowsChecked G table proofs L S M ∧ ∀ t ∈ T, ∃ s ∈ S, checkRestCovers table s t = true)
  | .callable a bs L S, .callable c ds M T => decide
      (CoversFields (Rel table) (a :: bs) (c :: ds) ∧ ArrowsChecked G table proofs L S M ∧
       ∀ t ∈ T, ∃ s ∈ S, checkRestCovers table s t = true)
  | .ctors L, .ctors M => decide (∀ q ∈ M, ∃ p ∈ L, Domains (Rel table) q.1 p.1 ∧ Rel table p.2 q.2)
  | _, _ => false


set_option synthInstance.maxSize 1024 in
theorem checkClause_sound [DecidableEq ι] {G : NormalGraph ι} {table proofs a b}
    (h : checkClause G table proofs a b = true) : Covers G (Rel table) a b := by
  cases a <;> cases b <;> simp only [checkClause, Bool.false_eq_true, Covers] at *
  all_goals try contradiction
  all_goals try trivial
  case ctors.ctors => exact of_decide_eq_true h
  · exact of_decide_eq_true h
  · exact of_decide_eq_true h
  · have hh := of_decide_eq_true h
    exact ⟨fun p hp => by obtain ⟨e, _, _, _, he⟩ := hh.1 p hp; exact checkArrow_sound he,
      fun t ht => by obtain ⟨s, hs, hc⟩ := hh.2 t ht; exact ⟨s, hs, checkRestCovers_iff.mp hc⟩⟩
  · exact of_decide_eq_true h
  · -- numLit ≤ numLit
    exact of_decide_eq_true h
  · have hh := of_decide_eq_true h
    exact ⟨fun p hp => by obtain ⟨e, _, _, _, he⟩ := hh.1 p hp; exact checkArrow_sound he,
      fun t ht => by obtain ⟨s, hs, hc⟩ := hh.2 t ht; exact ⟨s, hs, checkRestCovers_iff.mp hc⟩⟩
  · have hh := of_decide_eq_true h
    exact ⟨hh.1,
      fun p hp => by obtain ⟨e, _, _, _, he⟩ := hh.2.1 p hp; exact checkArrow_sound he,
      fun t ht => by obtain ⟨s, hs, hc⟩ := hh.2.2 t ht; exact ⟨s, hs, checkRestCovers_iff.mp hc⟩⟩
  · -- strLit ≤ strLit
    exact of_decide_eq_true h
  · exact of_decide_eq_true h

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

set_option synthInstance.maxSize 1024 in
theorem checkClause_mono [DecidableEq ι] {G : NormalGraph ι} {table a b es es'}
    (hm : ∀ e ∈ es, e ∈ es') (h : checkClause G table es a b = true) :
    checkClause G table es' a b = true := by
  cases a <;> cases b <;> simp only [checkClause, Bool.false_eq_true, decide_eq_true_eq] at *
  all_goals try contradiction
  all_goals try trivial
  all_goals first
    | exact h
    | (refine ⟨fun p hp => ?_, h.2⟩; obtain ⟨e,he,hL,hP,hc⟩ := h.1 p hp;
       exact ⟨e,hm e he,hL,hP,hc⟩)
    | (refine ⟨h.1, fun p hp => ?_, h.2.2⟩; obtain ⟨e,he,hL,hP,hc⟩ := h.2.1 p hp;
       exact ⟨e,hm e he,hL,hP,hc⟩)

private theorem arrow_evidence_complete [DecidableEq ι] {G : NormalGraph ι} {table} {L M : Ops ι}
    {S : List (List ι × List (List ι) × List ι × List ι)}
    (h : ∀ p ∈ M, CallArrow (compatible G) (Rel table) L S p.1 p.2.1 p.2.2) :
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
theorem checkClause_complete [DecidableEq ι] {G : NormalGraph ι} {table a b}
    (h : Covers G (Rel table) a b) : ∃ es, checkClause G table es a b = true := by
  by_cases hb : b = .top
  · subst hb; exact ⟨[], by cases a <;> rfl⟩
  cases a <;> cases b <;> simp only [Covers] at h
  all_goals try contradiction
  all_goals try exact absurd rfl hb
  case ctors.ctors => exact ⟨[], by simpa only [checkClause, decide_eq_true_eq] using h⟩
  · exact ⟨[], rfl⟩
  · exact ⟨[], rfl⟩
  · exact ⟨[], by simpa only [checkClause, decide_eq_true_eq] using h⟩
  · exact ⟨[], by simpa only [checkClause, decide_eq_true_eq] using h⟩
  · obtain ⟨es,he⟩ := arrow_evidence_complete h.1
    refine ⟨es, ?_⟩
    simp only [checkClause, decide_eq_true_eq]
    exact ⟨he, fun t ht => by obtain ⟨s, hs, hc⟩ := h.2 t ht; exact ⟨s, hs, checkRestCovers_iff.mpr hc⟩⟩
  · exact ⟨[], rfl⟩
  · exact ⟨[], by simpa [checkClause] using h⟩
  · -- num ≤ num
    exact ⟨[], rfl⟩
  · -- numLit ≤ num
    exact ⟨[], rfl⟩
  · -- numLit ≤ numLit
    exact ⟨[], by simpa [checkClause] using h⟩
  · exact ⟨[], rfl⟩
  · obtain ⟨es,he⟩ := arrow_evidence_complete h.1
    refine ⟨es, ?_⟩
    simp only [checkClause, decide_eq_true_eq]
    exact ⟨he, fun t ht => by obtain ⟨s, hs, hc⟩ := h.2 t ht; exact ⟨s, hs, checkRestCovers_iff.mpr hc⟩⟩
  · obtain ⟨es,he⟩ := arrow_evidence_complete h.2.1
    refine ⟨es, ?_⟩
    simp only [checkClause, decide_eq_true_eq]
    exact ⟨h.1, he,
      fun t ht => by obtain ⟨s, hs, hc⟩ := h.2.2 t ht; exact ⟨s, hs, checkRestCovers_iff.mpr hc⟩⟩
  · -- str ≤ str
    exact ⟨[], rfl⟩
  · -- strLit ≤ str
    exact ⟨[], rfl⟩
  · -- strLit ≤ strLit
    exact ⟨[], by simpa [checkClause] using h⟩
  · exact ⟨[], by simpa only [checkClause, decide_eq_true_eq] using h⟩

structure Certificate (ι : Type) where
  table : Table ι
  arrows : Evidence ι
  deriving Repr

set_option synthInstance.maxSize 1024 in
def checkCore [DecidableEq ι] (G : NormalGraph ι) (S T : List ι) (cert : Certificate ι) : Bool :=
  decide ((S, T) ∈ cert.table ∧ ∀ p ∈ cert.table, Opaque G p.1 p.2 ∧
    ∀ a ∈ sourceClauses G p.1, ∃ b ∈ clausesOf G p.2,
      checkClause G cert.table cert.arrows a b = true)


theorem checkCore_sound [DecidableEq ι] {G : NormalGraph ι} {S T cert}
    (h : checkCore G S T cert = true) : Core G S T := by
  simp only [checkCore, decide_eq_true_eq] at h
  refine ⟨cert.table, h.1, ?_⟩
  intro p hp
  refine ⟨(h.2 p hp).1, fun a ha => ?_⟩
  obtain ⟨b, hb, hc⟩ := (h.2 p hp).2 a ha
  exact ⟨b, hb, checkClause_sound hc⟩

theorem checkCore_complete [DecidableEq ι] {G : NormalGraph ι} {S T}
    (h : Core G S T) : ∃ cert, checkCore G S T cert = true := by
  obtain ⟨table, hm, hv⟩ := h
  have rows : ∀ p ∈ table, ∃ es : Evidence ι,
      ∀ a ∈ sourceClauses G p.1, ∃ b ∈ clausesOf G p.2,
        checkClause G table es a b = true := by
    intro p hp
    apply collect (sourceClauses G p.1)
      (fun a es => ∃ b ∈ clausesOf G p.2, checkClause G table es a b = true)
    · intro a es es' hm ⟨b, hb, hc⟩
      exact ⟨b, hb, checkClause_mono hm hc⟩
    · intro a ha
      obtain ⟨b, hb, hc⟩ := (hv p hp).2 a ha
      obtain ⟨es, he⟩ := checkClause_complete hc
      exact ⟨es, b, hb, he⟩
  obtain ⟨es, he⟩ := collect table _ (fun p es es' hm h a ha => by
    obtain ⟨b, hb, hc⟩ := h a ha
    exact ⟨b, hb, checkClause_mono hm hc⟩) rows
  exact ⟨⟨table, es⟩, by
    simp only [checkCore, decide_eq_true_eq]
    exact ⟨hm, fun p hp => ⟨(hv p hp).1, he p hp⟩⟩⟩

inductive Proof (ι : Type) where
  | core (certificate : Certificate ι)
  | subset
  | trans (middle : List ι) (left right : Proof ι)
  /-- A scheme row below a checked instance of its signatures: the instance
  table, the types the binders are instantiated at, the table's domain and the
  domain's free parameter rows. -/
  | inst (table : InstTable ι) (instances : List (List ι)) (domain : List ι) (free : FreeMap ι)
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
    | some s => !G.params j && expand G U == [.arrs s.signatures []] && FreeOk G D V &&
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

/-- `S` is one scheme row, and `T` one arrow clause whose every signature is an
image of one of the scheme's under `θ`. -/
def checkInst [DecidableEq ι] (G : NormalGraph ι) (S T : List ι) (tbl : InstTable ι)
    (θs : List (List ι)) (D : List ι) (V : FreeMap ι) : Bool :=
  match S, expand G T with
  | [i], [.arrs L []] =>
    match G.schemes i with
    | some s => !G.params i && θs.length == s.binders.length && TableOk G tbl D V &&
        L.all fun q => s.signatures.any fun p => sigImg tbl (s.binders.zip θs) p == some q
    | none => false
  | _, _ => false

theorem checkInst_sound [DecidableEq ι] {G : NormalGraph ι} {S T tbl θs D V}
    (h : checkInst G S T tbl θs D V = true) : Sub G S T := by
  unfold checkInst at h
  split at h
  · rename_i i L hT
    split at h
    · rename_i s hs
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.any_eq_true,
        beq_iff_eq] at h
      exact .inst h.1.1.1 hs h.1.1.2 h.1.2 h.2 hT
    · cases h
  · cases h

def check [DecidableEq ι] (G : NormalGraph ι) (S T : List ι) : Proof ι → Bool
  | .core cert => checkCore G S T cert
  | .subset => decide (∀ i ∈ S, i ∈ T)
  | .trans middle left right => check G S middle left && check G middle T right
  | .inst tbl θs D V => checkInst G S T tbl θs D V
  | .gen D V U p => genOk G S T D V U && check G S U p

theorem check_sound [DecidableEq ι] {G : NormalGraph ι} {S T proof}
    (h : check G S T proof = true) : Sub G S T := by
  induction proof generalizing S T with
  | core cert => exact .core (checkCore_sound h)
  | subset => exact .subset (of_decide_eq_true h)
  | trans middle left right ih ih' =>
    simp only [check, Bool.and_eq_true] at h
    exact .trans (ih h.1) (ih' h.2)
  | inst tbl θs D V => exact checkInst_sound h
  | gen D V U p ih =>
    simp only [check, Bool.and_eq_true] at h
    exact genOk_sound h.1 (ih h.2)

theorem check_complete [dec : DecidableEq ι] {G : NormalGraph ι} {S T}
    (h : Sub G S T) : ∃ proof, check G S T proof = true := by
  induction h with
  | core h =>
    obtain ⟨cert, hc⟩ := checkCore_complete h
    exact ⟨.core cert, hc⟩
  | subset h => exact ⟨.subset, by simpa only [check, decide_eq_true_eq] using h⟩
  | trans h1 h2 ih ih' =>
    rename_i S U T
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    exact ⟨.trans U left right, by simp [check, hl, hr]⟩
  | @inst T inst i s tbl θs D V L hp hq hlen hok hL hT =>
    have he : inst = dec := Subsingleton.elim _ _
    subst he
    refine ⟨.inst tbl θs D V, ?_⟩
    simp only [check, checkInst, hT, hq, hp, hok, hlen, Bool.not_false, Bool.true_and,
      beq_self_eq_true, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact fun q hq => hL q hq
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

def SourceSub (G : PositiveGraphs.Graph ι) (S T : List ι) : Prop :=
  Sub (normalizeGraph G) S T

def checkSource [DecidableEq ι] (G : PositiveGraphs.Graph ι) (S T : List ι)
    (proof : Proof ι) : Bool := check (normalizeGraph G) S T proof

theorem source_iff_checked [DecidableEq ι] {G : PositiveGraphs.Graph ι} {S T} :
    SourceSub G S T ↔ ∃ proof, checkSource G S T proof = true := derivable_iff_checked

theorem accepted_source [DecidableEq ι] {G : PositiveGraphs.Graph ι} {S T proof}
    (h : checkSource G S T proof = true) :
    FamLe (Tower.setSem (PositiveGraphs.denote G) S) (Tower.setSem (PositiveGraphs.denote G) T) :=
  transport_inclusion G S T (check_sound h).sound

theorem accepted_subsumption [DecidableEq ι] {G : PositiveGraphs.Graph ι} {S T proof}
    (h : checkSource G S T proof = true) (n : Nat) (W : WorldT n) (heap : Heap) (t : Tm)
    (hs : Safe (Tower.setSem (PositiveGraphs.denote G) S) n W heap t) :
    Safe (Tower.setSem (PositiveGraphs.denote G) T) n W heap t := by
  apply Safe_mono n _ W heap t hs
  intro j _ U v hv
  exact accepted_source h j U v hv

#print axioms checkArrow_sound
#print axioms checkArrow_complete
#print axioms check_sound
#print axioms check_complete
#print axioms accepted_source
end Verification.Model.PositiveCertificates
