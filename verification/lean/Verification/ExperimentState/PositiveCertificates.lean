import Verification.ExperimentState.PositiveRules

/-! Executable certificates for PositiveRules. Completeness concerns existence
of accepted evidence for a declarative derivation, not semantic completeness or
automatic proof search. -/
namespace Verification.ExperimentState.PositiveCertificates
open PositiveNormalization PositiveGraphs PositiveRules

inductive ArrowCert (ι : Type) where
  | empty
  | source (p : List (List ι) × List ι)
  | union (pre : List (List ι)) (a b : List ι) (suffix : List (List ι))
      (left right : ArrowCert ι)
  | combine (b b' : List ι) (left right : ArrowCert ι)
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

/-- One checker for ordered argument-list coverage; every union certificate
identifies the unchanged positions as well as the position being split. -/
def checkArrow [DecidableEq ι] (G : NormalGraph ι) (table : Table ι)
    (L : List (List (List ι) × List ι)) (As : List (List ι)) (d : List ι) : ArrowCert ι → Bool
  | .empty => decide ([] ∈ As)
  | .source p => decide (p ∈ L ∧ (p.2 = [] ∨ Rel table p.2 d)) && checkDomains table As p.1
  | .union pre a b suffix left right => decide (As = pre ++ (a ++ b) :: suffix) &&
      checkArrow G table L (pre ++ a :: suffix) d left &&
      checkArrow G table L (pre ++ b :: suffix) d right
  | .combine b b' left right =>
      checkArrow G table L As b left && checkArrow G table L As b' right &&
      decide (∀ i ∈ b, ∀ k ∈ b', compatible G i k = true → Rel table [i] d)

theorem checkArrow_sound [DecidableEq ι] {G : NormalGraph ι} {table L As d cert}
    (h : checkArrow G table L As d cert = true) : CallArrow G (Rel table) L As d := by
  induction cert generalizing As d with
  | empty => exact .empty (of_decide_eq_true h)
  | source p =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq, checkDomains_iff] at h
    exact .source h.1.1 h.2 h.1.2
  | union pre a b suffix left right ih ih' =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1]
    exact .union (ih h.1.2) (ih' h.2)
  | combine b b' left right ih ih' =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .combine (ih h.1.1) (ih' h.1.2) h.2

theorem checkArrow_complete [DecidableEq ι] {G : NormalGraph ι} {table L As d}
    (h : CallArrow G (Rel table) L As d) : ∃ cert, checkArrow G table L As d cert = true := by
  induction h with
  | empty he => exact ⟨.empty, by simpa [checkArrow] using he⟩
  | source hp hd hc =>
    rename_i p As d
    exact ⟨.source p, by simp [checkArrow, hp, hd, hc, checkDomains_iff]⟩
  | @union pre a suffix d b ha hb ih ih' =>
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    exact ⟨.union pre a b suffix left right, by simp [checkArrow, hl, hr]⟩
  | combine ha hb hg ih ih' =>
    rename_i As b b' d
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    refine ⟨.combine b b' left right, ?_⟩
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hl, hr⟩, hg⟩

abbrev Evidence (ι : Type) := List (Ops ι × ((List (List ι) × List ι) × ArrowCert ι))

set_option synthInstance.maxSize 1024 in
def checkClause [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (proofs : Evidence ι) :
    Clause (List ι) → Clause (List ι) → Bool
  | .nul, .nul => true
  | .undef, .undef => true
  | .bool, .bool => true
  | .boolLit _, .bool => true
  | .boolLit a, .boolLit b => decide (a = b)
  | .num, .num => true
  | .numLit _, .num => true
  | .numLit a, .numLit b => decide (a = b)
  | .refs a bs, .refs c ds => decide (CoversFields (Rel table) (a :: bs) (c :: ds))
  | .arrs L, .arrs M | .callable _ _ L, .arrs M => decide (∀ p ∈ M, ∃ e ∈ proofs,
      e.1 = L ∧ e.2.1 = p ∧ checkArrow G table L p.1 p.2 e.2.2 = true)
  | .callable a bs L, .callable c ds M => decide
      (CoversFields (Rel table) (a :: bs) (c :: ds) ∧
       ∀ p ∈ M, ∃ e ∈ proofs,
         e.1 = L ∧ e.2.1 = p ∧ checkArrow G table L p.1 p.2 e.2.2 = true)
  | _, _ => false


set_option synthInstance.maxSize 1024 in
theorem checkClause_sound [DecidableEq ι] {G : NormalGraph ι} {table proofs a b}
    (h : checkClause G table proofs a b = true) : Covers G (Rel table) a b := by
  cases a <;> cases b <;> simp only [checkClause, Bool.false_eq_true, Covers] at *
  all_goals try contradiction
  all_goals try trivial
  · exact of_decide_eq_true h
  · have hh := of_decide_eq_true h
    intro p hp
    obtain ⟨e, _, _, _, he⟩ := hh p hp
    exact checkArrow_sound he
  · exact of_decide_eq_true h
  · -- numLit ≤ numLit
    exact of_decide_eq_true h
  · have hh := of_decide_eq_true h
    intro p hp
    obtain ⟨e,_,_,_,he⟩ := hh p hp
    exact checkArrow_sound he
  · have hh := of_decide_eq_true h
    refine ⟨hh.1,?_⟩
    intro p hp
    obtain ⟨e,_,_,_,he⟩ := hh.2 p hp
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

set_option synthInstance.maxSize 1024 in
theorem checkClause_mono [DecidableEq ι] {G : NormalGraph ι} {table a b es es'}
    (hm : ∀ e ∈ es, e ∈ es') (h : checkClause G table es a b = true) :
    checkClause G table es' a b = true := by
  cases a <;> cases b <;> simp only [checkClause, Bool.false_eq_true, decide_eq_true_eq] at *
  all_goals try contradiction
  all_goals try trivial
  all_goals first
    | (intro p hp; obtain ⟨e,he,hL,hP,hc⟩ := h p hp; exact ⟨e,hm e he,hL,hP,hc⟩)
    | (refine ⟨h.1,?_⟩; intro p hp; obtain ⟨e,he,hL,hP,hc⟩ := h.2 p hp;
       exact ⟨e,hm e he,hL,hP,hc⟩)

private theorem arrow_evidence_complete [DecidableEq ι] {G : NormalGraph ι} {table} {L M : Ops ι}
    (h : ∀ p ∈ M, CallArrow G (Rel table) L p.1 p.2) :
    ∃ es : Evidence ι, ∀ p ∈ M, ∃ e ∈ es,
      e.1 = L ∧ e.2.1 = p ∧ checkArrow G table L p.1 p.2 e.2.2 = true := by
  have hx : ∀ p ∈ M, ∃ es : Evidence ι, ∃ e ∈ es,
      e.1 = L ∧ e.2.1 = p ∧ checkArrow G table L p.1 p.2 e.2.2 = true := by
    intro p hp
    obtain ⟨pc, hc⟩ := checkArrow_complete (h p hp)
    exact ⟨[(L, (p, pc))], (L, (p, pc)), by simp, rfl, rfl, hc⟩
  obtain ⟨es, he⟩ := collect M _ (fun p es es' hm ⟨e, he, hL, hp, hc⟩ =>
    ⟨e, hm e he, hL, hp, hc⟩) hx
  exact ⟨es,he⟩

set_option synthInstance.maxSize 1024 in
theorem checkClause_complete [DecidableEq ι] {G : NormalGraph ι} {table a b}
    (h : Covers G (Rel table) a b) : ∃ es, checkClause G table es a b = true := by
  cases a <;> cases b <;> simp only [Covers] at h
  all_goals try contradiction
  · exact ⟨[], rfl⟩
  · exact ⟨[], rfl⟩
  · exact ⟨[], by simpa only [checkClause, decide_eq_true_eq] using h⟩
  · rename_i L M
    obtain ⟨es,he⟩ := arrow_evidence_complete h
    exact ⟨es,by simpa only [checkClause,decide_eq_true_eq] using he⟩
  · exact ⟨[], rfl⟩
  · exact ⟨[], by simpa [checkClause] using h⟩
  · -- num ≤ num
    exact ⟨[], rfl⟩
  · -- numLit ≤ num
    exact ⟨[], rfl⟩
  · -- numLit ≤ numLit
    exact ⟨[], by simpa [checkClause] using h⟩
  · exact ⟨[], rfl⟩
  · obtain ⟨es,he⟩ := arrow_evidence_complete h
    exact ⟨es,by simpa only [checkClause,decide_eq_true_eq] using he⟩
  · obtain ⟨es,he⟩ := arrow_evidence_complete h.2
    exact ⟨es,by simpa only [checkClause,decide_eq_true_eq] using And.intro h.1 he⟩

structure Certificate (ι : Type) where
  table : Table ι
  arrows : Evidence ι
  deriving Repr

set_option synthInstance.maxSize 1024 in
def checkCore [DecidableEq ι] (G : NormalGraph ι) (S T : List ι) (cert : Certificate ι) : Bool :=
  decide ((S, T) ∈ cert.table ∧ ∀ p ∈ cert.table,
    ∀ a ∈ sourceClauses G p.1, ∃ b ∈ expand G p.2,
      checkClause G cert.table cert.arrows a b = true)


theorem checkCore_sound [DecidableEq ι] {G : NormalGraph ι} {S T cert}
    (h : checkCore G S T cert = true) : Core G S T := by
  simp only [checkCore, decide_eq_true_eq] at h
  refine ⟨cert.table, h.1, ?_⟩
  intro p hp a ha
  obtain ⟨b, hb, hc⟩ := h.2 p hp a ha
  exact ⟨b, hb, checkClause_sound hc⟩

theorem checkCore_complete [DecidableEq ι] {G : NormalGraph ι} {S T}
    (h : Core G S T) : ∃ cert, checkCore G S T cert = true := by
  obtain ⟨table, hm, hv⟩ := h
  have rows : ∀ p ∈ table, ∃ es : Evidence ι,
      ∀ a ∈ sourceClauses G p.1, ∃ b ∈ expand G p.2,
        checkClause G table es a b = true := by
    intro p hp
    apply collect (sourceClauses G p.1)
      (fun a es => ∃ b ∈ expand G p.2, checkClause G table es a b = true)
    · intro a es es' hm ⟨b, hb, hc⟩
      exact ⟨b, hb, checkClause_mono hm hc⟩
    · intro a ha
      obtain ⟨b, hb, hc⟩ := hv p hp a ha
      obtain ⟨es, he⟩ := checkClause_complete hc
      exact ⟨es, b, hb, he⟩
  obtain ⟨es, he⟩ := collect table _ (fun p es es' hm h a ha => by
    obtain ⟨b, hb, hc⟩ := h a ha
    exact ⟨b, hb, checkClause_mono hm hc⟩) rows
  exact ⟨⟨table, es⟩, by simpa only [checkCore, decide_eq_true_eq] using And.intro hm he⟩

inductive Proof (ι : Type) where
  | core (certificate : Certificate ι)
  | subset
  | trans (middle : List ι) (left right : Proof ι)
  deriving Repr

def check [DecidableEq ι] (G : NormalGraph ι) (S T : List ι) : Proof ι → Bool
  | .core cert => checkCore G S T cert
  | .subset => decide (∀ i ∈ S, i ∈ T)
  | .trans middle left right => check G S middle left && check G middle T right

theorem check_sound [DecidableEq ι] {G : NormalGraph ι} {S T proof}
    (h : check G S T proof = true) : Sub G S T := by
  induction proof generalizing S T with
  | core cert => exact .core (checkCore_sound h)
  | subset => exact .subset (of_decide_eq_true h)
  | trans middle left right ih ih' =>
    simp only [check, Bool.and_eq_true] at h
    exact .trans (ih h.1) (ih' h.2)

theorem check_complete [DecidableEq ι] {G : NormalGraph ι} {S T}
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
end Verification.ExperimentState.PositiveCertificates
