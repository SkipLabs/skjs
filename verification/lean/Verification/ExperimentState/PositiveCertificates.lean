import Verification.ExperimentState.PositiveRules

/-! Executable certificates for PositiveRules. Completeness concerns existence
of accepted evidence for a declarative derivation, not semantic completeness or
automatic proof search. -/
namespace Verification.ExperimentState.PositiveCertificates
open PositiveNormalization PositiveGraphs PositiveRules

inductive ArrowCert (ι : Type) where
  | empty
  | source (p : List ι × List ι)
  | union (a b : List ι) (left right : ArrowCert ι)
  | combine (b b' : List ι) (left right : ArrowCert ι)
  deriving Repr, DecidableEq

def checkArrow [DecidableEq ι] (G : NormalGraph ι) (table : Table ι)
    (L : Ops ι) (c d : List ι) : ArrowCert ι → Bool
  | .empty => decide (c = [])
  | .source p => decide (p ∈ L ∧ Rel table c p.1 ∧ (p.2 = [] ∨ Rel table p.2 d))
  | .union a b left right => decide (c = a ++ b) &&
      checkArrow G table L a d left && checkArrow G table L b d right
  | .combine b b' left right =>
      checkArrow G table L c b left && checkArrow G table L c b' right &&
      decide (∀ i ∈ b, ∀ k ∈ b', compatible G i k = true → Rel table [i] d)


theorem checkArrow_sound [DecidableEq ι] {G : NormalGraph ι} {table L c d cert}
    (h : checkArrow G table L c d cert = true) : Arrow G (Rel table) L c d := by
  induction cert generalizing c d with
  | empty => simp only [checkArrow, decide_eq_true_eq] at h; subst c; exact .empty
  | source p =>
    simp only [checkArrow, decide_eq_true_eq] at h
    exact .source h.1 h.2.1 h.2.2
  | union a b left right ih ih' =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1.1]
    exact .union (ih h.1.2) (ih' h.2)
  | combine b b' left right ih ih' =>
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .combine (ih h.1.1) (ih' h.1.2) h.2

theorem checkArrow_complete [DecidableEq ι] {G : NormalGraph ι} {table L c d}
    (h : Arrow G (Rel table) L c d) : ∃ cert, checkArrow G table L c d cert = true := by
  induction h with
  | empty => exact ⟨.empty, by simp [checkArrow]⟩
  | source hp hd hc =>
    rename_i p c d
    exact ⟨.source p, by simp [checkArrow, hp, hd, hc]⟩
  | union ha hb ih ih' =>
    rename_i a d b
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    exact ⟨.union a b left right, by simp [checkArrow, hl, hr]⟩
  | combine ha hb hg ih ih' =>
    rename_i c b b' d
    obtain ⟨left, hl⟩ := ih
    obtain ⟨right, hr⟩ := ih'
    refine ⟨.combine b b' left right, ?_⟩
    simp only [checkArrow, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hl, hr⟩, hg⟩

abbrev Evidence (ι : Type) := List (Ops ι × ((List ι × List ι) × ArrowCert ι))

set_option synthInstance.maxSize 1024 in
def checkClause [DecidableEq ι] (G : NormalGraph ι) (table : Table ι) (proofs : Evidence ι) :
    Clause (List ι) → Clause (List ι) → Bool
  | .nul, .nul => true
  | .bool, .bool => true
  | .refs a bs, .refs c ds => decide (∀ b ∈ c :: ds,
      ∃ x ∈ a :: bs, Rel table x b ∧ Rel table b x)
  | .arrs L, .arrs M => decide (∀ p ∈ M, ∃ e ∈ proofs,
      e.1 = L ∧ e.2.1 = p ∧ checkArrow G table L p.1 p.2 e.2.2 = true)
  | _, _ => false


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

theorem checkClause_mono [DecidableEq ι] {G : NormalGraph ι} {table a b es es'}
    (hm : ∀ e ∈ es, e ∈ es') (h : checkClause G table es a b = true) :
    checkClause G table es' a b = true := by
  cases a <;> cases b <;> simp only [checkClause, Bool.false_eq_true, decide_eq_true_eq] at *
  all_goals try contradiction
  all_goals try trivial
  intro p hp
  obtain ⟨e, he, hL, hP, hc⟩ := h p hp
  exact ⟨e, hm e he, hL, hP, hc⟩

theorem checkClause_complete [DecidableEq ι] {G : NormalGraph ι} {table a b}
    (h : Covers G (Rel table) a b) : ∃ es, checkClause G table es a b = true := by
  cases a <;> cases b <;> simp only [Covers] at h
  all_goals try contradiction
  · exact ⟨[], rfl⟩
  · exact ⟨[], rfl⟩
  · exact ⟨[], by simpa only [checkClause, decide_eq_true_eq] using h⟩
  · rename_i L M
    have hx : ∀ p ∈ M, ∃ es : Evidence ι, ∃ e ∈ es,
        e.1 = L ∧ e.2.1 = p ∧ checkArrow G table L p.1 p.2 e.2.2 = true := by
      intro p hp
      obtain ⟨pc, hc⟩ := checkArrow_complete (h p hp)
      exact ⟨[(L, (p, pc))], (L, (p, pc)), by simp, rfl, rfl, hc⟩
    obtain ⟨es, he⟩ := collect M _ (fun p es es' hm ⟨e, he, hL, hp, hc⟩ =>
      ⟨e, hm e he, hL, hp, hc⟩) hx
    exact ⟨es, by simpa only [checkClause, decide_eq_true_eq] using he⟩

structure Certificate (ι : Type) where
  table : Table ι
  arrows : Evidence ι
  deriving Repr

set_option synthInstance.maxSize 1024 in
def checkCore [DecidableEq ι] (G : NormalGraph ι) (S T : List ι) (cert : Certificate ι) : Bool :=
  decide ((S, T) ∈ cert.table ∧ ∀ p ∈ cert.table,
    ∀ a ∈ expand G p.1, ∃ b ∈ expand G p.2, checkClause G cert.table cert.arrows a b = true)


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
      ∀ a ∈ expand G p.1, ∃ b ∈ expand G p.2, checkClause G table es a b = true := by
    intro p hp
    apply collect (expand G p.1)
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

#print axioms check_sound
#print axioms check_complete
#print axioms accepted_source
end Verification.ExperimentState.PositiveCertificates
