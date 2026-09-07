import Verification.ExperimentState.ProgramTyping

/-! Finite program evidence checked against the declarative rules. Each node
states its sequent explicitly. The external entry point also checks that the
root is the requested closed program and type; evidence cannot change the task.
No proof search or semantic observation budget is involved. -/
namespace Verification.ExperimentState.ProgramCertificates
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules

structure Sequent (ι : Type) where
  context : List (Ty ι)
  term : Tm
  type : Ty ι
  deriving DecidableEq

inductive Rule (ι : Type) where
  | var | nul | tru | fls | lam | app | letE | alloc | read | write
  | ifTrue | ifFalse
  | sub (proof : PositiveCertificates.Proof ι)

inductive Evidence (ι : Type) where
  | node (claim : Sequent ι) (rule : Rule ι) (premises : List (Evidence ι))

def claim : Evidence ι → Sequent ι
  | .node j _ _ => j

/-- Only finite, syntactic premises of one rule. -/
def Local [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) (r : Rule ι) (ps : List (Sequent ι)) : Prop :=
  match r, j.term, ps with
  | .var, .var i, [] => j.context[i]? = some j.type
  | .nul, .nul, [] => Represents G j.type .nul
  | .tru, .tru, [] | .fls, .fls, [] => Represents G j.type .bool
  | .lam, .lam b, ps =>
    match expand G j.type with
    | [.arrs L] => ps = L.map (fun p => ⟨p.1 :: j.context, b, p.2⟩)
    | _ => False
  | .app, .app f a, [jf, ja] =>
    jf.context = j.context ∧ jf.term = f ∧ ja.context = j.context ∧ ja.term = a ∧
    match expand G jf.type with
    | [.arrs L] => (ja.type, j.type) ∈ L
    | _ => False
  | .letE, .app (.lam b) a, [ja, jb] =>
    ja.context = j.context ∧ ja.term = a ∧ jb = ⟨ja.type :: j.context, b, j.type⟩
  | .alloc, .alloc a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧ Represents G j.type (.refs ja.type [])
  | .read, .read a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧ Represents G ja.type (.refs j.type [])
  | .write, .write a b, [ja, jb] =>
    ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
    Represents G ja.type (.refs jb.type []) ∧ Represents G j.type .nul
  | .ifTrue, .ite (.test tag (.var i)) u _, [ju] =>
    ju = ⟨j.context, u, j.type⟩ ∧
    match j.context[i]? with
    | some A => Answers G A tag true
    | none => False
  | .ifFalse, .ite (.test tag (.var i)) _ e, [je] =>
    je = ⟨j.context, e, j.type⟩ ∧
    match j.context[i]? with
    | some A => Answers G A tag false
    | none => False
  | .sub proof, _, [jt] =>
    jt.context = j.context ∧ jt.term = j.term ∧
    PositiveCertificates.check G jt.type j.type proof = true
  | _, _, _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) (r : Rule ι) (ps) :
    Decidable (Local G j r ps) := by
  unfold Local
  split <;> try infer_instance
  all_goals try dsimp [Represents, Answers]
  all_goals first | infer_instance | (split <;> infer_instance)

def checkTree [DecidableEq ι] (G : NormalGraph ι) : Evidence ι → Bool
  | .node j r ps => decide (Local G j r (ps.map claim)) && ps.attach.all (fun e => checkTree G e.val)
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem e.property
  simp only [Evidence.node.sizeOf_spec]
  omega

def checkScope (d : Nat) : Tm → Bool
  | .var i => decide (i < d)
  | .lam b => checkScope (d+1) b
  | .app a b | .write a b => checkScope d a && checkScope d b
  | .alloc a | .read a | .test _ a => checkScope d a
  | .ite c a b => checkScope d c && checkScope d a && checkScope d b
  | _ => true

theorem checkScope_iff (d : Nat) (t : Tm) : checkScope d t = true ↔ Scoped d t := by
  induction t generalizing d <;> simp_all [checkScope, Scoped, and_assoc]

/-- Bind evidence to the actual requested program, type and empty context.
Scope includes unselected branches and bodies of empty overloads. -/
def check [DecidableEq ι] (G : NormalGraph ι) (t : Tm) (A : Ty ι) (e : Evidence ι) : Bool :=
  decide (claim e = ⟨[], t, A⟩) && checkScope 0 t && checkTree G e

theorem local_sound [DecidableEq ι] {G : NormalGraph ι} {j r ps}
    (hl : Local G j r ps)
    (hp : ∀ p ∈ ps, HasTy G p.context p.term p.type) : HasTy G j.context j.term j.type := by
  rcases j with ⟨Γ, t, A⟩
  unfold Local at hl
  split at hl <;> (try dsimp only at *) <;> (try subst t)
  · exact .var hl
  · exact .nul hl
  · exact .tru hl
  · exact .fls hl
  · split at hl
    · rename_i b ps L hL
      apply HasTy.lam hL
      intro p hmem
      apply hp ⟨p.1 :: Γ, b, p.2⟩
      rw [hl]
      exact List.mem_map.mpr ⟨p, hmem, rfl⟩
    · contradiction
  · rename_i f a jf ja
    rcases hl with ⟨hΓf, htf, hΓa, hta, hL⟩
    have hf := hp jf (by simp)
    have ha := hp ja (by simp)
    rw [hΓf, htf] at hf
    rw [hΓa, hta] at ha
    split at hL
    · rename_i L he
      exact .app hf he hL ha
    · contradiction
  · rename_i b a ja jb
    rcases hl with ⟨hΓ, ht, rfl⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    exact .letE ha (hp ⟨ja.type :: Γ, b, A⟩ (by simp))
  · rename_i a ja
    rcases hl with ⟨hΓ, ht, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    exact .alloc ha hr
  · rename_i a ja
    rcases hl with ⟨hΓ, ht, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    exact .read ha hr
  · rename_i a b ja jb
    rcases hl with ⟨hΓa, hta, hΓb, htb, hr, hn⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa, hta] at ha
    rw [hΓb, htb] at hb
    exact .write ha hr hb hn
  · rename_i tag i u e ju
    rcases hl with ⟨rfl, hq⟩
    split at hq
    · rename_i D hd
      exact .ifTag hd hq (fun _ => hp ⟨Γ, u, A⟩ (by simp)) (by intro h; cases h)
    · contradiction
  · rename_i tag i u e je
    rcases hl with ⟨rfl, hq⟩
    split at hq
    · rename_i D hd
      exact .ifTag hd hq (by intro h; cases h) (fun _ => hp ⟨Γ, e, A⟩ (by simp))
    · contradiction
  · rename_i proof t jt
    rcases hl with ⟨hΓ, ht, hc⟩
    have hj := hp jt (by simp)
    rw [hΓ, ht] at hj
    exact .sub hj hc

theorem checkTree_sound [DecidableEq ι] {G : NormalGraph ι} (e : Evidence ι)
    (he : checkTree G e = true) : HasTy G (claim e).context (claim e).term (claim e).type := by
  cases e with
  | node j r ps =>
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at he
    apply local_sound he.1
    intro p hp
    obtain ⟨e, he', rfl⟩ := List.mem_map.mp hp
    exact checkTree_sound e (he.2 ⟨e, he'⟩ (by simp))
termination_by sizeOf e

theorem check_sound [DecidableEq ι] {G : NormalGraph ι} {t A e}
    (he : check G t A e = true) : Scoped 0 t ∧ HasTy G [] t A := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at he
  refine ⟨(checkScope_iff 0 t).mp he.1.2, ?_⟩
  have ht := checkTree_sound e he.2
  simpa only [he.1.1] using ht

theorem accepted_safe [DecidableEq ι] {G : NormalGraph ι} {t A e}
    (he : check G t A e = true) (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaning G A) n W h t :=
  (check_sound he).2.closed_safe (check_sound he).1 n W h hw hh

def Representable [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) : Prop :=
  ∃ e, claim e = j ∧ checkTree G e = true

private theorem gather [DecidableEq ι] {G : NormalGraph ι} (js : List (Sequent ι))
    (h : ∀ j ∈ js, Representable G j) :
    ∃ es : List (Evidence ι), es.map claim = js ∧ ∀ e ∈ es, checkTree G e = true := by
  induction js with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons j js ih =>
    obtain ⟨e, he, hc⟩ := h j (by simp)
    obtain ⟨es, hes, hcs⟩ := ih (fun k hk => h k (by simp [hk]))
    refine ⟨e :: es, by simp [he, hes], ?_⟩
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | hm
    · exact hc
    · exact hcs e' hm

private theorem node_complete [DecidableEq ι] {G : NormalGraph ι} {j r js}
    (hl : Local G j r js) (h : ∀ p ∈ js, Representable G p) : Representable G j := by
  obtain ⟨es, hes, hcs⟩ := gather js h
  refine ⟨.node j r es, rfl, ?_⟩
  simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨by simpa only [hes] using hl, fun e _ => hcs e.val e.property⟩

/-- Every declarative derivation has finite accepted evidence. This is coverage
of the rules, not semantic completeness and not a proof-search algorithm. -/
theorem checkTree_complete [DecidableEq ι] {G : NormalGraph ι} {Γ t A}
    (ht : HasTy G Γ t A) : Representable G ⟨Γ, t, A⟩ := by
  induction ht with
  | var hi => exact node_complete (r := .var) (js := []) hi (by simp)
  | nul hr => exact node_complete (r := .nul) (js := []) hr (by simp)
  | tru hr => exact node_complete (r := .tru) (js := []) hr (by simp)
  | fls hr => exact node_complete (r := .fls) (js := []) hr (by simp)
  | @lam F L Γ b hr hb ih =>
    apply node_complete (r := .lam) (js := L.map (fun p => ⟨p.1 :: Γ, b, p.2⟩))
    · simp only [Local, show expand G F = [.arrs L] from hr]
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @app Γ f F L A B a hf hr hp ha ihf iha =>
    apply node_complete (r := .app) (js := [⟨Γ,f,F⟩, ⟨Γ,a,A⟩])
    · simpa only [Local, show expand G F = [.arrs L] from hr, true_and] using hp
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact ihf
      · exact iha
  | @letE Γ a A b B ha hb iha ihb =>
    apply node_complete (r := .letE) (js := [⟨Γ,a,A⟩, ⟨A::Γ,b,B⟩])
    · exact ⟨rfl, rfl, rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact iha
      · exact ihb
  | @alloc Γ a A Ref ha hr ih =>
    apply node_complete (G := G) (j := ⟨Γ, .alloc a, Ref⟩) (r := .alloc) (js := [⟨Γ,a,A⟩]) ⟨rfl,rfl,hr⟩
    simpa using ih
  | @read Γ a Ref A ha hr ih =>
    apply node_complete (G := G) (j := ⟨Γ, .read a, A⟩) (r := .read) (js := [⟨Γ,a,Ref⟩]) ⟨rfl,rfl,hr⟩
    simpa using ih
  | @write Γ a Ref A b N ha hr hb hn iha ihb =>
    apply node_complete (G := G) (j := ⟨Γ, .write a b, N⟩) (r := .write) (js := [⟨Γ,a,Ref⟩, ⟨Γ,b,A⟩]) ⟨rfl,rfl,rfl,rfl,hr,hn⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihb
  | @ifTag Γ i A tag q u B e hi hq ht he iht ihe =>
    cases q with
    | true =>
      apply node_complete (r := .ifTrue) (js := [⟨Γ,u,B⟩])
      · simpa only [Local, hi, true_and] using hq
      · simpa using iht rfl
    | false =>
      apply node_complete (r := .ifFalse) (js := [⟨Γ,e,B⟩])
      · simpa only [Local, hi, true_and] using hq
      · simpa using ihe rfl
  | @sub Γ t A B cert ht hc ih =>
    apply node_complete (G := G) (j := ⟨Γ, t, B⟩) (r := .sub cert) (js := [⟨Γ,t,A⟩]) ⟨rfl,rfl,hc⟩
    simpa using ih

theorem derivable_iff_checked [DecidableEq ι] (G : NormalGraph ι) (t : Tm) (A : Ty ι) :
    (Scoped 0 t ∧ HasTy G [] t A) ↔ ∃ e, check G t A e = true := by
  constructor
  · rintro ⟨hs, ht⟩
    obtain ⟨e, he, hc⟩ := checkTree_complete ht
    exact ⟨e, by simp [check, he, (checkScope_iff 0 t).mpr hs, hc]⟩
  · rintro ⟨e, he⟩; exact check_sound he

#print axioms checkTree_sound
#print axioms derivable_iff_checked
#print axioms accepted_safe
end Verification.ExperimentState.ProgramCertificates
