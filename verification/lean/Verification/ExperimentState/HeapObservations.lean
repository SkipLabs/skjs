import Verification.ExperimentState.Rules

/-! Current-content assertions over the existing heap semantics. These are not
value types or ownership permissions. `SafePost` strengthens the existing safety
predicate with a heap-dependent postcondition; it uses exactly the same steps,
world extensions and heap invariant. This module establishes semantic rules,
not an extension of the source checker or its certificate format. -/
namespace Verification.ExperimentState.HeapObservations
open Verification.ExperimentState

abbrev Post := Heap → Val → Prop

def Observes (h : Heap) (l : Nat) (v : Val) : Prop := h[l]? = some v

def Contents (h : Heap) (l : Nat) (P : Val → Prop) : Prop :=
  ∃ v, Observes h l v ∧ P v

/-- Proposed point-claim meaning: a persistent storage invariant AND a current
read observation. It is heap-indexed, unlike a value family. -/
def ObservedRef (A : Fam) (P : Val → Prop) (n : Nat) (W : WorldT n) (h : Heap) (v : Val) : Prop :=
  ∃ l, v = .obj l .nul ∧ refT A n W v ∧ Contents h l P

/-- Read observations may be absorbed when the storage invariant stays fixed.
No covariance or contravariance of the invariant reference is assumed. -/
theorem observed_union_absorb {A P Q n W h v} (hpq : ∀ u, P u → Q u) :
    (ObservedRef A P n W h v ∨ ObservedRef A Q n W h v) ↔ ObservedRef A Q n W h v := by
  constructor
  · rintro (⟨l,he,hr,u,ho,hp⟩ | hq)
    · exact ⟨l,he,hr,u,ho,hpq u hp⟩
    · exact hq
  · exact Or.inr

def exact (v : Val) : Fam := fun _ _ u => u = v

/-- At budget zero there is no observation, just as in `Safe`. At positive
budget, termination establishes both the value type and a fact about that heap.
Divergence remains permitted; this is safety with partial correctness. -/
def SafePost (T : Fam) (Q : Post) : (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, _, _, _ => True
  | n + 1, W, h, t =>
      (isVal t = true ∧ T (n + 1) W t ∧ Q h t) ∨
      (∃ (U : WorldT n) (h' : Heap) (t' : Tm),
        WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧ Step h t h' t' ∧
          HeapOk n U h' ∧ SafePost T Q n U h' t')

theorem erase {T Q} : ∀ {n W h t}, SafePost T Q n W h t → Safe T n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with ⟨hv,ht,_⟩ | ⟨U,h',t',hx,hu,step,hh,hs⟩
    · exact Or.inl ⟨hv,ht⟩
    · exact Or.inr ⟨U,h',t',hx,hu,step,hh,ih hs⟩

/-- Finite closure of the existing step relation, with its step count. This
introduces no new reduction rules. -/
inductive Steps : Nat → Heap → Tm → Heap → Tm → Prop where
  | refl : Steps 0 h t h t
  | next : Step h t h' t' → Steps k h' t' h'' t'' → Steps (k+1) h t h'' t''

/-- Adequacy of the postcondition for actual terminating executions. One level
beyond the executed steps is needed to observe the final value. -/
theorem postcondition {T Q k h t h' v} (run : Steps k h t h' v) (hv : isVal v = true) :
    ∀ (W : WorldT (k+1)), SafePost T Q (k+1) W h t → Q h' v := by
  induction run with
  | refl =>
    intro W hs
    rcases hs with ⟨_,_,hq⟩ | ⟨_,_,_,_,_,step,_,_⟩
    · exact hq
    · exact False.elim (value_no_step hv step)
  | next step run ih =>
    intro W hs
    rcases hs with ⟨hval,_,_⟩ | ⟨U,h'',t'',hx,hu,step',hh,hs⟩
    · exact False.elim (value_no_step hval step)
    · obtain ⟨rfl,rfl⟩ := Step_det step step'
      exact ih hv U hs

/-- An ordinary arrow supplies no heap postcondition. Forgetting observations
lets its existing safety theorem be used without strengthening its meaning. -/
theorem forget {T} : ∀ {n W h t}, Safe T n W h t → SafePost T (fun _ _ => True) n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with ⟨hv,ht⟩ | ⟨U,h',t',hx,hu,step,hh,hs⟩
    · exact Or.inl ⟨hv,ht,trivial⟩
    · exact Or.inr ⟨U,h',t',hx,hu,step,hh,ih hs⟩

/-- Add a postcondition entailed by the final value's type. This preserves the
same operational behavior and does not assume that the initial heap survives. -/
theorem of_value_property {T Q} (hq : ∀ n W h v, T n W v → Q h v) :
    ∀ {n W h t}, Safe T n W h t → SafePost T Q n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with ⟨hv,ht⟩ | ⟨U,h',t',hx,hu,step,hh,hs⟩
    · exact Or.inl ⟨hv,ht,hq _ _ _ _ ht⟩
    · exact Or.inr ⟨U,h',t',hx,hu,step,hh,ih hs⟩

theorem consequence {T U : Fam} {Q R : Post}
    (hsub : ∀ n W v, T n W v → U n W v) (hr : ∀ h v, Q h v → R h v) :
    ∀ {n W h t}, SafePost T Q n W h t → SafePost U R n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with ⟨hv,ht,hq⟩ | ⟨U,h',t',hx,hu,step,hh,hs⟩
    · exact Or.inl ⟨hv,hsub _ _ _ ht,hr _ _ hq⟩
    · exact Or.inr ⟨U,h',t',hx,hu,step,hh,ih hs⟩

theorem weaken {T Q R} (hr : ∀ h v, Q h v → R h v)
    {n W h t} (hs : SafePost T Q n W h t) : SafePost T R n W h t :=
  consequence (fun _ _ _ ht => ht) hr hs

theorem value {T Q n W h v} (hv : isVal v = true) (ht : T n W v) (hq : Q h v) :
    SafePost T Q n W h v := by
  cases n with
  | zero => trivial
  | succ n => exact Or.inl ⟨hv,ht,hq⟩

theorem refine_value {T Q n W h v} (hv : isVal v = true) (hq : Q h v)
    (hs : Safe T n W h v) : SafePost T Q n W h v := by
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with ⟨_,ht⟩ | ⟨_,_,_,_,_,step,_,_⟩
    · exact Or.inl ⟨hv,ht,hq⟩
    · exact False.elim (value_no_step hv step)

/-- Enrich an existing one-step safety rule with its actual post-state, using
operational determinism. This reuses storage preservation rather than reproving it. -/
theorem one_step {T Q n W h t h' v} (ht : isVal t = false) (hv : isVal v = true)
    (step : Step h t h' v) (hq : Q h' v) (hs : Safe T n W h t) :
    SafePost T Q n W h t := by
  cases n with
  | zero => trivial
  | succ n =>
    rcases hs with ⟨hval,_⟩ | ⟨U,h'',t'',hx,hu,step',hh,hs'⟩
    · simp [ht] at hval
    · obtain ⟨rfl,rfl⟩ := Step_det step step'
      exact Or.inr ⟨U,h',v,hx,hu,step',hh,refine_value hv hq hs'⟩

/-- Composition passes facts about the heap actually produced by the subterm,
not facts about the initial heap. Works for every existing evaluation context. -/
theorem bind {A B : Fam} {Q R : Post} (C : Tm → Tm)
    (lift : ∀ {h t h' t'}, Step h t h' t' → Step h (C t) h' (C t')) :
    ∀ n W h t, WorldAdm W → HeapOk n W h → SafePost A Q n W h t →
    (∀ j (hj : j ≤ n) U, WExt (trunc j hj W) U → WorldAdm U →
      ∀ h' v, HeapOk j U h' → isVal v = true → A j U v → Q h' v →
        SafePost B R j U h' (C v)) → SafePost B R n W h (C t) := by
  intro n; induction n with
  | zero => intros; trivial
  | succ p ih =>
    intro W h t hw hh hs hc
    rcases hs with ⟨hv,ha,hq⟩ | ⟨U,h',t',hx,hu,step,hh',hs'⟩
    · exact hc (p+1) (Nat.le_refl _) W (by rw [trunc_id]; exact WExt_refl _) hw h t hh hv ha hq
    · refine Or.inr ⟨U,h',C t',hx,hu,lift step,hh',ih U h' t' hu hh' hs' ?_⟩
      intro j hj V he hv h'' v hh'' hval ha hq
      apply hc j (by omega) V _ hv h'' v hh'' hval ha hq
      have he' := WExt_trunc hj hx
      rw [trunc_trunc] at he'
      exact WExt_trans he' he

theorem bind_value {T Q n} {W : WorldT (n+1)} {h b a}
    (hv : isVal a = true) (hw : WorldAdm W) (hh : HeapOk (n+1) W h)
    (hs : SafePost T Q n (trunc n (Nat.le_succ n) W) h (subst 0 a b)) :
    SafePost T Q (n+1) W h (.letE a b) :=
  Or.inr ⟨_,h,_,WExt_refl _,WorldAdm_trunc _ hw,.letV hv,HeapOk_trunc n W h hh,hs⟩

/-- Observations supply read precision without narrowing the location's world
contract. Reading preserves the whole heap, so all current observations remain. -/
theorem read_observed {n W h l v} {c : Tm} (hw : WorldAdm W) (hh : HeapOk n W h)
    (hv : isVal v = true) (ho : Observes h l v) :
    SafePost (exact v) (fun h' u => h' = h ∧ u = v) n W h (.read (.obj l c)) := by
  cases n with
  | zero => trivial
  | succ p =>
    refine Or.inr ⟨trunc p (Nat.le_succ p) W,h,v,WExt_refl _,WorldAdm_trunc _ hw,
      .readV ho,HeapOk_trunc p W h hh,?_⟩
    exact value hv rfl ⟨rfl,rfl⟩

theorem read_contents {n W h l P} {c : Tm} (hw : WorldAdm W) (hh : HeapOk n W h)
    (hval : ∀ v, P v → isVal v = true) (ho : Contents h l P) :
    SafePost (fun _ _ v => P v) (fun h' u => h' = h ∧ Observes h' l u) n W h (.read (.obj l c)) := by
  obtain ⟨v,hread,hp⟩ := ho
  apply consequence _ _ (read_observed hw hh (hval v hp) hread)
  · intro _ _ u he; cases he; exact hp
  · intro h' u he
    exact ⟨he.1,by rw [he.1,he.2]; exact hread⟩

/-- This rule has no premise asserting old contents. The write permission comes
from the invariant reference, and the postcondition records the new contents. -/
theorem write_observed {A : Fam} (ha : Adm A) {n W h l v}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hr : refT A n W (.obj l .nul))
    (hv : isVal v = true) (ht : A n W v) :
    SafePost nulT (fun h' u => h' = h.set l v ∧ u = .nul) n W h (.write (.obj l .nul) v) := by
  obtain ⟨_,c,he,hl,hc⟩ := hr
  cases he
  have hlt : l < h.length := by
    have hb := (List.getElem?_eq_some_iff.mp hl).1
    rw [hh.1]; exact hb
  exact one_step rfl rfl (.writeV hv hlt) ⟨rfl,rfl⟩
    (write_rule ha n W h l v hv hw hh hl hc ht)

theorem alloc_observed {A : Fam} (ha : Adm A) {n W h v}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hv : isVal v = true) (ht : A n W v) :
    SafePost (refT A) (fun h' u => h' = h ++ [v] ∧ u = .obj h.length .nul) n W h (.alloc v) :=
  one_step rfl rfl (.allocV hv) ⟨rfl,rfl⟩ (alloc_rule ha n W h v hv hw hh ht)

/-- A same-location alias shares the observation; variable names do not matter. -/
theorem alias {h l k v} (he : l = k) (ho : Observes h l v) : Observes h k v := by
  simpa [he] using ho

theorem write_new {h : Heap} {l v} (hlt : l < h.length) : Observes (h.set l v) l v := by
  simp [Observes,hlt]

/-- Framing a different cell requires a proof of different runtime locations. -/
theorem write_frame {h l k v u} (hne : l ≠ k) (ho : Observes h k u) :
    Observes (h.set l v) k u := by
  simpa [Observes,List.getElem?_set_ne hne] using ho

theorem alloc_frame {h l u v} (ho : Observes h l u) : Observes (h ++ [v]) l u := by
  have hlt := (List.getElem?_eq_some_iff.mp ho).1
  simpa [Observes,List.getElem?_append_left hlt] using ho

theorem alloc_new (h : Heap) (v : Val) : Observes (h ++ [v]) h.length v := by
  simp [Observes]

/-- Composite proof: mutation produces a new observation, which the continuation
uses to type the next read exactly. No original-content premise is needed. -/
theorem write_then_read {A : Fam} (ha : Adm A) {n W h l v}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hr : refT A n W (.obj l .nul))
    (hv : isVal v = true) (ht : A n W v) :
    SafePost (exact v) (fun h' u => Observes h' l v ∧ u = v) n W h
      (.letE (.write (.obj l .nul) v) (.read (.obj l .nul))) := by
  have hlt : l < h.length := by
    obtain ⟨_,c,he,hl,_⟩ := hr
    cases he
    rw [hh.1]; exact (List.getElem?_eq_some_iff.mp hl).1
  apply bind (fun t => .letE t (.read (.obj l .nul))) Step.letC
    n W h (.write (.obj l .nul) v) hw hh
    (write_observed ha hw hh hr hv ht)
  intro j hj U hx hu h' u hh' hval ht hpost
  have ho : Observes h' l v := by rw [hpost.1]; exact write_new hlt
  cases j with
  | zero => trivial
  | succ p =>
    apply bind_value hval hu hh'
    change SafePost _ _ p _ h' (.read (.obj l .nul))
    apply weaken _ (read_observed (WorldAdm_trunc _ hu) (HeapOk_trunc p U h' hh') hv ho)
    intro h'' result hp
    exact ⟨by rw [hp.1]; exact ho,hp.2⟩

/-- Testing a read value refines the current contents only while its observation
still holds. Testing an old immutable snapshot cannot re-establish this premise. -/
theorem test_refines {h l v P} (ho : Observes h l v) (hp : P v) : Contents h l P :=
  ⟨v,ho,hp⟩

theorem call_forget {A B : Fam} (ha : Adm A) (hav : ValOnly A) {n W h f a}
    (hw : WorldAdm W) (hh : HeapOk n W h) (hf : arrowT A B n W f) (ht : A n W a) :
    SafePost B (fun _ _ => True) n W h (.app f a) :=
  forget (app_elim ha hav hf ht hw hh)

#print axioms bind_value
#print axioms postcondition
#print axioms bind
#print axioms read_observed
#print axioms write_observed
#print axioms alloc_observed
end Verification.ExperimentState.HeapObservations
