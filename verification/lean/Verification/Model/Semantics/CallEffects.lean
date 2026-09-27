import Verification.Model.Semantics.HeapObservations
import Verification.Model.Semantics.Purity

/-! Call postconditions qualify the same receiver/arguments/result contract
as ordinary arrows. They concern calls admitted by that contract, not every
untyped invocation of a function. Fresh allocation is permitted; preserving
the input heap means keeping its existing locations unchanged on return.
Throws carry no return postcondition, just as in `SafePost`. -/
namespace Verification.Model.CallEffects
open HeapObservations

inductive Effect where
  | unrestricted
  | preservesInputHeap
  deriving Repr, DecidableEq

/-- One qualified call contract. `Args` distinguishes fixed argument lists
from a fixed prefix followed by an argument-pack contract. Mapping the type
operands preserves the effect by construction. -/
structure Contract (α Args : Type) where
  receiver : α
  arguments : Args
  result : α
  effect : Effect
  deriving Repr, DecidableEq

def Contract.map (f : α → β) (g : Args → Args') (s : Contract α Args) : Contract β Args' :=
  ⟨f s.receiver, g s.arguments, f s.result, s.effect⟩

abbrev Arrow (α : Type) := Contract α (List α)
abbrev RestArrow (α : Type) := Contract α (List α × α)

def Arrow.map (f : α → β) (s : Arrow α) : Arrow β := Contract.map f (List.map f) s
def RestArrow.map (f : α → β) (s : RestArrow α) : RestArrow β :=
  Contract.map f (fun p => (p.1.map f, f p.2)) s

/-- Deliberate forgetting, for ordinary call elimination. -/
def Arrow.plain (s : Arrow α) : α × List α × α := (s.receiver, s.arguments, s.result)
def RestArrow.plain (s : RestArrow α) : α × List α × α × α :=
  (s.receiver, s.arguments.1, s.arguments.2, s.result)

def Effect.post : Effect → Heap → Post
  | .unrestricted, _ => fun _ _ => True
  | .preservesInputHeap, before => fun after _ => before.IsPrefix after

/-- The arrow equation, with a heap postcondition relative to this call's
entry heap. The input and result contracts are exactly those of `Promise`.
The effect is per signature: one overload may preserve its input heap while
another overload of the same value does not. -/
def PromiseWith (effect : Effect)
    (Acc : (j : Nat) → WorldT j → List Tm → Prop) (Rc R : Fam)
    (k : Nat) (W : WorldT k) (v : Val) : Prop :=
  ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
    WorldAdm U → ∀ (heap : Heap), HeapOk j U heap → ∀ r, isVal r = true → Rc j U r →
      ∀ args, CallArguments.Values args → Acc j U args →
        ∃ result, CallArguments.Invoke ⟨v, r, args⟩ result ∧
          SafePost R (effect.post heap) j U heap result

theorem PromiseWith.erase {effect Acc Rc R k W v}
    (h : PromiseWith effect Acc Rc R k W v) : Promise Acc Rc R k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  obtain ⟨result, hi, hs⟩ := h j hj U hx hu heap hh r hrv hr args hv ha
  exact ⟨result, hi, HeapObservations.erase hs⟩

theorem unrestricted_iff {Acc Rc R k W v} :
    PromiseWith .unrestricted Acc Rc R k W v ↔ Promise Acc Rc R k W v := by
  constructor
  · exact PromiseWith.erase
  · intro h j hj U hx hu heap hh r hrv hr args hv ha
    obtain ⟨result, hi, hs⟩ := h j hj U hx hu heap hh r hrv hr args hv ha
    exact ⟨result, hi, forget hs⟩

theorem PromiseWith.down {effect Acc Rc R n W v}
    (h : PromiseWith effect Acc Rc R (n + 1) W v) :
    PromiseWith effect Acc Rc R n (trunc n (Nat.le_succ n) W) v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  exact h j (by omega) U (by rwa [trunc_trunc] at hx) hu heap hh r hrv hr args hv ha

theorem PromiseWith.mono {effect Acc Rc R n W W' v} (hx : WExt W W')
    (h : PromiseWith effect Acc Rc R n W v) : PromiseWith effect Acc Rc R n W' v := by
  intro j hj U hy hu heap hh r hrv hr args hv ha
  exact h j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hy) hu heap hh r hrv hr args hv ha

/-- Effect coverage is implication of the normal-return postcondition.
There is deliberately no rule strengthening an unrestricted signature. -/
def Effect.Covers (source target : Effect) : Prop :=
  ∀ before after value, source.post before after value → target.post before after value

def Effect.covers : Effect → Effect → Bool
  | .preservesInputHeap, _ => true
  | .unrestricted, .unrestricted => true
  | .unrestricted, .preservesInputHeap => false

theorem Effect.covers_sound {a b : Effect} (h : a.covers b = true) : a.Covers b := by
  cases a <;> cases b <;> simp_all [Effect.covers, Effect.Covers, Effect.post]

theorem PromiseWith.weaken {effect effect' Acc Acc' Rc Rc' R T k W v}
    (he : effect.Covers effect')
    (hrecv : ∀ j, j < k → ∀ U r, Rc' j U r → Rc j U r)
    (hacc : ∀ j, j < k → ∀ U args, Acc' j U args → Acc j U args)
    (hres : ∀ j, j < k → ∀ U u, R j U u → T j U u)
    (h : PromiseWith effect Acc Rc R k W v) : PromiseWith effect' Acc' Rc' T k W v := by
  intro j hj U hx hu heap hh r hrv hr args hv ha
  obtain ⟨result, hi, hs⟩ :=
    h j hj U hx hu heap hh r hrv (hrecv j hj U r hr) args hv (hacc j hj U args ha)
  exact ⟨result, hi, consequence_below (fun m hm => hres m (by omega)) (he heap) hs⟩

theorem PromiseWith.congr {effect Acc Acc' Rc Rc' R T n W v}
    (hrecv : Agree Rc Rc' n)
    (hacc : ∀ j, j < n → ∀ U args, Acc j U args ↔ Acc' j U args)
    (hres : Agree R T n) :
    PromiseWith effect Acc Rc R n W v ↔ PromiseWith effect Acc' Rc' T n W v := by
  constructor <;> intro h
  · exact h.weaken (fun _ _ _ h => h)
      (fun j hj U r => (hrecv j hj U r).mpr)
      (fun j hj U args => (hacc j hj U args).mpr)
      (fun j hj U u => (hres j hj U u).mp)
  · exact h.weaken (fun _ _ _ h => h)
      (fun j hj U r => (hrecv j hj U r).mp)
      (fun j hj U args => (hacc j hj U args).mp)
      (fun j hj U u => (hres j hj U u).mpr)

/-- Application consumes a qualified signature, without inspecting the
callee's implementation. Its entry heap is after actual evaluation. -/
theorem call_safe {effect : Effect} {P : ArgFam} {Rc R : Fam}
    (hP : Adm P) (hRc : Adm Rc) {n W heap f r vs}
    (hf : PromiseWith effect P Rc R n W f) (hr : Rc n W r)
    (hrv : isVal r = true) (hv : CallArguments.Values vs) (ha : P n W vs)
    (hw : WorldAdm W) (hh : HeapOk n W heap) :
    SafePost R (effect.post heap) n W heap (.invoke f r vs) := by
  cases n with
  | zero => trivial
  | succ n =>
    let U := trunc n (Nat.le_succ n) W
    obtain ⟨body, hi, hs⟩ := hf n (Nat.lt_succ_self n) U (WExt_refl _)
      (WorldAdm_trunc _ hw) heap (HeapOk_trunc n W heap hh) r hrv (hRc.down n W r hr)
      vs hv (hP.transfer ha n (Nat.le_succ n) U (WExt_refl _))
    exact .inr ⟨U, heap, body, WExt_refl _, WorldAdm_trunc _ hw, hi.step heap,
      HeapOk_trunc n W heap hh, hs⟩

/-- The conservative executable purity check enriches independently proved
safety. It cannot manufacture safety or a return type on its own. -/
theorem pure_safe {R : Fam} : ∀ {n W heap t},
    Purity.PureRun t → Safe R n W heap t →
    SafePost R (Effect.preservesInputHeap.post heap) n W heap t := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W heap t hp hs
    rcases hs with (⟨hv, ht⟩ | hth) | ⟨U, h', t', hx, hu, step, hh, hs⟩
    · exact .inl (.inl ⟨hv, ht, ⟨[], by simp⟩⟩)
    · exact .inl (.inr hth)
    · obtain ⟨rfl, hp'⟩ := hp.step step
      exact .inr ⟨U, h', t', hx, hu, step, hh, ih hp' hs⟩

def callsT (L : List (Arrow Fam)) : Fam := fun k W v =>
  Invocable v ∧ ∀ s ∈ L, PromiseWith s.effect (ArgsShort s.arguments) s.receiver s.result k W v

theorem callsT_adm (L : List (Arrow Fam)) : Adm (callsT L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun s hs => (h.2 s hs).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun s hs => (h.2 s hs).mono hx⟩⟩

theorem callsT_erase {L : List (Arrow Fam)} {n W v} (h : callsT L n W v) :
    Model.callsT (L.map Arrow.plain) n W v := by
  refine ⟨h.1, ?_⟩
  intro p hp
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
  exact (h.2 s hs).erase

theorem callsT_select {L n W v p} (hf : callsT L n W v) (hp : p ∈ L) :
    callsT [p] n W v := by
  refine ⟨hf.1, ?_⟩
  intro q hq
  cases List.mem_singleton.mp hq
  exact hf.2 p hp

theorem callsT_congr {α : Type} (l : List α) (f g : α → Arrow Fam) {n : Nat}
    (he : ∀ x ∈ l, (f x).effect = (g x).effect)
    (h : ∀ x ∈ l, Agree (f x).receiver (g x).receiver n ∧
      ArgsAgree n (f x).arguments (g x).arguments ∧ Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : callsT (l.map f) n W v ↔ callsT (l.map g) n W v := by
  unfold callsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [← he x hm]
    exact (PromiseWith.congr (h x hm).1
      (fun j hj U args => ArgsShort_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mp (hs (f x) (List.mem_map_of_mem hm))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [he x hm]
    exact (PromiseWith.congr (h x hm).1
      (fun j hj U args => ArgsShort_congr (h x hm).2.1 hj U args)
      (h x hm).2.2).mpr (hs (g x) (List.mem_map_of_mem hm))

/-- Fixed arguments are value families, whereas the rest is an argument-list
family. Both are operands of the same effect-qualified contract. -/
abbrev RestSignature := Contract Fam (List Fam × ArgFam)

def restsT (L : List RestSignature) : Fam := fun k W v =>
  Invocable v ∧ ∀ s ∈ L,
    PromiseWith s.effect (ArgsRest s.arguments.1 s.arguments.2) s.receiver s.result k W v

theorem restsT_adm (L : List RestSignature) : Adm (restsT L) :=
  ⟨fun _ _ _ h => ⟨h.1, fun s hs => (h.2 s hs).down⟩,
   fun _ _ _ hx _ h => ⟨h.1, fun s hs => (h.2 s hs).mono hx⟩⟩

theorem restsT_erase {L : List RestSignature} {n W v} (h : restsT L n W v) :
    Model.restsT (L.map fun s => (s.receiver, s.arguments.1, s.arguments.2, s.result)) n W v := by
  refine ⟨h.1, ?_⟩
  intro p hp
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
  exact (h.2 s hs).erase

/-- Conjunction and overload normalization preserve every signature's effect. -/
theorem callsT_append (L M : List (Arrow Fam)) (n W v) :
    callsT (L ++ M) n W v ↔ callsT L n W v ∧ callsT M n W v := by
  simp only [callsT, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨hc, hl, hm⟩ => ⟨⟨hc, hl⟩, hc, hm⟩, fun ⟨⟨hc, hl⟩, _, hm⟩ => ⟨hc, hl, hm⟩⟩

theorem restsT_append (L M : List RestSignature) (n W v) :
    restsT (L ++ M) n W v ↔ restsT L n W v ∧ restsT M n W v := by
  simp only [restsT, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨hc, hl, hm⟩ => ⟨⟨hc, hl⟩, hc, hm⟩, fun ⟨⟨hc, hl⟩, _, hm⟩ => ⟨hc, hl, hm⟩⟩

theorem restsT_congr {α : Type} (l : List α) (f g : α → RestSignature) {n : Nat}
    (he : ∀ x ∈ l, (f x).effect = (g x).effect)
    (h : ∀ x ∈ l, Agree (f x).receiver (g x).receiver n ∧
      ArgsAgree n (f x).arguments.1 (g x).arguments.1 ∧
      Agree (f x).arguments.2 (g x).arguments.2 n ∧ Agree (f x).result (g x).result n)
    (W : WorldT n) (v : Val) : restsT (l.map f) n W v ↔ restsT (l.map g) n W v := by
  have args : ∀ x ∈ l, ∀ j, j < n → ∀ U vs,
      ArgsRest (f x).arguments.1 (f x).arguments.2 j U vs ↔
      ArgsRest (g x).arguments.1 (g x).arguments.2 j U vs := by
    intro x hx j hj U vs
    have hl := ArgsAgree_length (h x hx).2.1
    unfold ArgsRest
    rw [hl]
    exact and_congr (ArgsShort_congr (h x hx).2.1 hj U _) ((h x hx).2.2.1 j hj U _)
  unfold restsT
  refine and_congr Iff.rfl ⟨fun hs p hp => ?_, fun hs p hp => ?_⟩
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [← he x hm]
    exact (PromiseWith.congr (h x hm).1 (args x hm) (h x hm).2.2.2).mp
      (hs (f x) (List.mem_map_of_mem hm))
  · obtain ⟨x, hm, rfl⟩ := List.mem_map.mp hp
    rw [he x hm]
    exact (PromiseWith.congr (h x hm).1 (args x hm) (h x hm).2.2.2).mpr
      (hs (g x) (List.mem_map_of_mem hm))

#print axioms call_safe
#print axioms pure_safe
#print axioms PromiseWith.weaken
#print axioms unrestricted_iff
#print axioms PromiseWith.erase
end Verification.Model.CallEffects
