-- OperationResults.lean defines an operation's result family as the closure of its outcomes; without it operation results have no least admissible bound.
import Verification.Semantics.OperationResults

namespace Verification.OperationWorlds
open OperationResults

/-- A fixed choice of world annotations for a modeled execution. It is supplied
by the program/host model, independently of the result bound being checked. -/
structure Policy where
  allows : Config → Config → Prop
  unique : ∀ {c d e}, allows c d → allows c e → d = e

inductive Follows (p : Policy) : Config → Config → Prop where
  | refl : Follows p c c
  | snoc : Follows p c d → Edge d e → p.allows d e → Follows p c e

def SafeWith (p : Policy) (B : Fam) : (n : Nat) → WorldT n → Heap → Tm → Prop
  | 0, _, _, _ => True
  | n+1, W, h, t =>
      ((isVal t = true ∧ B (n+1) W t) ∨ Thrown t) ∨
      ∃ U : WorldT n, ∃ h' t',
        WExt (trunc n (Nat.le_succ n) W) U ∧ WorldAdm U ∧
        Step h t h' t' ∧ HeapOk n U h' ∧
        p.allows ⟨n+1,W,h,t⟩ ⟨n,U,h',t'⟩ ∧ SafeWith p B n U h' t'

theorem erase {p B} : ∀ n (W : WorldT n) h t,
    SafeWith p B n W h t → Safe B n W h t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W h t hs
    rcases hs with (hv | ht) | ⟨U,h',t',he,hu,st,hh,_,rest⟩
    · exact .inl (.inl hv)
    · exact .inl (.inr ht)
    · exact .inr ⟨U,h',t',he,hu,st,hh,ih U h' t' rest⟩

theorem Follows.safe {p c d B} (path : Follows p c d)
    (hs : SafeWith p B c.level c.world c.heap c.term) :
    SafeWith p B d.level d.world d.heap d.term := by
  induction path with
  | refl => exact hs
  | snoc path edge allowed ih =>
    cases edge with
    | step he hu step hh =>
      rcases ih with (⟨hv,_⟩ | thrown) | ⟨V,h',t',_,_,_,_,ha,rest⟩
      · exact False.elim (value_no_step hv step)
      · exact False.elim (thrown.no_step step)
      · have eq := p.unique allowed ha
        cases eq
        exact rest

def outcomes (p : Policy) (op : Val → Tm) (A : Fam) : Fam := fun n W v =>
  (0 < n ∧ isVal v = true ∧ Scoped 0 v) ∧
    ∃ k, ∃ U : WorldT k, ∃ h x h', WorldAdm U ∧ HeapOk k U h ∧ A k U x ∧
      Follows p ⟨k,U,h,op x⟩ ⟨n,W,h',v⟩

def result (p : Policy) (op : Val → Tm) (A : Fam) : Fam := closure (outcomes p op A)

theorem result_adm (p : Policy) (op : Val → Tm) (A : Fam) : Adm (result p op A) :=
  closure_adm _

/-- All payload types, including references, retain their meaning in the SAME
world chosen by the fixed policy. No world-independence premise is needed. -/
theorem result_le_of_safe {p op A B} (hb : Adm B)
    (safe : ∀ n (W : WorldT n) h x, WorldAdm W → HeapOk n W h → A n W x →
      SafeWith p B n W h (op x)) : FamLe (result p op A) B := by
  apply closure_le hb
  rintro n W v ⟨⟨hn,hv,_⟩,k,U,h,x,h',hu,hh,hx,path⟩
  have hs := path.safe (safe k U h x hu hh hx)
  cases n with
  | zero => omega
  | succ n =>
    rcases hs with (⟨_,hb⟩ | thrown) | ⟨_,_,_,_,_,step,_,_,_⟩
    · exact hb
    · exact False.elim (val_not_thrown hv thrown)
    · exact False.elim (value_no_step hv step)

theorem safe_result_from {p op A} {k} {U : WorldT k} {h x}
    (hu : WorldAdm U) (hh : HeapOk k U h) (hx : A k U x) :
    ∀ n (W : WorldT n) heap t,
      Follows p ⟨k,U,h,op x⟩ ⟨n,W,heap,t⟩ →
      SafeWith p values n W heap t → SafeWith p (result p op A) n W heap t := by
  intro n; induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro W heap t path hs
    rcases hs with (⟨hv,hclosed⟩ | thrown) | ⟨V,h',t',he,ha,step,hok,allow,rest⟩
    · exact .inl (.inl ⟨hv,closure_contains _ _ _ _
        ⟨⟨Nat.zero_lt_succ _,hclosed⟩,k,U,h,x,heap,hu,hh,hx,path⟩⟩)
    · exact .inl (.inr thrown)
    · exact .inr ⟨V,h',t',he,ha,step,hok,allow,
        ih V h' t' (.snoc path (.step he ha step hok) allow) rest⟩

theorem safe_result {p op A n W heap x}
    (hw : WorldAdm W) (hh : HeapOk n W heap) (hx : A n W x)
    (hs : SafeWith p values n W heap (op x)) :
    Safe (result p op A) n W heap (op x) :=
  erase n W heap (op x) (safe_result_from hw hh hx n W heap (op x) .refl hs)

#print axioms result_le_of_safe
#print axioms safe_result
theorem result_mono {p op A B} (hab : FamLe A B) :
    FamLe (result p op A) (result p op B) := by
  apply closure_mono
  rintro n W v ⟨hv,k,U,h,x,h',hu,hh,hx,path⟩
  exact ⟨hv,k,U,h,x,h',hu,hh,hab k U x hx,path⟩

theorem result_union (p : Policy) (op : Val → Tm) (A B : Fam) :
    result p op (unionT A B) = unionT (result p op A) (result p op B) := by
  funext n W v; apply propext; constructor
  · apply closure_le (unionT_adm _ _ (result_adm p op A) (result_adm p op B))
    rintro j U u ⟨hv,k,V,h,x,h',hw,hh,hx,path⟩
    rcases hx with hx | hx
    · exact Or.inl (closure_contains _ _ _ _ ⟨hv,k,V,h,x,h',hw,hh,hx,path⟩)
    · exact Or.inr (closure_contains _ _ _ _ ⟨hv,k,V,h,x,h',hw,hh,hx,path⟩)
  · rintro (ha | hb)
    · exact result_mono (fun _ _ _ h => Or.inl h) n W v ha
    · exact result_mono (fun _ _ _ h => Or.inr h) n W v hb

def awaited (p : Policy) (intrinsic : Val) (T : Fam) : Fam :=
  result p (fun x => .invoke intrinsic .undef [x]) T

#print axioms result_union
end Verification.OperationWorlds
