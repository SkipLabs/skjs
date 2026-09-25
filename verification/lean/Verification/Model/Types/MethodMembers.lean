import Verification.Model.Types.ReferenceConjunctions

/-! # Host-relative method members

A method member's contract is relative to its host: reading the member from
an object and invoking it **with that object as receiver** behaves as typed.
It promises nothing for another receiver, so a member's signatures carry no
receiver. This is self-application, as in Abadi and Cardelli's object
calculus, and exactly the shape method-call syntax lowers to: read the member
from the saved object, then invoke it with that object.

A member is a view whose family depends on the host: the location's contract
implies, below the level, the member's signatures with the host as the one
receiver. The host is fixed when the member is read; every field keeps its
location contract, so the pair (value read, host) keeps its contract as the
world grows. -/
namespace Verification.Model.MethodMembers

/-- One member: its key, its fixed signatures `(parameters, result)` and its
variadic ones `(parameters, rest, result)`, none with a receiver. -/
structure Member where
  key : PropKey
  calls : List (List Fam × Fam)
  rests : List (List Fam × ArgFam × Fam)

/-- The host as the one receiver a member admits. -/
def hostT (v : Val) : Fam := fun _ _ r => r = v

theorem hostT_adm (v : Val) : Adm (hostT v) :=
  ⟨fun _ _ _ h => h, fun _ _ _ _ _ h => h⟩

/-- What a member promises of a value read from host `v`: its signatures, each
with receiver `v`. -/
def onHost (v : Val) (m : Member) : Fam :=
  interT (callsT (m.calls.map fun p => (hostT v, p.1, p.2)))
    (restsT (m.rests.map fun s => (hostT v, s.1, s.2.1, s.2.2)))

theorem onHost_adm (v : Val) (m : Member) : Adm (onHost v m) :=
  interT_adm _ _ (callsT_adm _) (restsT_adm _)

/-- The views a host's members are, each at its host-relative family. -/
def hostViews (v : Val) (ms : List Member) : Fields :=
  ms.map fun m => (m.key, onHost v m)

/-- **Host-relative members.** Each member is a view of the object whose
reads, invoked on the object, meet the member's signatures. -/
def methodT (ms : List Member) : Fam := fun k W v => viewT (hostViews v ms) k W v

theorem methodT_adm (ms : List Member) : Adm (methodT ms) :=
  ⟨fun n W v h => (viewT_adm (hostViews v ms)).down n W v h,
   fun n W U hx v h => (viewT_adm (hostViews v ms)).mono n W U hx v h⟩

theorem methodT_nil (k : Nat) (W : WorldT k) (v : Val) : methodT [] k W v := by
  intro f T hm
  simp [hostViews] at hm

theorem methodT_append (ms ns : List Member) (k : Nat) (W : WorldT k) (v : Val) :
    methodT (ms ++ ns) k W v ↔ methodT ms k W v ∧ methodT ns k W v := by
  simp only [methodT, hostViews, List.map_append]
  exact viewT_append _ _ k W v

/-- A member of the object, read from it: the host-relative family its
location implies. -/
theorem methodT_at {ms : List Member} {m : Member} (hm : m ∈ ms) {k} {W : WorldT k} {v}
    (h : methodT ms k W v) :
    ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr k),
      v = .objAt flds .absent ∧ flds.lookup m.key = some l ∧ lookup W l = some c ∧
      ∀ (j : Nat) (hj : j < k) (W' : WorldT j) (u : Val), c j hj W' u → onHost v m j W' u :=
  viewT_at (fs := hostViews v ms) (List.mem_map_of_mem (f := fun m => (m.key, onHost v m)) hm) h

/-- A member's syntax: its key, fixed signatures `(parameters, result)` and
variadic ones `(parameters, rest, result)`, operands of any sort. -/
structure Sig (α : Type) where
  key : PropKey
  calls : List (List α × α)
  rests : List (List α × α × α) := []
  deriving Repr, DecidableEq

/-- The member a signature denotes, operands read by `X` and rests by `P`. -/
def Member.of {α : Type} (X : α → Fam) (P : α → ArgFam) (m : Sig α) : Member :=
  ⟨m.key, m.calls.map fun p => (p.1.map X, X p.2), m.rests.map fun s => (s.1.map X, P s.2.1, X s.2.2)⟩

private theorem argsAgree_map {α : Type} {X Y : α → Fam} {n : Nat}
    (h : ∀ a, Agree (X a) (Y a) n) : ∀ As : List α, ArgsAgree n (As.map X) (As.map Y)
  | [] => .nil
  | a :: As => .cons (h a) (argsAgree_map h As)

/-- A member's host-relative family depends on its operands only below the
budget, as a call clause's does. -/
theorem onHost_congr {α : Type} (X Y : α → Fam) (P Q : α → ArgFam) (n : Nat)
    (h : ∀ a, Agree (X a) (Y a) n) (hP : ∀ a, Agree (P a) (Q a) n) (m : Sig α) (v : Val) :
    Agree (onHost v (Member.of X P m)) (onHost v (Member.of Y Q m)) n := by
  intro j hj W u
  have hX : ∀ a, Agree (X a) (Y a) j := fun a k hk W v => h a k (by omega) W v
  have hQ : ∀ a, Agree (P a) (Q a) j := fun a k hk W v => hP a k (by omega) W v
  simp only [onHost, Member.of, List.map_map, interT, Function.comp_def]
  exact and_congr
    (callsT_congr m.calls (fun p => (hostT v, p.1.map X, X p.2))
      (fun p => (hostT v, p.1.map Y, Y p.2))
      (fun p _ => ⟨fun _ _ _ _ => Iff.rfl, argsAgree_map hX p.1, hX p.2⟩) W u)
    (restsT_congr m.rests (fun s => (hostT v, s.1.map X, P s.2.1, X s.2.2))
      (fun s => (hostT v, s.1.map Y, Q s.2.1, Y s.2.2))
      (fun s _ => ⟨fun _ _ _ _ => Iff.rfl, argsAgree_map hX s.1, hQ s.2.1, hX s.2.2⟩) W u)

/-- Members agreeing below the budget, read at their hosts, are the same
members. -/
theorem methodT_congr {α : Type} (X Y : α → Fam) (P Q : α → ArgFam) (n : Nat)
    (h : ∀ a, Agree (X a) (Y a) n) (hP : ∀ a, Agree (P a) (Q a) n) (ms : List (Sig α))
    (W : WorldT n) (v : Val) :
    methodT (ms.map (Member.of X P)) n W v ↔ methodT (ms.map (Member.of Y Q)) n W v := by
  simp only [methodT, hostViews, List.map_map]
  constructor
  · intro hv f T hmem
    obtain ⟨m, hm', he⟩ := List.mem_map.mp hmem
    cases he
    obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ := hv _ _ (List.mem_map.mpr ⟨m, hm', rfl⟩)
    exact ⟨flds, l, c, rfl, hf, hl, fun j hj W' u hu =>
      (onHost_congr X Y P Q n h hP m _ j hj W' u).mp (hag j hj W' u hu)⟩
  · intro hv f T hmem
    obtain ⟨m, hm', he⟩ := List.mem_map.mp hmem
    cases he
    obtain ⟨flds, l, c, rfl, hf, hl, hag⟩ := hv _ _ (List.mem_map.mpr ⟨m, hm', rfl⟩)
    exact ⟨flds, l, c, rfl, hf, hl, fun j hj W' u hu =>
      (onHost_congr X Y P Q n h hP m _ j hj W' u).mpr (hag j hj W' u hu)⟩

/-- Rename a member signature's operands. -/
def Sig.map {α β : Type} (f : α → β) (m : Sig α) : Sig β :=
  ⟨m.key, m.calls.map (fun p => (p.1.map f, f p.2)), m.rests.map (fun s => (s.1.map f, f s.2.1, f s.2.2))⟩

/-- Every operand of a member signature. -/
def Sig.operands {α : Type} (m : Sig α) : List α :=
  m.calls.flatMap (fun p => p.1 ++ [p.2]) ++ m.rests.flatMap (fun s => s.1 ++ [s.2.1, s.2.2])

/-- Renaming a signature's operands is reading them through the renaming. -/
theorem Member.of_map {α β : Type} (X : β → Fam) (P : β → ArgFam) (f : α → β) (m : Sig α) :
    Member.of X P (m.map f) = Member.of (fun a => X (f a)) (fun a => P (f a)) m := by
  simp [Member.of, Sig.map, Function.comp_def]

end Verification.Model.MethodMembers
