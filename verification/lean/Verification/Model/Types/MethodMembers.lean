import Verification.Model.Types.ReferenceConjunctions

/-! # Host-relative method members

A method member's contract is relative to its host: reading the member from
an object and invoking it **with that object as receiver** behaves as typed.
It promises nothing for another receiver, so a member's signatures carry no
receiver. This is self-application, as in Abadi and Cardelli's object
calculus, and exactly the shape method-call syntax lowers to: read the member
from the saved object, then invoke it with that object.

A member is at a location of its host whose contract implies, below the
level and in every world extending the current one, the member's signatures
with the host as the one receiver. The host is fixed when the member is read;
every field keeps its location contract, so the pair (value read, host) keeps
its contract as the world grows. -/
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

/-- `v` holds `key` at a location whose contract implies `A` below the level,
in every world extending the current one. -/
def holdsAt (key : PropKey) (A : Fam) : Fam := fun k W v =>
  ∃ (flds : List (PropKey × Nat)) (l : Nat) (c : Ctr k),
    v = .objAt flds .absent ∧ flds.lookup key = some l ∧ lookup W l = some c ∧
    ∀ (j : Nat) (hj : j < k) (U : WorldT j), WExt (trunc j (Nat.le_of_lt hj) W) U →
      ∀ (u : Val), c j hj U u → A j U u

theorem holdsAt_adm (key : PropKey) (A : Fam) : Adm (holdsAt key A) := by
  refine ⟨?_, ?_⟩
  · intro n W v h
    obtain ⟨flds, l, c, hv, hf, hl, hag⟩ := h
    refine ⟨flds, l, _, hv, hf, lookup_trunc (Nat.le_succ n) W l c hl, ?_⟩
    intro j hj U hx u hu
    exact hag j (by omega) U (by rwa [trunc_trunc] at hx) u hu
  · intro n W W' hx v h
    obtain ⟨flds, l, c, hv, hf, hl, hag⟩ := h
    exact ⟨flds, l, c, hv, hf, WExt_lookup hx hl, fun j hj U hU u hu =>
      hag j hj U (WExt_trans (WExt_trunc (Nat.le_of_lt hj) hx) hU) u hu⟩

/-- A weaker family below the level is held wherever a stronger one is. -/
theorem holdsAt_mono {key : PropKey} {A B : Fam} {k : Nat}
    (h : ∀ j, j < k → ∀ (U : WorldT j) u, A j U u → B j U u) {W : WorldT k} {v : Val}
    (hv : holdsAt key A k W v) : holdsAt key B k W v := by
  obtain ⟨flds, l, c, hρ, hf, hl, hag⟩ := hv
  exact ⟨flds, l, c, hρ, hf, hl, fun j hj U hU u hu => h j hj U u (hag j hj U hU u hu)⟩

/-- `v` holds `key` along its prototype chain, `d` prototypes up: at `d = 0`
its own location for the key, whose contract implies `A`; at `d + 1` it lacks
the key and its prototype location's contract implies the same `d` up. The
family `A` is fixed, so the host a member is read from stays the receiver
however far up its key is found. -/
def along (key : PropKey) (A : Fam) : Nat → Fam
  | 0 => holdsAt key A
  | d + 1 => fun k W v => ∃ flds : List (PropKey × Nat), v = .objAt flds .absent ∧
      flds.lookup key = none ∧ holdsAt CallArguments.protoField (along key A d) k W v

theorem along_adm (key : PropKey) (A : Fam) : ∀ d, Adm (along key A d)
  | 0 => holdsAt_adm key A
  | d + 1 => by
    refine ⟨?_, ?_⟩
    · rintro n W v ⟨flds, hρ, hmiss, h⟩
      exact ⟨flds, hρ, hmiss, (holdsAt_adm _ (along key A d)).down n W v h⟩
    · rintro n W W' hx v ⟨flds, hρ, hmiss, h⟩
      exact ⟨flds, hρ, hmiss, (holdsAt_adm _ (along key A d)).mono n W W' hx v h⟩

/-- A weaker family below the level is found wherever a stronger one is, the
same number of prototypes up. -/
theorem along_mono {key : PropKey} {A B : Fam} : ∀ (d : Nat) {k : Nat},
    (∀ j, j < k → ∀ (U : WorldT j) u, A j U u → B j U u) →
    ∀ {W : WorldT k} {v : Val}, along key A d k W v → along key B d k W v
  | 0, _, h, _, _, hv => holdsAt_mono h hv
  | d + 1, _, h, _, _, ⟨flds, hρ, hmiss, hv⟩ =>
    ⟨flds, hρ, hmiss, holdsAt_mono (fun j hj U u hu =>
      along_mono d (fun i hi U' u' => h i (by omega) U' u') hu) hv⟩

/-- **Host-relative members.** A member of `v` is where JavaScript's lookup
finds its key: at `v`'s own location for it, or, when `v` lacks the key, where
its prototype chain has it, some prototypes up (`along`). The contract found
there implies, in every world extending the current one, the member's
signatures invoked on `v`. The implication is not claimed in unrelated
worlds: there the object's own locations need not hold their contracts, and a
method reading them could not be safe. -/
def memberT (m : Member) : Fam := fun k W v => ∃ d, along m.key (onHost v m) d k W v

theorem memberT_adm (m : Member) : Adm (memberT m) := by
  refine ⟨?_, ?_⟩
  · rintro n W v ⟨d, h⟩
    exact ⟨d, (along_adm _ _ d).down n W v h⟩
  · rintro n W W' hx v ⟨d, h⟩
    exact ⟨d, (along_adm _ _ d).mono n W W' hx v h⟩

/-- A member whose signatures imply another's below the level, found by the
same key, is that member. -/
theorem memberT_mono {m m' : Member} (hkey : m.key = m'.key) {k : Nat}
    (h : ∀ v, ∀ j, j < k → ∀ (U : WorldT j) u, onHost v m j U u → onHost v m' j U u)
    {W : WorldT k} {v : Val} (hv : memberT m k W v) : memberT m' k W v := by
  obtain ⟨d, hv⟩ := hv
  exact ⟨d, hkey ▸ along_mono d (h v) hv⟩

def methodT (ms : List Member) : Fam := fun k W v => ∀ m ∈ ms, memberT m k W v

theorem methodT_adm (ms : List Member) : Adm (methodT ms) :=
  ⟨fun n W v h m hm => (memberT_adm m).down n W v (h m hm),
    fun n W W' hx v h m hm => (memberT_adm m).mono n W W' hx v (h m hm)⟩

theorem methodT_nil (k : Nat) (W : WorldT k) (v : Val) : methodT [] k W v := by
  intro m hm
  simp at hm

theorem methodT_append (ms ns : List Member) (k : Nat) (W : WorldT k) (v : Val) :
    methodT (ms ++ ns) k W v ↔ methodT ms k W v ∧ methodT ns k W v := by
  simp only [methodT, List.mem_append, or_imp, forall_and]

/-- A member of the object, read from it. -/
theorem methodT_at {ms : List Member} {m : Member} (hm : m ∈ ms) {k} {W : WorldT k} {v}
    (h : methodT ms k W v) : memberT m k W v :=
  h m hm

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
  constructor
  · intro hv m hmem
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
    exact memberT_mono (m := Member.of X P s) (m' := Member.of Y Q s) rfl
      (fun v j hj U u => (onHost_congr X Y P Q n h hP s v j hj U u).mp)
      (hv (Member.of X P s) (List.mem_map_of_mem hs))
  · intro hv m hmem
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
    exact memberT_mono (m := Member.of Y Q s) (m' := Member.of X P s) rfl
      (fun v j hj U u => (onHost_congr X Y P Q n h hP s v j hj U u).mpr)
      (hv (Member.of Y Q s) (List.mem_map_of_mem hs))

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
