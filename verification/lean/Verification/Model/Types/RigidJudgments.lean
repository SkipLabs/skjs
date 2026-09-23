import Verification.Model.Programs.DirectObligation

/-! # Declarative inclusion under rigid bounds

`Sub ps a b` is the inclusion judgment of the rigid fragment, stated by rules
and independent of any algorithm: a rigid name is below itself and below
whatever its declared bound is below, ground unions are compared by inclusion,
and callables are contravariant in their parameters and covariant in their
result. `Ty.leUnder` is the executable relation. This module proves that every
accepted comparison is derivable, that the judgment is semantically sound on
its own, and that on well-formed parameter lists the executable relation
decides the judgment. A kernel-checked counterexample records what the earlier
fuel could not decide. -/
namespace Verification.Model.RigidJudgments
open DirectObligation PositiveGraphs

inductive Sub (ps : List Parameter) : Ty → Ty → Prop
  | variadic_fixed {rc ps' e r} (extra : Nat) :
      Sub ps (.variadic rc ps' e r) (.arrow rc (ps' ++ List.replicate extra e) r)
  | variadic_refl {rc ps' e r} : Sub ps (.variadic rc ps' e r) (.variadic rc ps' e r)
  | array_refl {e} : Sub ps (.array e) (.array e)
  | rigid_refl {x} : Sub ps (.rigid x) (.rigid x)
  | bound {x u b} (p : Parameter) (hp : p ∈ ps) (hn : p.name = x) (hu : p.upper = some u)
      (h : Sub ps u b) : Sub ps (.rigid x) b
  | ground {A B : List Nat} (h : ∀ i, i ∈ A → i ∈ B) : Sub ps (.ground A) (.ground B)
  /-- A caller may pass less than the callable accepts: the callable's
  receiver and parameters `ps'` are above the caller's, pointwise. -/
  | arrow {rc rd : Ty} {qs ps' : List Ty} {r t : Ty} (hrecv : Sub ps rd rc)
      (hlen : ps'.length = qs.length)
      (hargs : ∀ i (hq : i < qs.length) (hp : i < ps'.length), Sub ps qs[i] ps'[i])
      (hres : Sub ps r t) : Sub ps (.arrow rc ps' r) (.arrow rd qs t)
  /-- Every value is below top; a rigid name only through its bound. -/
  | top {a : Ty} (ha : ∀ x, a ≠ .rigid x) : Sub ps a .top

/-! ## The judgment is reflexive -/

theorem Sub.refl (ps : List Parameter) : ∀ a : Ty, Sub ps a a
  | .top => .top (fun _ h => by cases h)
  | .variadic .. => .variadic_refl
  | .array _ => .array_refl
  | .rigid _ => .rigid_refl
  | .ground _ => .ground fun _ h => h
  | .arrow rc qs r =>
    .arrow (Sub.refl ps rc) rfl (fun i _ hp => Sub.refl ps qs[i]) (Sub.refl ps r)
termination_by a => sizeOf a
decreasing_by
  all_goals simp_wf
  · omega
  · have := List.sizeOf_lt_of_mem (List.getElem_mem hp)
    omega
  · omega

/-! ## Lists: pointwise facts against the executable's `zip`/`all` walk -/

private theorem all_zip_index {f : Ty → Ty → Bool} :
    ∀ {qs ps' : List Ty}, ps'.length = qs.length →
      (qs.zip ps').all (fun (q, p) => f q p) = true →
      ∀ i (hq : i < qs.length) (hp : i < ps'.length), f qs[i] ps'[i] = true
  | [], [], _, _, i, hq, _ => by simp at hq
  | [], _ :: _, hlen, _, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _, _ => by simp at hlen
  | q :: qs, p :: ps', hlen, hall, i, hq, hp => by
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
      cases i with
      | zero => exact hall.1
      | succ i =>
        simp only [List.length_cons] at hlen
        exact all_zip_index (Nat.add_right_cancel hlen) hall.2 i
          (Nat.lt_of_succ_lt_succ hq) (Nat.lt_of_succ_lt_succ hp)

private theorem index_all_zip {f : Ty → Ty → Bool} :
    ∀ {qs ps' : List Ty}, ps'.length = qs.length →
      (∀ i (hq : i < qs.length) (hp : i < ps'.length), f qs[i] ps'[i] = true) →
      (qs.zip ps').all (fun (q, p) => f q p) = true
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | q :: qs, p :: ps', hlen, h => by
      simp only [List.length_cons] at hlen
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
      exact ⟨h 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _),
        index_all_zip (Nat.add_right_cancel hlen) fun i hq hp =>
          h (i + 1) (Nat.succ_lt_succ hq) (Nat.succ_lt_succ hp)⟩

private theorem argsLe_of_index {G : NormalGraph Nat} {η : String → Fam} :
    ∀ {qs ps' : List Ty}, ps'.length = qs.length →
      (∀ i (hq : i < qs.length) (hp : i < ps'.length),
        FamLe (qs[i].denote G η) (ps'[i].denote G η)) →
      ArgsLe (Ty.denoteList G η qs) (Ty.denoteList G η ps')
  | [], [], _, _ => .nil
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | q :: qs, p :: ps', hlen, h => by
      simp only [List.length_cons] at hlen
      exact .cons (h 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))
        (argsLe_of_index (Nat.add_right_cancel hlen) fun i hq hp =>
          h (i + 1) (Nat.succ_lt_succ hq) (Nat.succ_lt_succ hp))

/-! ## Semantic soundness of the judgment itself -/

/-- Under any assignment satisfying the declared bounds, a derivable inclusion
is a semantic inclusion. The executable relation inherits this through
`Sub_of_leUnder`; the judgment does not depend on the executable relation for it. -/
theorem Sub.sound {G : NormalGraph Nat} {η : String → Fam} {ps : List Parameter}
    (hs : Satisfies G η ps) {a b : Ty} (h : Sub ps a b) :
    FamLe (a.denote G η) (b.denote G η) := by
  induction h with
  | @variadic_fixed rc ps' e r extra =>
    simpa [Ty.denote, Ty.denoteList_eq_map] using DirectObligation.variadic_fixed (rc.denote G η)
      (Ty.denoteList G η ps') (e.denote G η) (r.denote G η) extra
  | variadic_refl | array_refl | rigid_refl => exact fun _ _ _ hv => hv
  | bound p hp hn hu _ ih =>
    intro k W v hv
    subst hn
    exact ih k W v ((hs p hp _ hu) k W v hv)
  | ground h =>
    intro k W v hv
    obtain ⟨label, hlabel, hv⟩ := hv
    exact ⟨label, h label hlabel, hv⟩
  | arrow _ hlen _ _ ihrecv ihargs ihres =>
    exact callsT_single_mono ihrecv (argsLe_of_index hlen ihargs) ihres
  | @top a ha =>
    intro k W v hv
    cases a with
    | rigid x => exact absurd rfl (ha x)
    | top => exact hv
    | ground _ => exact ProgramTyping.meaning_value hv
    | arrow _ _ _ | variadic _ _ _ _ => exact ⟨hv.1.val, hv.1.scoped⟩
    | array _ =>
      obtain ⟨fields, rfl, _⟩ := hv
      exact ⟨rfl, trivial⟩

/-! ## Every accepted comparison is derivable -/

theorem Sub_of_follows {ps : List Parameter} {x y : String} :
    ∀ {n : Nat}, follows ps n x y = true → Sub ps (.rigid x) (.rigid y) := by
  intro n
  induction n generalizing x with
  | zero =>
    intro h
    simp only [follows] at h
    split at h
    · next heq => rw [beq_iff_eq.mp heq]; exact .rigid_refl
    · contradiction
  | succ n ih =>
    intro h
    simp only [follows] at h
    split at h
    · next heq => rw [beq_iff_eq.mp heq]; exact .rigid_refl
    · obtain ⟨p, hp, hstep⟩ := List.any_eq_true.mp h
      have hname : p.name = x := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hstep).1
      have htail := (Bool.and_eq_true_iff.mp hstep).2
      split at htail <;> try contradiction
      next upper hu => exact .bound p hp hname hu (ih htail)

/-- Anything below a rigid name is below whatever that name is below. -/
theorem Sub.trans_rigid {ps : List Parameter} {a b : Ty} {y : String}
    (hay : Sub ps a (.rigid y)) (hyb : Sub ps (.rigid y) b) : Sub ps a b := by
  generalize hc : Ty.rigid y = c at hay
  induction hay with
  | rigid_refl => cases hc; exact hyb
  | bound p hp hn hu _ ih => exact .bound p hp hn hu (ih hc)
  | variadic_fixed _ => cases hc
  | array_refl | variadic_refl => cases hc
  | ground _ => cases hc
  | arrow _ _ _ _ _ _ _ => cases hc
  | top _ => cases hc

theorem Sub_of_leUnderFuel {ps : List Parameter} (n : Nat) (a b : Ty)
    (h : Ty.leUnderFuel n ps a b = true) : Sub ps a b := by
  induction n generalizing a b with
  | zero => simp [Ty.leUnderFuel] at h
  | succ n ih =>
    cases a with
    | rigid x =>
      cases b with
      | rigid y =>
        simp only [Ty.leUnderFuel] at h
        exact Sub_of_follows h
      | ground B => exact entered (fun h => ih _ _ h) h
      | variadic _ ps e r => exact entered (fun h => ih _ _ h) h
      | array e => exact entered (fun h => ih _ _ h) h
      | arrow _ qs t => exact entered (fun h => ih _ _ h) h
      | top => exact entered (fun h => ih _ _ h) h
    | top =>
      cases b with
      | top => exact .top (fun _ h => by cases h)
      | rigid _ | ground _ | array _ | variadic _ _ _ _ | arrow _ _ _ =>
        simp [Ty.leUnderFuel] at h
    | ground A =>
      cases b with
      | rigid y | array _ | variadic _ _ _ _ => simp [Ty.leUnderFuel] at h
      | top => exact .top (fun _ h => by cases h)
      | arrow _ qs t => simp [Ty.leUnderFuel] at h
      | ground B =>
        simp only [Ty.leUnderFuel] at h
        exact .ground fun i hi => by simpa using (List.all_eq_true.mp h) i hi
    | arrow rc ps' r =>
      cases b with
      | rigid y | array _ | variadic _ _ _ _ => simp [Ty.leUnderFuel] at h
      | top => exact .top (fun _ h => by cases h)
      | ground B => simp [Ty.leUnderFuel] at h
      | arrow rd qs t =>
        simp only [Ty.leUnderFuel, Bool.and_eq_true] at h
        have hlen := beq_iff_eq.mp h.1.1.2
        exact .arrow (ih _ _ h.1.1.1) hlen
          (fun i hq hp => ih _ _ (all_zip_index hlen h.1.2 i hq hp)) (ih _ _ h.2)
    | array e =>
      cases b with
      | rigid _ | ground _ | arrow _ _ _ | variadic _ _ _ _ => simp [Ty.leUnderFuel] at h
      | top => exact .top (fun _ h => by cases h)
      | array f =>
        have heq : e = f := by simpa [Ty.leUnderFuel] using h
        subst f
        exact .array_refl
    | variadic rc ps' e r =>
      cases b with
      | rigid _ | ground _ | array _ => simp [Ty.leUnderFuel] at h
      | top => exact .top (fun _ h => by cases h)
      | arrow rd qs t =>
        have hh : rc = rd ∧ qs = ps' ++ List.replicate (qs.length - ps'.length) e ∧ r = t := by
          simpa [Ty.leUnderFuel] using h
        obtain ⟨rfl, hq, rfl⟩ := hh
        rw [hq]
        exact .variadic_fixed _
      | variadic rd qs f t =>
        have heq : Ty.variadic rc ps' e r = .variadic rd qs f t := by simpa [Ty.leUnderFuel] using h
        cases heq
        exact .variadic_refl

where
  /-- The executable's walk to a parameter whose bound is not a rigid name,
  followed by entering that bound: a chain of bound steps in the judgment. -/
  entered {n : Nat} {x : String} {b : Ty}
      (ih : ∀ {a b : Ty}, Ty.leUnderFuel n ps a b = true → Sub ps a b)
      (h : (ps.any fun q => match q.upper with
        | some (.rigid _) | none => false
        | some terminal => follows ps ps.length x q.name && Ty.leUnderFuel n ps terminal b) = true) :
      Sub ps (.rigid x) b := by
    obtain ⟨q, hq, hstep⟩ := List.any_eq_true.mp h
    cases hu : q.upper with
    | none => simp [hu] at hstep
    | some upper =>
      cases upper with
      | rigid _ => simp [hu] at hstep
      | variadic _ ps e r | array A | ground A | top =>
        simp only [hu, Bool.and_eq_true] at hstep
        exact (Sub_of_follows hstep.1).trans_rigid (.bound q hq rfl hu (ih hstep.2))
      | arrow _ ps'' r =>
        simp only [hu, Bool.and_eq_true] at hstep
        exact (Sub_of_follows hstep.1).trans_rigid (.bound q hq rfl hu (ih hstep.2))

theorem Sub_of_leUnder {ps : List Parameter} {a b : Ty} (h : Ty.leUnder ps a b = true) :
    Sub ps a b :=
  Sub_of_leUnderFuel _ _ _ h

/-! ## Every derivation is accepted, on well-formed parameters

`parametersOf` builds parameter lists whose names are distinct, whose rigid
bounds name earlier parameters, and whose bounds are ground or rigid. On such
lists the walk through bounds descends, so `ps.length` steps suffice, and a
walk enters at most one bound before reaching ground. -/

structure WellFormed (ps : List Parameter) : Prop where
  injective : ∀ i j (hi : i < ps.length) (hj : j < ps.length), ps[i].name = ps[j].name → i = j
  descending : ∀ i (hi : i < ps.length) y, ps[i].upper = some (.rigid y) →
    ∃ j, j < i ∧ ∃ hj : j < ps.length, ps[j].name = y
  grounded : ∀ i (hi : i < ps.length) u, ps[i].upper = some u →
    (∃ A, u = .ground A) ∨ (∃ y, u = .rigid y)

theorem follows_refl (ps : List Parameter) (n : Nat) (x : String) : follows ps n x x = true := by
  cases n <;> simp [follows]

theorem follows_step {ps : List Parameter} {n : Nat} {x y z : String}
    (p : Parameter) (hp : p ∈ ps) (hn : p.name = x) (hu : p.upper = some (.rigid y))
    (h : follows ps n y z = true) : follows ps (n + 1) x z = true := by
  simp only [follows]
  split
  · rfl
  · exact List.any_eq_true.mpr ⟨p, hp, by simp [hn, hu, h]⟩

theorem follows_mono {ps : List Parameter} {x y : String} :
    ∀ {n : Nat}, follows ps n x y = true → follows ps (n + 1) x y = true := by
  intro n
  induction n generalizing x with
  | zero =>
    intro h
    simp only [follows] at h
    split at h
    · next heq => simp [follows, heq]
    · contradiction
  | succ n ih =>
    intro h
    simp only [follows] at h
    split at h
    · next heq => simp [follows, heq]
    · obtain ⟨p, hp, hstep⟩ := List.any_eq_true.mp h
      have hname : p.name = x := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hstep).1
      have htail := (Bool.and_eq_true_iff.mp hstep).2
      split at htail <;> try contradiction
      next upper hu => exact follows_step p hp hname hu (ih htail)

theorem follows_mono_le {ps : List Parameter} {x y : String} {n m : Nat} (hle : n ≤ m)
    (h : follows ps n x y = true) : follows ps m x y = true := by
  induction hle with
  | refl => exact h
  | step _ ih => exact follows_mono ih

theorem rigid_of_sub_rigid {ps : List Parameter} {u : Ty} {z : String}
    (h : Sub ps u (.rigid z)) : ∃ y, u = .rigid y := by
  generalize hc : Ty.rigid z = c at h
  cases h with
  | rigid_refl => exact ⟨_, rfl⟩
  | bound p _ _ _ _ => exact ⟨_, rfl⟩
  | variadic_fixed _ => cases hc
  | array_refl | variadic_refl => cases hc
  | ground _ => cases hc
  | arrow _ _ _ _ => cases hc
  | top _ => cases hc

/-- Nothing ground or callable is below a rigid name, so a walk between rigid
names on a well-formed list descends the declaration order and needs no more
steps than there are parameters before its start. -/
theorem follows_of_walk {ps : List Parameter} (hw : WellFormed ps) :
    ∀ k i (hik : i < k) (hi : i < ps.length) z,
      Sub ps (.rigid ps[i].name) (.rigid z) → follows ps (i + 1) ps[i].name z = true := by
  intro k
  induction k with
  | zero => intro i hik; exact absurd hik (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hik hi z h
    generalize hx : ps[i].name = x at h ⊢
    generalize hc : Ty.rigid z = c at h
    cases h with
    | rigid_refl => cases hc; exact follows_refl _ _ _
    | top _ => cases hc
    | bound p hp hn hu h' =>
      cases hc
      obtain ⟨y, rfl⟩ := rigid_of_sub_rigid h'
      obtain ⟨i', hi', hpi⟩ := List.getElem_of_mem hp
      have : i' = i := hw.injective i' i hi' hi (by rw [hpi, hn, hx])
      subst this
      obtain ⟨j, hji, hj, hjy⟩ := hw.descending i' hi' y (by rw [hpi]; exact hu)
      have hwalk := ih j (Nat.lt_of_lt_of_le hji (Nat.le_of_lt_succ hik)) hj z (by rw [hjy]; exact h')
      rw [hjy] at hwalk
      exact follows_step p hp hn hu (follows_mono_le (by omega) hwalk)

/-- A walk from a rigid name to a ground type enters exactly one bound, the
ground bound of the last parameter it reaches. -/
theorem terminal_of_walk {ps : List Parameter} (hw : WellFormed ps) :
    ∀ k i (hik : i < k) (hi : i < ps.length) (B : List Nat),
      Sub ps (.rigid ps[i].name) (.ground B) →
      ∃ q, q ∈ ps ∧ ∃ A, q.upper = some (.ground A) ∧
        follows ps (i + 1) ps[i].name q.name = true ∧ Sub ps (.ground A) (.ground B) := by
  intro k
  induction k with
  | zero => intro i hik; exact absurd hik (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hik hi B h
    generalize hx : ps[i].name = x at h ⊢
    generalize hc : Ty.ground B = c at h
    cases h with
    | rigid_refl => cases hc
    | top _ => cases hc
    | bound p hp hn hu h' =>
      cases hc
      obtain ⟨i', hi', hpi⟩ := List.getElem_of_mem hp
      have : i' = i := hw.injective i' i hi' hi (by rw [hpi, hn, hx])
      subst this
      rcases hw.grounded i' hi' _ (by rw [hpi]; exact hu) with ⟨A, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨p, hp, A, hu, by rw [← hn]; exact follows_refl _ _ _, h'⟩
      · obtain ⟨j, hji, hj, hjy⟩ := hw.descending i' hi' y (by rw [hpi]; exact hu)
        obtain ⟨q, hq, A, hqu, hwalk, hsub⟩ :=
          ih j (Nat.lt_of_lt_of_le hji (Nat.le_of_lt_succ hik)) hj B (by rw [hjy]; exact h')
        rw [hjy] at hwalk
        exact ⟨q, hq, A, hqu, follows_step p hp hn hu (follows_mono_le (by omega) hwalk), hsub⟩

/-- A walk from a rigid name to top enters exactly one bound, the ground bound
of the last parameter it reaches, which is below top. -/
theorem terminal_of_walk_top {ps : List Parameter} (hw : WellFormed ps) :
    ∀ k i (hik : i < k) (hi : i < ps.length),
      Sub ps (.rigid ps[i].name) .top →
      ∃ q, q ∈ ps ∧ ∃ A, q.upper = some (.ground A) ∧
        follows ps (i + 1) ps[i].name q.name = true := by
  intro k
  induction k with
  | zero => intro i hik; exact absurd hik (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hik hi h
    generalize hx : ps[i].name = x at h ⊢
    generalize hc : Ty.top = c at h
    cases h with
    | top ha => exact absurd rfl (ha x)
    | bound p hp hn hu h' =>
      cases hc
      obtain ⟨i', hi', hpi⟩ := List.getElem_of_mem hp
      have : i' = i := hw.injective i' i hi' hi (by rw [hpi, hn, hx])
      subst this
      rcases hw.grounded i' hi' _ (by rw [hpi]; exact hu) with ⟨A, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨p, hp, A, hu, by rw [← hn]; exact follows_refl _ _ _⟩
      · obtain ⟨j, hji, hj, hjy⟩ := hw.descending i' hi' y (by rw [hpi]; exact hu)
        obtain ⟨q, hq, A, hqu, hwalk⟩ :=
          ih j (Nat.lt_of_lt_of_le hji (Nat.le_of_lt_succ hik)) hj (by rw [hjy]; exact h')
        rw [hjy] at hwalk
        exact ⟨q, hq, A, hqu, follows_step p hp hn hu (follows_mono_le (by omega) hwalk)⟩
    | rigid_refl => cases hc

/-- On a well-formed list no rigid name is below a callable: its bounds end in
ground types, and nothing ground is below a callable. -/
theorem no_rigid_below_arrow {ps : List Parameter} (hw : WellFormed ps) :
    ∀ k i (hik : i < k) (hi : i < ps.length) (rc : Ty) (qs : List Ty) (t : Ty),
      Sub ps (.rigid ps[i].name) (.arrow rc qs t) → False := by
  intro k
  induction k with
  | zero => intro i hik; exact absurd hik (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hik hi rc qs t h
    generalize hx : ps[i].name = x at h
    generalize hc : Ty.arrow rc qs t = c at h
    cases h with
    | rigid_refl => cases hc
    | top _ => cases hc
    | bound p hp hn hu h' =>
      cases hc
      obtain ⟨i', hi', hpi⟩ := List.getElem_of_mem hp
      have : i' = i := hw.injective i' i hi' hi (by rw [hpi, hn, hx])
      subst this
      rcases hw.grounded i' hi' _ (by rw [hpi]; exact hu) with ⟨A, rfl⟩ | ⟨y, rfl⟩
      · generalize hd : Ty.ground A = d at h'
        cases h' <;> cases hd
      · obtain ⟨j, hji, hj, hjy⟩ := hw.descending i' hi' y (by rw [hpi]; exact hu)
        exact ih j (Nat.lt_of_lt_of_le hji (Nat.le_of_lt_succ hik)) hj rc qs t (by rw [hjy]; exact h')

theorem no_rigid_below_array {ps : List Parameter} (hw : WellFormed ps) :
    ∀ k i (hik : i < k) (hi : i < ps.length) (e : Ty),
      Sub ps (.rigid ps[i].name) (.array e) → False := by
  intro k
  induction k with
  | zero => intro i hik; exact absurd hik (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hik hi e h
    generalize hx : ps[i].name = x at h
    generalize hc : Ty.array e = c at h
    cases h with
    | rigid_refl => cases hc
    | top _ => cases hc
    | bound p hp hn hu h' =>
      cases hc
      obtain ⟨i', hi', hpi⟩ := List.getElem_of_mem hp
      have : i' = i := hw.injective i' i hi' hi (by rw [hpi, hn, hx])
      subst this
      rcases hw.grounded i' hi' _ (by rw [hpi]; exact hu) with ⟨A, rfl⟩ | ⟨y, rfl⟩
      · generalize hd : Ty.ground A = d at h'
        cases h' <;> cases hd
      · obtain ⟨j, hji, hj, hjy⟩ := hw.descending i' hi' y (by rw [hpi]; exact hu)
        exact ih j (Nat.lt_of_lt_of_le hji (Nat.le_of_lt_succ hik)) hj e (by rw [hjy]; exact h')

theorem no_rigid_below_variadic {ps : List Parameter} (hw : WellFormed ps) :
    ∀ k i (hik : i < k) (hi : i < ps.length) (rc : Ty) (qs : List Ty) (e r : Ty),
      Sub ps (.rigid ps[i].name) (.variadic rc qs e r) → False := by
  intro k
  induction k with
  | zero => intro i hik; exact absurd hik (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hik hi rc qs e r h
    generalize hx : ps[i].name = x at h
    generalize hc : Ty.variadic rc qs e r = c at h
    cases h with
    | rigid_refl => cases hc
    | top _ => cases hc
    | bound p hp hn hu h' =>
      cases hc
      obtain ⟨i', hi', hpi⟩ := List.getElem_of_mem hp
      have : i' = i := hw.injective i' i hi' hi (by rw [hpi, hn, hx])
      subst this
      rcases hw.grounded i' hi' _ (by rw [hpi]; exact hu) with ⟨A, rfl⟩ | ⟨y, rfl⟩
      · generalize hd : Ty.ground A = d at h'
        cases h' <;> cases hd
      · obtain ⟨j, hji, hj, hjy⟩ := hw.descending i' hi' y (by rw [hpi]; exact hu)
        exact ih j (Nat.lt_of_lt_of_le hji (Nat.le_of_lt_succ hik)) hj rc qs e r (by rw [hjy]; exact h')

theorem leUnderFuel_ground {ps : List Parameter} {A B : List Nat}
    (h : Sub ps (.ground A) (.ground B)) : ∀ n, 1 ≤ n → Ty.leUnderFuel n ps (.ground A) (.ground B) = true := by
  intro n hn
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ m =>
    generalize ha : Ty.ground A = a at h
    generalize hb : Ty.ground B = b at h
    cases h with
    | ground hAB =>
      cases ha; cases hb
      simp only [Ty.leUnderFuel]
      exact List.all_eq_true.mpr fun i hi => by simpa using hAB i hi
    | variadic_fixed _ => cases ha
    | array_refl | variadic_refl => cases ha
    | rigid_refl => cases ha
    | bound _ _ _ _ _ => cases ha
    | arrow _ _ _ _ => cases ha
    | top _ => cases hb

/-! ### Depth arithmetic -/

theorem foldl_max_init_le : ∀ (l : List Nat) (init : Nat), init ≤ l.foldl max init
  | [], _ => Nat.le_refl _
  | a :: l, init => Nat.le_trans (Nat.le_max_left init a) (foldl_max_init_le l (max init a))

theorem le_foldl_max_of_mem : ∀ (l : List Nat) (init x : Nat), x ∈ l → x ≤ l.foldl max init
  | [], _, _, h => absurd h (List.not_mem_nil)
  | a :: l, init, x, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_trans (Nat.le_max_right init x) (foldl_max_init_le l (max init x))
      · exact le_foldl_max_of_mem l (max init a) x h

theorem depth_param_lt {rc : Ty} {ps' : List Ty} {r : Ty} (i : Nat) (hi : i < ps'.length) :
    ps'[i].depth < (Ty.arrow rc ps' r).depth := by
  simp only [Ty.depth]
  have := le_foldl_max_of_mem (ps'.map Ty.depth) (max rc.depth r.depth) ps'[i].depth
    (List.mem_map.mpr ⟨ps'[i], List.getElem_mem hi, rfl⟩)
  omega

theorem depth_result_lt {rc : Ty} {ps' : List Ty} {r : Ty} :
    r.depth < (Ty.arrow rc ps' r).depth := by
  simp only [Ty.depth]
  have := foldl_max_init_le (ps'.map Ty.depth) (max rc.depth r.depth)
  have := Nat.le_max_right rc.depth r.depth
  omega

theorem depth_receiver_lt {rc : Ty} {ps' : List Ty} {r : Ty} :
    rc.depth < (Ty.arrow rc ps' r).depth := by
  simp only [Ty.depth]
  have := foldl_max_init_le (ps'.map Ty.depth) (max rc.depth r.depth)
  have := Nat.le_max_left rc.depth r.depth
  omega

theorem depth_pos : ∀ a : Ty, 1 ≤ a.depth
  | .top => by simp [Ty.depth]
  | .rigid _ => by simp [Ty.depth]
  | .ground _ => by simp [Ty.depth]
  | .array _ | .variadic .. => by simp only [Ty.depth]; omega
  | .arrow _ _ _ => by simp only [Ty.depth]; omega

/-- The fuel a derivation needs: one step per structural level of either
side, and one more to enter a bound from a rigid name. -/
def need (a b : Ty) : Nat :=
  a.depth + b.depth + (match a with | .rigid _ => 1 | _ => 0)

theorem need_le (a b : Ty) : need a b ≤ a.depth + b.depth + 1 := by
  unfold need; split <;> omega

theorem leUnderFuel_of_Sub {ps : List Parameter} (hw : WellFormed ps) {a b : Ty} (h : Sub ps a b) :
    ∀ n, need a b ≤ n → Ty.leUnderFuel n ps a b = true := by
  induction h with
  | variadic_fixed extra =>
    intro n hn
    cases n with
    | zero => simp [need, Ty.depth] at hn
    | succ m => simp [Ty.leUnderFuel]
  | variadic_refl | array_refl =>
    intro n hn
    cases n with
    | zero => simp [need, Ty.depth] at hn
    | succ m => simp [Ty.leUnderFuel]
  | rigid_refl =>
    intro n hn
    cases n with
    | zero => simp [need, Ty.depth] at hn
    | succ m => simp [Ty.leUnderFuel, follows_refl]
  | @bound x u b p hp hn hu h' _ =>
    intro n hle
    cases n with
    | zero => simp [need, Ty.depth] at hle
    | succ m =>
      have full : Sub ps (.rigid x) b := .bound p hp hn hu h'
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hp
      have hxi : ps[i].name = x := by rw [hpi, hn]
      cases b with
      | rigid z =>
        simp only [Ty.leUnderFuel]
        have := follows_of_walk hw ps.length i hi hi z (by rw [hxi]; exact full)
        rw [hxi] at this
        exact follows_mono_le (by omega) this
      | ground B =>
        obtain ⟨q, hq, A, hqu, hwalk, hsub⟩ :=
          terminal_of_walk hw ps.length i hi hi B (by rw [hxi]; exact full)
        rw [hxi] at hwalk
        simp only [Ty.leUnderFuel]
        refine List.any_eq_true.mpr ⟨q, hq, ?_⟩
        simp only [hqu, Bool.and_eq_true]
        refine ⟨follows_mono_le (by omega) hwalk, leUnderFuel_ground hsub m ?_⟩
        simp [need, Ty.depth] at hle
        omega
      | variadic rc qs e r =>
        exact absurd (by rw [hxi]; exact full)
          (no_rigid_below_variadic hw ps.length i hi hi rc qs e r)
      | array e =>
        exact absurd (by rw [hxi]; exact full) (no_rigid_below_array hw ps.length i hi hi e)
      | arrow rc qs t =>
        exact absurd (by rw [hxi]; exact full) (no_rigid_below_arrow hw ps.length i hi hi rc qs t)
      | top =>
        obtain ⟨q, hq, A, hqu, hwalk⟩ :=
          terminal_of_walk_top hw ps.length i hi hi (by rw [hxi]; exact full)
        rw [hxi] at hwalk
        simp only [Ty.leUnderFuel]
        refine List.any_eq_true.mpr ⟨q, hq, ?_⟩
        simp only [hqu, Bool.and_eq_true]
        refine ⟨follows_mono_le (by omega) hwalk, ?_⟩
        simp [need, Ty.depth] at hle
        cases m with
        | zero => omega
        | succ m => simp [Ty.leUnderFuel]
  | ground hAB =>
    intro n hn
    exact leUnderFuel_ground (.ground hAB) n (by simp [need, Ty.depth] at hn; omega)
  | @top a ha =>
    intro n hn
    cases n with
    | zero => have := depth_pos a; simp [need] at hn; omega
    | succ m =>
      cases a with
      | rigid x => exact absurd rfl (ha x)
      | top | ground _ | arrow _ _ _ | array _ | variadic _ _ _ _ => simp [Ty.leUnderFuel]
  | @arrow rc rd qs ps' r t _ hlen _ _ ihrecv ihargs ihres =>
    intro n hle
    cases n with
    | zero => simp [need, Ty.depth] at hle
    | succ m =>
      simp only [Ty.leUnderFuel, Bool.and_eq_true]
      have hr := depth_result_lt (rc := rc) (ps' := ps') (r := r)
      have ht := depth_result_lt (rc := rd) (ps' := qs) (r := t)
      have hrc := depth_receiver_lt (rc := rc) (ps' := ps') (r := r)
      have hrd := depth_receiver_lt (rc := rd) (ps' := qs) (r := t)
      simp only [need] at hle
      refine ⟨⟨⟨ihrecv m ?_, beq_iff_eq.mpr hlen⟩,
        index_all_zip hlen fun i hq hp => ihargs i hq hp m ?_⟩, ihres m ?_⟩
      · have := need_le rd rc
        omega
      · have hq' := depth_param_lt (rc := rd) (ps' := qs) (r := t) i hq
        have hp' := depth_param_lt (rc := rc) (ps' := ps') (r := r) i hp
        have := need_le qs[i] ps'[i]
        omega
      · have := need_le r t
        omega

/-- The executable relation decides the judgment on well-formed parameters. -/
theorem leUnder_of_Sub {ps : List Parameter} (hw : WellFormed ps) {a b : Ty} (h : Sub ps a b) :
    Ty.leUnder ps a b = true := by
  unfold Ty.leUnder
  apply leUnderFuel_of_Sub hw h
  have := need_le a b
  omega

theorem leUnder_iff_Sub {ps : List Parameter} (hw : WellFormed ps) {a b : Ty} :
    Ty.leUnder ps a b = true ↔ Sub ps a b :=
  ⟨Sub_of_leUnder, leUnder_of_Sub hw⟩

/-! ## The counterexample the structural fuel could not decide

Before `upperDepths` was part of the fuel, `Ty.leUnder` charged only for the
structure of the two sides and one step per parameter. A parameter bounded by
a deep callable is declaratively below that callable, yet the walk into the
bound needs as many steps as the callable is deep. The judgment holds; the old
fuel is exhausted; the repaired fuel decides it. -/

/-- A receiver for the arrows below: one ground label. -/
def anyReceiver : Ty := .ground [0]

/-- `() => () => ... => boolean`, `n` arrows deep. -/
def deep : Nat → Ty
  | 0 => .ground [1, 2]
  | n + 1 => .arrow anyReceiver [] (deep n)

def counterexampleParameters : List Parameter :=
  [⟨"y", .quantified, some (deep 9)⟩,
   ⟨"x", .quantified, some (.arrow anyReceiver [deep 9] (.ground [1, 2]))⟩]

def counterexampleLeft : Ty := .rigid "x"
def counterexampleRight : Ty := .arrow anyReceiver [.rigid "y"] (.ground [1, 2])

theorem counterexample_derivable :
    Sub counterexampleParameters counterexampleLeft counterexampleRight :=
  .bound ⟨"x", .quantified, some (.arrow anyReceiver [deep 9] (.ground [1, 2]))⟩
    (by simp [counterexampleParameters]) rfl rfl
    (.arrow (Sub.refl _ _) rfl
      (fun i hq hp => by
        cases i with
        | zero =>
          exact .bound ⟨"y", .quantified, some (deep 9)⟩
            (by simp [counterexampleParameters]) rfl rfl (Sub.refl _ _)
        | succ i => simp at hq)
      (Sub.refl _ _))

-- The structural fuel: two parameters, depth 1 on the left, depth 2 on the right, plus one.
#guard Ty.leUnderFuel 6 counterexampleParameters counterexampleLeft counterexampleRight = false
-- The repaired fuel decides it.
#guard Ty.leUnder counterexampleParameters counterexampleLeft counterexampleRight = true

#print axioms Sub.sound
#print axioms Sub_of_leUnder
#print axioms leUnder_iff_Sub
end Verification.Model.RigidJudgments
