import Verification.Model.Source.GenericSource
import Verification.Model.Programs.CertificateJudgments

/-! # The source checker decides the declarative judgments

`GenericSource` is the executable checker for bodies under rigid binders. This
module connects it to the declarative judgments of `RigidJudgments` and
`CertificateJudgments`: the parameter lists it builds are well-formed, so
`Ty.leUnder` decides `Sub` on every list the checker uses. -/
namespace Verification.Model.SourceJudgments
open DirectObligation RigidJudgments GenericSource

theorem WellFormed.nil : WellFormed ([] : List Parameter) :=
  ⟨fun i _ hi => absurd hi (Nat.not_lt_zero _),
   fun i hi => absurd hi (Nat.not_lt_zero _),
   fun i hi => absurd hi (Nat.not_lt_zero _)⟩

private theorem getElem_snoc_left {ps : List Parameter} {q : Parameter} {i : Nat}
    (hi : i < ps.length) (h : i < (ps ++ [q]).length) : (ps ++ [q])[i] = ps[i] :=
  List.getElem_append_left hi

private theorem getElem_snoc_right {ps : List Parameter} {q : Parameter}
    (h : ps.length < (ps ++ [q]).length) : (ps ++ [q])[ps.length] = q := by
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

/-- Appending a parameter whose name is new and whose bound names an earlier
parameter, or is ground, keeps the list well-formed. -/
theorem WellFormed.snoc {ps : List Parameter} (hw : WellFormed ps) {q : Parameter}
    (hname : ∀ p ∈ ps, p.name ≠ q.name)
    (hupper : ∀ u, q.upper = some u →
      (∃ A, u = .ground A) ∨ (∃ y, u = .rigid y ∧ ∃ p ∈ ps, p.name = y)) :
    WellFormed (ps ++ [q]) := by
  have hlen : (ps ++ [q]).length = ps.length + 1 := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj heq
    by_cases hi' : i < ps.length <;> by_cases hj' : j < ps.length
    · rw [getElem_snoc_left hi', getElem_snoc_left hj'] at heq
      exact hw.injective i j hi' hj' heq
    · have hj'' : j = ps.length := by omega
      subst hj''
      rw [getElem_snoc_left hi', getElem_snoc_right] at heq
      exact absurd heq (hname _ (List.getElem_mem hi'))
    · have hi'' : i = ps.length := by omega
      subst hi''
      rw [getElem_snoc_right, getElem_snoc_left hj'] at heq
      exact absurd heq.symm (hname _ (List.getElem_mem hj'))
    · omega
  · intro i hi y hu
    by_cases hi' : i < ps.length
    · rw [getElem_snoc_left hi'] at hu
      obtain ⟨j, hji, hj, hjy⟩ := hw.descending i hi' y hu
      exact ⟨j, hji, by omega, by rw [getElem_snoc_left hj]; exact hjy⟩
    · have hi'' : i = ps.length := by omega
      subst hi''
      rw [getElem_snoc_right] at hu
      rcases hupper _ hu with ⟨_, h⟩ | ⟨y', hy, p, hp, hpy⟩
      · cases h
      · cases hy
        obtain ⟨j, hj, hpj⟩ := List.getElem_of_mem hp
        exact ⟨j, hj, by omega, by rw [getElem_snoc_left hj, hpj]; exact hpy⟩
  · intro i hi u hu
    by_cases hi' : i < ps.length
    · rw [getElem_snoc_left hi'] at hu
      exact hw.grounded i hi' u hu
    · have hi'' : i = ps.length := by omega
      subst hi''
      rw [getElem_snoc_right] at hu
      rcases hupper u hu with ⟨A, hA⟩ | ⟨y, hy, _⟩
      · exact .inl ⟨A, hA⟩
      · exact .inr ⟨y, hy⟩

private theorem boundOf_some (T : SourceTypes.Table) (seen : List Parameter) (bound : Lean.Json) :
    boundOf T seen (some bound) =
      (if isBooleanType bound then .ok (some (DirectObligation.Ty.ground [1, 2]))
      else match paramName bound with
        | .ok u =>
          if seen.any (·.name == u) then .ok (some (DirectObligation.Ty.rigid u))
          else .error "a type-parameter bound must name an earlier parameter"
        | .error _ => match declaredBound T bound with
          | .ok labels => .ok (some (.ground labels))
          | .error _ => .error "a type-parameter bound is a ground type or an earlier type parameter") :=
  rfl

theorem boundOf_upper {T : SourceTypes.Table} {seen : List Parameter} {b : Option Lean.Json} {u : Ty}
    (h : boundOf T seen b = .ok (some u)) :
    (∃ A, u = .ground A) ∨ (∃ y, u = .rigid y ∧ ∃ p ∈ seen, p.name = y) := by
  cases b with
  | none => cases h
  | some bound =>
    rw [boundOf_some] at h
    split at h
    · exact .inl ⟨_, (Option.some.inj (Except.ok.inj h)).symm⟩
    · split at h
      · next name hname =>
        split at h
        · next hany =>
          obtain ⟨p, hp, hpn⟩ := List.any_eq_true.mp hany
          exact .inr ⟨name, (Option.some.inj (Except.ok.inj h)).symm, p, hp, beq_iff_eq.mp hpn⟩
        · cases h
      · split at h
        · exact .inl ⟨_, (Option.some.inj (Except.ok.inj h)).symm⟩
        · cases h

private theorem go_cons (T : SourceTypes.Table) (seen : List Parameter) (tp : Fragment.TypeParam) (rest : List Fragment.TypeParam) :
    parametersOf.go T seen (tp :: rest) =
      (if tp.name == "undefined" then .error "shadowing undefined is outside the fragment"
      else if seen.any (·.name == tp.name) then .error "duplicate type parameter"
      else match boundOf T seen tp.bound with
        | .error e => .error e
        | .ok upper => parametersOf.go T (seen ++ [⟨tp.name, .quantified, upper⟩]) rest) :=
  rfl

theorem go_wellFormed (T : SourceTypes.Table) : ∀ (tps : List Fragment.TypeParam) (seen ps : List Parameter),
    WellFormed seen → parametersOf.go T seen tps = .ok ps → WellFormed ps
  | [], seen, ps, hw, h => by
      cases Except.ok.inj (h : (Except.ok seen : Except String (List Parameter)) = .ok ps)
      exact hw
  | tp :: rest, seen, ps, hw, h => by
      rw [go_cons] at h
      split at h
      · cases h
      split at h
      · cases h
      next hdup =>
      split at h
      · cases h
      next upper hupper =>
      refine go_wellFormed T rest _ ps (WellFormed.snoc hw ?_ ?_) h
      · intro p hp heq
        apply hdup
        exact List.any_eq_true.mpr ⟨p, hp, beq_iff_eq.mpr heq⟩
      · intro u hu
        simp only at hu
        subst hu
        exact boundOf_upper hupper

/-- Every parameter list the checker builds is well-formed, so the executable
inclusion relation decides the declarative judgment on it. -/
theorem parametersOf_wellFormed {T : SourceTypes.Table} {tps : List Fragment.TypeParam} {ps : List Parameter}
    (h : parametersOf T tps = .ok ps) : WellFormed ps :=
  go_wellFormed T tps [] ps WellFormed.nil h

theorem leUnder_iff_Sub_of_parametersOf {T : SourceTypes.Table} {tps : List Fragment.TypeParam} {ps : List Parameter}
    (h : parametersOf T tps = .ok ps) {a b : Ty} : Ty.leUnder ps a b = true ↔ Sub ps a b :=
  leUnder_iff_Sub (parametersOf_wellFormed h)

#print axioms parametersOf_wellFormed

/-! ## Expressions

`HasTy c env b t` is the typing judgment of a lowered body under the binders
and claims in `c`. A variable has its environment type; a primitive literal
its singleton; an assignment writes a value below the cell's contract and has
the value's type; a call names a callable binding and passes each argument
below its parameter; a closure is claimed exactly as annotated, its body below
its declared result. There is no general subsumption: inclusions appear where
the source imposes them. `exprTyB` decides it. -/

inductive HasTy (c : Ctx) : List (String × Ty) → Body → Ty → Prop
  | var {env : List (String × Ty)} {pos : Span} {name : String} {t : Ty}
      (h : env.lookup name = some t) : HasTy c env (.var pos name) t
  | null {env : List (String × Ty)} {pos : Span} : HasTy c env (.lit pos .vnull) (.ground [0])
  | tru {env : List (String × Ty)} {pos : Span} : HasTy c env (.lit pos (.vbool true)) (.ground [1])
  | fls {env : List (String × Ty)} {pos : Span} : HasTy c env (.lit pos (.vbool false)) (.ground [2])
  | undef {env : List (String × Ty)} {pos : Span} : HasTy c env (.lit pos .vundef) (.ground [3])
  | assign {env : List (String × Ty)} {pos : Span} {name : String} {rhs : Body} {t k : Ty}
      (hc : c.cells.contains name = true) (hk : env.lookup name = some k)
      (h : HasTy c env rhs t) (hle : Sub c.parameters t k) :
      HasTy c env (.assign pos name rhs) t
  /-- Each argument has a type below its parameter; `ts` lists those types.
  The call passes `undefined` as the receiver, which the callable admits. -/
  | call {env : List (String × Ty)} {pos cpos : Span} {name : String} {args : List Body}
      {rc : Ty} {ps ts : List Ty} {r : Ty}
      (hf : env.lookup name = some (.arrow rc ps r)) (hrecv : Sub c.parameters (.ground [3]) rc)
      (hlen : ps.length = args.length)
      (hts : ts.length = args.length)
      (hargs : ∀ i (ha : i < args.length) (ht : i < ts.length), HasTy c env args[i] ts[i])
      (hle : ∀ i (ht : i < ts.length) (hp : i < ps.length), Sub c.parameters ts[i] ps[i]) :
      HasTy c env (.call pos (.var cpos name) args) r
  | callRest {env : List (String × Ty)} {pos cpos : Span} {name : String} {args : List Body}
      {rc : Ty} {ps ts : List Ty} {e r : Ty}
      (hf : env.lookup name = some (.variadic rc ps e r)) (hrecv : Sub c.parameters (.ground [3]) rc)
      (hlen : ps.length ≤ args.length)
      (hts : ts.length = args.length)
      (hargs : ∀ i (ha : i < args.length) (ht : i < ts.length), HasTy c env args[i] ts[i])
      (hle : ∀ i (ht : i < ts.length)
        (hp : i < (ps ++ List.replicate (args.length - ps.length) e).length),
        Sub c.parameters ts[i] (ps ++ List.replicate (args.length - ps.length) e)[i]) :
      HasTy c env (.call pos (.var cpos name) args) r
  | lambda {env : List (String × Ty)} {pos : Span} {ps : List (String × Ty)} {declared : Ty}
      {body : Body} {t : Ty}
      (hclaim : c.claims.exprs.lookup pos = some (.arrow .top (ps.map Prod.snd) declared))
      (h : HasTy c (ps ++ env) body t) (hle : Sub c.parameters t declared) :
      HasTy c env (.lambda pos ps declared body) (.arrow .top (ps.map Prod.snd) declared)

theorem requireLeE_ok {c : Ctx} {env : List (String × Ty)} {role : SourceRole}
    {subject : Subject} {a b : Ty} :
    requireLeE c env role subject a b = .ok () ↔ Ty.leUnder c.parameters a b = true := by
  unfold requireLeE
  constructor
  · intro h
    split at h
    · assumption
    · cases h
  · intro h
    simp [h]

theorem argsTyB_nil {c : Ctx} {env : List (String × Ty)} : argsTyB c env [] [] = .ok () := by
  simp [argsTyB]

theorem requireLeE_of_le (c : Ctx) (env : List (String × Ty)) (role : SourceRole)
    (subject : Subject) {a b : Ty} (h : Ty.leUnder c.parameters a b = true) :
    requireLeE c env role subject a b = .ok () := by
  unfold requireLeE
  simp [h]

/-! ### Every accepted expression is derivable -/

mutual

theorem HasTy_of_exprTyB {c : Ctx} : ∀ (b : Body) {env : List (String × Ty)} {t : Ty},
    exprTyB c env b = .ok t → HasTy c env b t
  | .var pos name, env, t, h => by
      simp only [exprTyB] at h
      split at h
      · next hk => cases h; exact .var hk
      · cases h
  | .lit pos v, env, t, h => by
      cases v with
      | vnull => simp only [exprTyB] at h; cases h; exact .null
      | vundef => simp only [exprTyB] at h; cases h; exact .undef
      | vbool b => cases b <;> (try simp only [exprTyB] at h) <;> cases h <;> constructor
      | vnum _ => simp only [exprTyB] at h; cases h
      | vstr _ => simp only [exprTyB] at h; cases h
      | vbigint _ => simp only [exprTyB] at h; cases h
  | .assign pos name rhs, env, t, h => by
      simp only [exprTyB] at h
      split at h
      · cases h
      · next hcell =>
        split at h
        · cases h
        · next k hk =>
          split at h
          · cases h
          · next actual hr =>
            split at h
            · cases h
            · next hle =>
              cases h
              exact .assign (by simpa using hcell) hk (HasTy_of_exprTyB rhs hr)
                (Sub_of_leUnder (requireLeE_ok.mp hle))
  | .call pos callee args, env, t, h => by
      cases callee with
      | var cpos name =>
        simp only [exprTyB] at h
        split at h
        · next rc ps r hf =>
          split at h
          · cases h
          · next hrecv =>
            split at h
            · cases h
            · next hlen =>
              split at h
              · cases h
              · next hargs =>
                cases h
                have hlen' : ps.length = args.length := by simpa using hlen
                obtain ⟨ts, hts, hty, hsub⟩ := Args_of_argsTyB ps args hargs hlen'
                exact .call hf (Sub_of_leUnder (by simpa using hrecv)) hlen' hts hty hsub
        · next rc ps e r hf =>
          split at h
          · cases h
          · next hrecv =>
            split at h
            · cases h
            · next hlen =>
              split at h
              · cases h
              · next hargs =>
                cases h
                have hlen' : ps.length ≤ args.length := by omega
                have hl : (ps ++ List.replicate (args.length - ps.length) e).length = args.length := by
                  simp only [List.length_append, List.length_replicate]; omega
                obtain ⟨ts, hts, hty, hsub⟩ := Args_of_argsTyB _ args hargs hl
                exact .callRest hf (Sub_of_leUnder (by simpa using hrecv)) hlen' hts hty hsub
        · cases h
      | lit _ _ => simp only [exprTyB] at h; cases h
      | assign _ _ _ => simp only [exprTyB] at h; cases h
      | call _ _ _ => simp only [exprTyB] at h; cases h
      | lambda _ _ _ _ => simp only [exprTyB] at h; cases h
  | .lambda pos ps declared body, env, t, h => by
      simp only [exprTyB] at h
      split at h
      · cases h
      · next claim hclaim =>
        split at h
        · next heq =>
          subst heq
          unfold closureTyB at h
          split at h
          · cases h
          · next actual hb =>
            split at h
            · next hle => cases h; exact .lambda hclaim (HasTy_of_exprTyB body hb) (Sub_of_leUnder hle)
            · cases h
        · cases h

theorem Args_of_argsTyB {c : Ctx} {env : List (String × Ty)} :
    ∀ (ps : List Ty) (args : List Body), argsTyB c env ps args = .ok () → ps.length = args.length →
      ∃ ts : List Ty, ts.length = args.length ∧
        (∀ i (ha : i < args.length) (ht : i < ts.length), HasTy c env args[i] ts[i]) ∧
        (∀ i (ht : i < ts.length) (hp : i < ps.length), Sub c.parameters ts[i] ps[i])
  | [], [], _, _ => ⟨[], rfl, fun i ha => absurd ha (Nat.not_lt_zero _),
      fun i ht => absurd ht (Nat.not_lt_zero _)⟩
  | [], _ :: _, _, hlen => by simp at hlen
  | _ :: _, [], _, hlen => by simp at hlen
  | p :: ps, a :: args, h, hlen => by
      simp only [argsTyB] at h
      split at h
      · cases h
      · next actual hact =>
        split at h
        · cases h
        · next hle =>
          simp only [List.length_cons] at hlen
          obtain ⟨ts, hts, hty, hsub⟩ := Args_of_argsTyB ps args h (Nat.add_right_cancel hlen)
          refine ⟨actual :: ts, by simp [hts], ?_, ?_⟩
          · intro i ha ht
            cases i with
            | zero => exact HasTy_of_exprTyB a hact
            | succ i => exact hty i (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ ht)
          · intro i ht hp
            cases i with
            | zero => exact Sub_of_leUnder (requireLeE_ok.mp hle)
            | succ i => exact hsub i (Nat.lt_of_succ_lt_succ ht) (Nat.lt_of_succ_lt_succ hp)

end

/-! ### On well-formed binders, every derivation is accepted -/

theorem argsTyB_of_Args {c : Ctx} (hw : WellFormed c.parameters) {env : List (String × Ty)} :
    ∀ (ps ts : List Ty) (args : List Body), ps.length = args.length → ts.length = args.length →
      (∀ i (ha : i < args.length) (ht : i < ts.length), exprTyB c env args[i] = .ok ts[i]) →
      (∀ i (ht : i < ts.length) (hp : i < ps.length), Sub c.parameters ts[i] ps[i]) →
      argsTyB c env ps args = .ok ()
  | [], [], [], _, _, _, _ => argsTyB_nil
  | [], _, _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, _, [], hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _ :: _, _, hts, _, _ => by simp at hts
  | p :: ps, t :: ts, a :: args, hlen, hts, hty, hsub => by
      simp only [List.length_cons] at hlen hts
      have ht : exprTyB c env a = .ok t := hty 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      have hle : requireLeE c env .callArgument (.expression a.span) t p = .ok () :=
        requireLeE_of_le c env _ _ (leUnder_of_Sub hw (hsub 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)))
      have ih := argsTyB_of_Args hw ps ts args (Nat.add_right_cancel hlen) (Nat.add_right_cancel hts)
        (fun i ha ht => hty (i + 1) (Nat.succ_lt_succ ha) (Nat.succ_lt_succ ht))
        (fun i ht hp => hsub (i + 1) (Nat.succ_lt_succ ht) (Nat.succ_lt_succ hp))
      simp only [argsTyB]
      split
      · next e he => rw [ht] at he; cases he
      · next actual hact =>
        rw [ht] at hact
        cases hact
        split
        · next e he => rw [hle] at he; cases he
        · exact ih

theorem exprTyB_of_HasTy {c : Ctx} (hw : WellFormed c.parameters) {env : List (String × Ty)}
    {b : Body} {t : Ty} (h : HasTy c env b t) : exprTyB c env b = .ok t := by
  induction h with
  | var hk => simp [exprTyB, hk]
  | null => simp [exprTyB]
  | tru => simp [exprTyB]
  | fls => simp [exprTyB]
  | undef => simp [exprTyB]
  | @assign env pos name rhs t k hc hk _ hle ih =>
    have hle' := requireLeE_of_le c env .storageWrite (.expression pos) (leUnder_of_Sub hw hle)
    have hmem : name ∈ c.cells := by simpa using hc
    simp [exprTyB, hmem, hk, ih, hle']
  | @call env pos cpos name args rc ps ts r hf hrecv hlen hts _ hsub ih =>
    have hargs := argsTyB_of_Args hw ps ts args hlen hts ih hsub
    simp [exprTyB, hf, hlen, hargs, leUnder_of_Sub hw hrecv]
  | @callRest env pos cpos name args rc ps ts e r hf hrecv hlen hts _ hsub ih =>
    have hl : (ps ++ List.replicate (args.length - ps.length) e).length = args.length := by
      simp only [List.length_append, List.length_replicate]; omega
    have hargs := argsTyB_of_Args hw _ ts args hl hts ih hsub
    simp [exprTyB, hf, show ¬ps.length > args.length by omega, hargs, leUnder_of_Sub hw hrecv]
  | lambda hclaim _ hle ih =>
    simp [exprTyB, hclaim, closureTyB, ih, leUnder_of_Sub hw hle]

theorem exprTyB_iff_HasTy {c : Ctx} (hw : WellFormed c.parameters) {env : List (String × Ty)}
    {b : Body} {t : Ty} : exprTyB c env b = .ok t ↔ HasTy c env b t :=
  ⟨HasTy_of_exprTyB b, exprTyB_of_HasTy hw⟩

#print axioms exprTyB_iff_HasTy

/-- A closure is accepted exactly when its body has a type at most its
declared result, under its parameters and then the scope around it. A
quantified ordinary function is the case whose scope starts with `this` at
its receiver annotation (`GenericSource.closureTy`): the receiver premise is
that binding, and every use of `this` is judged against it. -/
theorem closureTyB_iff {c : Ctx} (hw : WellFormed c.parameters) {env : List (String × Ty)}
    {pos : Span} {ps : List (String × Ty)} {declared : Ty} {body : Body} :
    (∃ t, closureTyB c env pos ps declared body = .ok t) ↔
      ∃ t, HasTy c (ps ++ env) body t ∧ Sub c.parameters t declared := by
  constructor
  · rintro ⟨t, h⟩
    unfold closureTyB at h
    split at h
    · cases h
    · next actual hb =>
      split at h
      · next hle => exact ⟨actual, HasTy_of_exprTyB body hb, Sub_of_leUnder hle⟩
      · cases h
  · rintro ⟨t, ht, hle⟩
    refine ⟨.arrow .top (ps.map Prod.snd) declared, ?_⟩
    unfold closureTyB
    rw [exprTyB_of_HasTy hw ht]
    simp [leUnder_of_Sub hw hle]

#print axioms closureTyB_iff

/-! ## Declaration bodies

A declaration body is immutable copies, each seeing the earlier, then a
return. At each statement the producer claims an environment; every claimed
binding type is above what the body established, and the claimed types are
what later statements see. Each initializer and the returned expression is
claimed too, above its established type; a copy's binding type is its
annotation, or the initializer's claim when it has none, and the return's
claim is below the declared result. `bodyClaimsB` decides it. -/

theorem distinct_iff_nodup : ∀ (l : List String), distinct l = true ↔ l.Nodup
  | [] => by simp [distinct]
  | x :: xs => by
      simp only [distinct, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.nodup_cons,
        distinct_iff_nodup xs]
      simp

/-- Each binding's claim at an entry, above what the body established, in
scope order; the claims are what the rest of the body sees. -/
inductive Entry (c : Ctx) (source : List (String × Ty)) :
    List (String × Ty) → List (String × Ty) → Prop
  | nil : Entry c source [] []
  | cons {name : String} {actual expected : Ty} {env H : List (String × Ty)}
      (hs : source.lookup name = some expected) (hle : Sub c.parameters actual expected)
      (h : Entry c source env H) :
      Entry c source ((name, actual) :: env) ((name, expected) :: H)

/-- The claimed environment at a statement: distinct names, exactly the
scope's names, each claim above its binding's established type. -/
def EntryOk (c : Ctx) (env : List (String × Ty)) (pos : Span) (H : List (String × Ty)) : Prop :=
  ∃ source, c.claims.entries.lookup pos.1 = some source ∧ (source.map Prod.fst).Nodup ∧
    source.length = env.length ∧ (∀ p ∈ source, p.1 ∈ env.map Prod.fst) ∧ Entry c source env H

/-- An expression's claim, above the type the body establishes for it. -/
def ExprClaim (c : Ctx) (env : List (String × Ty)) (e : Body) (claimed : Ty) : Prop :=
  c.claims.exprs.lookup e.span = some claimed ∧
    ∃ actual, HasTy c env e actual ∧ Sub c.parameters actual claimed

inductive Bindings (c : Ctx) (pos : Span) :
    List (String × Ty) → List BindingT → List (String × Ty) → Prop
  | nil {H : List (String × Ty)} : Bindings c pos H [] H
  | cons {H H' : List (String × Ty)} {b : BindingT} {rest : List BindingT} {claimed : Ty}
      (hc : ExprClaim c H b.init claimed) (hle : Sub c.parameters claimed (b.annot.getD claimed))
      (h : Bindings c pos (H ++ [(b.name, b.annot.getD claimed)]) rest H') :
      Bindings c pos H (b :: rest) H'

inductive Checked (c : Ctx) : List (String × Ty) → Ty → List StmtT → Prop
  /-- The end of the body returns `undefined`. -/
  | done {env : List (String × Ty)} {result : Ty}
      (hle : Sub c.parameters (.ground [3]) result) : Checked c env result []
  | ret {env H : List (String × Ty)} {result claimed : Ty} {pos : Span} {e : Body}
      (hentry : EntryOk c env pos H) (hexpr : ExprClaim c H e claimed)
      (hle : Sub c.parameters claimed result) : Checked c env result [.ret pos e]
  | constants {env H H' : List (String × Ty)} {result : Ty} {pos : Span}
      {bindings : List BindingT} {rest : List StmtT}
      (hentry : EntryOk c env pos H) (hbind : Bindings c pos H bindings H')
      (hrest : Checked c H' result rest) : Checked c env result (.constants pos bindings :: rest)
  /-- An expression statement: its claim, then the rest in the same scope. -/
  | effect {env H : List (String × Ty)} {result claimed : Ty} {pos : Span} {e : Body}
      {rest : List StmtT}
      (hentry : EntryOk c env pos H) (hexpr : ExprClaim c H e claimed)
      (hrest : Checked c H result rest) : Checked c env result (.effect pos e :: rest)

/-! ### Entries -/

theorem Entry_of_entryBindings {c : Ctx} {source ctx : List (String × Ty)} {pos : Span} :
    ∀ {env H : List (String × Ty)}, entryBindings c source ctx pos env = .ok H → Entry c source env H
  | [], H, h => by
      simp only [entryBindings] at h
      cases h
      exact .nil
  | (name, actual) :: env, H, h => by
      simp only [entryBindings] at h
      split at h
      · cases h
      · next expected hs =>
        split at h
        · cases h
        · next hle =>
          split at h
          · cases h
          · next H' hrec =>
            cases h
            exact .cons hs (Sub_of_leUnder (requireLeE_ok.mp hle)) (Entry_of_entryBindings hrec)

theorem entryBindings_of_Entry {c : Ctx} (hw : WellFormed c.parameters)
    {source ctx : List (String × Ty)} {pos : Span} {env H : List (String × Ty)}
    (h : Entry c source env H) : entryBindings c source ctx pos env = .ok H := by
  induction h with
  | nil => simp [entryBindings]
  | @cons name actual expected env H hs hle _ ih =>
    have hle' := requireLeE_of_le c ctx .entryClaim (.binding name pos) (leUnder_of_Sub hw hle)
    simp [entryBindings, hs, hle', ih]

theorem EntryOk_of_entryClaimsB {c : Ctx} {env : List (String × Ty)} {pos : Span}
    {H : List (String × Ty)} (h : entryClaimsB c env pos = .ok H) : EntryOk c env pos H := by
  simp only [entryClaimsB] at h
  split at h
  · cases h
  · next source hs =>
    split at h
    · cases h
    · next hnd =>
      split at h
      · cases h
      · next hcov =>
        refine ⟨source, hs, (distinct_iff_nodup _).mp (by simpa using hnd), ?_, ?_,
          Entry_of_entryBindings h⟩
        · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or] at hcov
          exact Decidable.of_not_not hcov.1
        · intro p hp
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, List.any_eq_true, not_exists,
            not_and, Bool.not_eq_true', Bool.not_eq_false] at hcov
          simpa using hcov.2 p hp

theorem entryClaimsB_of_EntryOk {c : Ctx} (hw : WellFormed c.parameters)
    {env : List (String × Ty)} {pos : Span} {H : List (String × Ty)}
    (h : EntryOk c env pos H) : entryClaimsB c env pos = .ok H := by
  obtain ⟨source, hs, hnd, hlen, hcov, he⟩ := h
  have hdistinct : distinct (source.map Prod.fst) = true := (distinct_iff_nodup _).mpr hnd
  simp [entryClaimsB, hs, hdistinct, hlen, entryBindings_of_Entry hw he]
  intro x y hxy
  simpa using hcov (x, y) hxy

/-! ### Expressions with claims, and bindings -/

theorem ExprClaim_of_expressionClaimB {c : Ctx} {env : List (String × Ty)} {e : Body}
    {claimed : Ty} (h : expressionClaimB c env e = .ok claimed) : ExprClaim c env e claimed := by
  simp only [expressionClaimB] at h
  split at h
  · cases h
  · next expected hs =>
    split at h
    · cases h
    · next actual hact =>
      split at h
      · cases h
      · next hle =>
        cases h
        exact ⟨hs, actual, HasTy_of_exprTyB e hact, Sub_of_leUnder (requireLeE_ok.mp hle)⟩

theorem expressionClaimB_of_ExprClaim {c : Ctx} (hw : WellFormed c.parameters)
    {env : List (String × Ty)} {e : Body} {claimed : Ty}
    (h : ExprClaim c env e claimed) : expressionClaimB c env e = .ok claimed := by
  obtain ⟨hs, actual, ht, hle⟩ := h
  have hle' := requireLeE_of_le c env .expressionClaim (.expression e.span) (leUnder_of_Sub hw hle)
  simp [expressionClaimB, hs, exprTyB_of_HasTy hw ht, hle']

theorem Bindings_of_bindingsB {c : Ctx} {pos : Span} :
    ∀ {bs : List BindingT} {H H' : List (String × Ty)}, bindingsB c pos H bs = .ok H' →
      Bindings c pos H bs H'
  | [], H, H', h => by
      simp only [bindingsB] at h
      cases h
      exact .nil
  | b :: rest, H, H', h => by
      simp only [bindingsB] at h
      split at h
      · cases h
      · next claimed hc =>
        split at h
        · cases h
        · next hle =>
          exact .cons (ExprClaim_of_expressionClaimB hc) (Sub_of_leUnder (requireLeE_ok.mp hle))
            (Bindings_of_bindingsB h)

theorem bindingsB_of_Bindings {c : Ctx} (hw : WellFormed c.parameters) {pos : Span}
    {bs : List BindingT} {H H' : List (String × Ty)} (h : Bindings c pos H bs H') :
    bindingsB c pos H bs = .ok H' := by
  induction h with
  | nil => simp [bindingsB]
  | @cons H H' b rest claimed hc hle _ ih =>
    have hle' := requireLeE_of_le c H .bindingAnnotation (.binding b.name pos) (leUnder_of_Sub hw hle)
    simp [bindingsB, expressionClaimB_of_ExprClaim hw hc, hle', ih]

/-! ### Bodies -/

theorem Checked_of_bodyClaimsB {c : Ctx} {result : Ty} {origin : Span} :
    ∀ {stmts : List StmtT} {env : List (String × Ty)}, bodyClaimsB c env result origin stmts = .ok () →
      Checked c env result stmts
  | [], env, h => by
      simp only [bodyClaimsB] at h
      exact .done (Sub_of_leUnder (requireLeE_ok.mp h))
  | [.ret pos e], env, h => by
      simp only [bodyClaimsB] at h
      split at h
      · cases h
      · next H hH =>
        split at h
        · cases h
        · next claimed hc =>
          exact .ret (EntryOk_of_entryClaimsB hH) (ExprClaim_of_expressionClaimB hc)
            (Sub_of_leUnder (requireLeE_ok.mp h))
  | .ret _ _ :: _ :: _, env, h => by simp only [bodyClaimsB] at h; cases h
  | .effect pos e :: rest, env, h => by
      simp only [bodyClaimsB] at h
      split at h
      · cases h
      · next H hH =>
        split at h
        · cases h
        · next claimed hc =>
          exact .effect (EntryOk_of_entryClaimsB hH) (ExprClaim_of_expressionClaimB hc)
            (Checked_of_bodyClaimsB h)
  | .constants pos bindings :: rest, env, h => by
      simp only [bodyClaimsB] at h
      split at h
      · cases h
      · next H hH =>
        split at h
        · cases h
        · next H' hb =>
          exact .constants (EntryOk_of_entryClaimsB hH) (Bindings_of_bindingsB hb)
            (Checked_of_bodyClaimsB h)

theorem bodyClaimsB_of_Checked {c : Ctx} (hw : WellFormed c.parameters) {result : Ty}
    {origin : Span} {stmts : List StmtT} {env : List (String × Ty)}
    (h : Checked c env result stmts) : bodyClaimsB c env result origin stmts = .ok () := by
  induction h with
  | @done env result hle =>
    simp [bodyClaimsB, requireLeE_of_le c env .returnContract (.returned origin) (leUnder_of_Sub hw hle)]
  | @ret env H result claimed pos e hentry hexpr hle =>
    have hle' := requireLeE_of_le c H .returnContract (.returned pos) (leUnder_of_Sub hw hle)
    simp [bodyClaimsB, entryClaimsB_of_EntryOk hw hentry, expressionClaimB_of_ExprClaim hw hexpr, hle']
  | constants hentry hbind _ ih =>
    simp [bodyClaimsB, entryClaimsB_of_EntryOk hw hentry, bindingsB_of_Bindings hw hbind, ih]
  | effect hentry hexpr _ ih =>
    simp [bodyClaimsB, entryClaimsB_of_EntryOk hw hentry, expressionClaimB_of_ExprClaim hw hexpr, ih]

/-- The pure checker decides the declaration-body judgment on well-formed
binders; `parametersOf_wellFormed` supplies well-formedness for every list
`GenericSource.check` builds. -/
theorem bodyClaimsB_iff_Checked {c : Ctx} (hw : WellFormed c.parameters) {result : Ty}
    {origin : Span} {stmts : List StmtT} {env : List (String × Ty)} :
    bodyClaimsB c env result origin stmts = .ok () ↔ Checked c env result stmts :=
  ⟨Checked_of_bodyClaimsB, bodyClaimsB_of_Checked hw⟩

#print axioms bodyClaimsB_iff_Checked

/-! ## Two certificate-generation gaps closed

`GenericSource.check` is lowering, then `bodyClaimsB`, then the signature
check, then certificate generation. The theorem above covers `bodyClaimsB`,
not all these stages. The last compiles the body to `GenericCertificate.Proof`.
Two bodies the judgment
accepts were refused there before this milestone: a returned call, because
declarations had a compiler of their own that knew only variables, and a
returned primitive literal, because the proof language had no literal. Both
are certified now. -/

private def paramT : Lean.Json :=
  Lean.Json.mkObj [("top", Lean.toJson false),
    ("atoms", Lean.toJson [Lean.Json.mkObj [("a", Lean.toJson "param"), ("name", Lean.toJson "T")]])]
private def thunkT : Lean.Json :=
  Lean.Json.mkObj [("top", Lean.toJson false),
    ("atoms", Lean.toJson [Lean.Json.mkObj [("a", Lean.toJson "function"),
      ("this", Lean.Json.mkObj [("top", Lean.toJson true), ("atoms", Lean.toJson ([] : List Lean.Json))]),
      ("params", Lean.toJson ([] : List Lean.Json)), ("result", paramT),
      ("construct", Lean.toJson "unknown"), ("array", Lean.toJson "unknown")]])]
private def T : Ty := .rigid "T"
private def tpT : Fragment.TypeParam := ⟨"T", none⟩
private def run (x : M α) : Except Failure α := x.run' SourceTypes.initial

-- `<T>(f: () => T): T { return f(); }`: a call the judgment accepts and the
-- proof language expresses, now certified.
private def applyFn : Fragment.Fn :=
  ⟨"apply", (0, 2), [⟨"f", thunkT, false⟩], paramT,
    [.ret (10, 18) (.call (12, 18) (.var (12, 13) "f") [] [] [])]⟩
private def applyClaims : Claims :=
  ⟨"apply", (0, 2), [("f", .arrow .top [] T)], T, [(10, [("f", .arrow .top [] T)])],
    [((12, 18), T), ((12, 13), .arrow .top [] T)]⟩
#guard (match run (check applyFn [tpT] applyClaims) with | .ok _ => true | .error _ => false)

-- `<T>(x: T): boolean { return true; }`: a literal the judgment accepts,
-- now certified through `Proof.lit` under the table's primitive rows.
private def literalFn : Fragment.Fn :=
  ⟨"always", (0, 2), [⟨"x", paramT, false⟩], booleanType, [.ret (10, 18) (.lit (17, 18) (.vbool true))]⟩
private def literalClaims : Claims :=
  ⟨"always", (0, 2), [("x", T)], .ground [1, 2], [(10, [("x", T)])], [((17, 18), .ground [1])]⟩
private def literalCtx : Ctx := ⟨[⟨"T", .quantified, none⟩], literalClaims, []⟩
#guard (match (translateStmts ["T"] [] (0, 2) literalFn.body).run' SourceTypes.initial with
  | .ok stmts => (match bodyClaimsB literalCtx [("x", T)] (.ground [1, 2]) (0, 2) stmts with
    | .ok () => true
    | .error _ => false)
  | .error _ => false)
#guard (match run (check literalFn [tpT] literalClaims) with | .ok _ => true | .error _ => false)

end Verification.Model.SourceJudgments
