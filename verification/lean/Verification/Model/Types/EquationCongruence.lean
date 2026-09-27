import Verification.Model.Types.EquationSupport

/-! Semantic congruence for parameterized equations. Local binders are owned by
an application, but their names must not affect what a quantified type means. -/
namespace Verification.Model.EquationGraphs
open PositiveGraphs PositiveRules PositiveNormalization CallEffects

private theorem assign_index (η : ParameterAssignment k ι) (bs : List ι)
    (As : List (ParameterFamily k)) (unique : bs.Nodup) (lengths : As.length = bs.length)
    (i : Nat) (hi : i < bs.length) :
    (assign η bs As).1 bs[i] = (As[i]'(by omega)).1 := by
  induction bs generalizing As i with
  | nil => simp at hi
  | cons b bs ih =>
    cases As with
    | nil => simp at lengths
    | cons A As =>
      cases i with
      | zero => exact assign_cons_head η b bs A As
      | succ i =>
        have hb : bs[i]'(by simpa using hi) ≠ b := by
          intro he
          exact (List.nodup_cons.mp unique).1 (he ▸ List.getElem_mem (by simpa using hi))
        rw [List.getElem_cons_succ, assign_cons_ne η bs A As hb]
        exact ih As (List.nodup_cons.mp unique).2 (by simpa using lengths) i (by simpa using hi)

theorem Scope.assign_bound (scope : Scope sig) (η : MixedAssignment (Label sig))
    (As : List MixedFamily) (hlen : As.length = sig[scope.head].binders.length)
    (slot : Fin sig[scope.head].binders.length) :
    (assign η scope.binders As).1 (scope.bound slot) = (As[slot.val]'(by omega)).1 := by
  have h := assign_index η scope.binders As scope.binders_nodup (by simpa using hlen)
    slot.val (by simp)
  simpa [Scope.binders, List.getElem_map, List.getElem_finRange] using h

/-- No local of an application is free in any of its captured arguments. -/
theorem Scope.argument_free (scope : Scope sig) (A : List (Label sig)) (hA : A ∈ scope.arguments)
    (l : Label sig) (hl : l ∈ A) (p : Label sig) (hp : p ∈ l.free) : p ∉ scope.binders := by
  intro hin
  obtain ⟨slot, rfl⟩ := Scope.mem_binders.mp hin
  apply scope.bound_fresh slot
  simp only [Scope.rawArgs, Args.free_ofList, Types.free_ofList, List.flatMap_map]
  exact List.mem_flatMap.mpr ⟨A, hA, List.mem_flatMap.mpr ⟨l, hl, Label.mem_free.mp hp⟩⟩

/-- Quantifying a scope's locals leaves its captured type arguments unchanged,
even if those arguments refer to other applications' parameters. -/
theorem Equations.arguments_assign (equations : Equations) (scope : Scope equations.signature)
    (η : MixedAssignment (Label equations.signature)) (As : List MixedFamily)
    (A : List (Label equations.signature)) (hA : A ∈ scope.arguments) :
    mixedMeaning equations.graph (assign η scope.binders As) A = mixedMeaning equations.graph η A := by
  apply equations.agree_free
  intro l hl p hp
  exact assign_nmem η scope.binders As (scope.argument_free A hA l hl p hp)

/-- Local parameters at the same slot receive the same selected semantic
family in two applications of one equation head. -/
theorem Equations.locals_assign (equations : Equations)
    (a b : Scope equations.signature) (head : a.head = b.head)
    (η θ : MixedAssignment (Label equations.signature)) (As : List MixedFamily)
    (hlen : As.length = equations.signature[a.head].binders.length)
    (i : Nat) (hi : i < equations.signature[a.head].binders.length) :
    mixedMeaning equations.graph (assign η a.binders As) [a.bound ⟨i, hi⟩] =
    mixedMeaning equations.graph (assign θ b.binders As) [b.bound ⟨i, by simpa [← head] using hi⟩] := by
  rw [mixedMeaning_parameter _ _ _ _ (equations.kind_bound a ⟨i, hi⟩),
    mixedMeaning_parameter _ _ _ _ (equations.kind_bound b ⟨i, by simpa [← head] using hi⟩)]
  rw [a.assign_bound η As hlen, b.assign_bound θ As (by simpa [← head] using hlen)]
  simp [head]

/-- Positionwise agreement of a declaration's mixed type arguments. -/
def Equations.ArgumentsAgree (equations : Equations)
    (η θ : MixedAssignment (Label equations.signature))
    (As Bs : List (List (Label equations.signature))) (n : Nat) : Prop :=
  As.length = Bs.length ∧ ∀ i (ha : i < As.length) (hb : i < Bs.length),
    Agree (mixedMeaning equations.graph η As[i]) (mixedMeaning equations.graph θ Bs[i]) n

/-- The induction hypothesis needed to lift argument agreement through finite
expressions. This is a proof premise, never an accepted certificate assumption. -/
def Equations.ApplicationsAgree (equations : Equations) (n : Nat) : Prop :=
  ∀ (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature)),
    a.head = b.head → equations.ArgumentsAgree η θ a.arguments b.arguments n →
    Agree (mixedMeaning equations.graph η [a.label]) (mixedMeaning equations.graph θ [b.label]) n

private theorem mixed_append_agree (G : NormalGraph ι) (η θ : MixedAssignment ι)
    (As Bs Cs Ds : List ι)
    (h1 : Agree (mixedMeaning G η As) (mixedMeaning G θ Bs) n)
    (h2 : Agree (mixedMeaning G η Cs) (mixedMeaning G θ Ds) n) :
    Agree (mixedMeaning G η (As ++ Cs)) (mixedMeaning G θ (Bs ++ Ds)) n := by
  intro m hm W x
  have happ (ρ : MixedAssignment ι) (A B : List ι) : mixedMeaning G ρ (A ++ B) m W x ↔
      mixedMeaning G ρ A m W x ∨ mixedMeaning G ρ B m W x := by
    rw [mixedMeaning_union G ρ (A ++ B), mixedMeaning_union G ρ A, mixedMeaning_union G ρ B]
    simp only [List.mem_append, or_and_right, exists_or]
  rw [happ, happ]
  exact or_congr (h1 m hm W x) (h2 m hm W x)

mutual
/-- Finite template traversal preserves semantic agreement, assuming it for
applications at the same step index. Captures and locals are separate premises. -/
theorem Tree.instantiate_agree (equations : Equations) (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (locals : allowLocals = true → ∀ i (ha : i < equations.signature[a.head].binders.length)
      (hb : i < equations.signature[b.head].binders.length),
      Agree (mixedMeaning equations.graph η [a.bound ⟨i, ha⟩])
        (mixedMeaning equations.graph θ [b.bound ⟨i, hb⟩]) n)
    (t : Tree) (va : t.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : t.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : t.lexical allowLocals = true) :
    Agree (mixedMeaning equations.graph η ((Tree.instantiate a t va).1.labels (Tree.instantiate a t va).2))
      (mixedMeaning equations.graph θ ((Tree.instantiate b t vb).1.labels (Tree.instantiate b t vb).2)) n := by
  cases t with
  | bound h ts slot => simp [Tree.lexical] at lex
  | argument i =>
    simpa only [Tree.instantiate, Types.labels_ofList] using args.2 i
      (by have := of_decide_eq_true va; simpa only [a.arity] using this)
      (by have := of_decide_eq_true vb; simpa only [b.arity] using this)
  | «local» i => exact locals lex i (of_decide_eq_true va) (of_decide_eq_true vb)
  | app h ts =>
    let oa := Args.instantiate a ts (Bool.and_eq_true_iff.mp va).2
    let ob := Args.instantiate b ts (Bool.and_eq_true_iff.mp vb).2
    have ca : (Tree.app h oa.1).scoped equations.signature 0 0 = true := by
      have hv := (Tree.instantiate a (.app h ts) va).2
      simpa only [Tree.instantiate, Types.scoped, Bool.and_true] using hv
    have cb : (Tree.app h ob.1).scoped equations.signature 0 0 = true := by
      have hv := (Tree.instantiate b (.app h ts) vb).2
      simpa only [Tree.instantiate, Types.scoped, Bool.and_true] using hv
    let sa := Scope.ofRaw h oa.1 (Bool.and_eq_true_iff.mp ca).1 oa.2.1
    let sb := Scope.ofRaw h ob.1 (Bool.and_eq_true_iff.mp cb).1 ob.2.1
    have hr := Args.instantiate_agree equations apps a b η θ args locals ts
      (Bool.and_eq_true_iff.mp va).2 (Bool.and_eq_true_iff.mp vb).2 lex
    have hs := apps sa sb η θ rfl hr
    dsimp only [sa, sb] at hs
    simp only [Scope.label, Scope.ofRaw_args] at hs
    simpa only [Scope.ofRaw, Tree.instantiate, Types.labels, oa, ob] using hs

theorem Types.instantiate_agree (equations : Equations) (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (locals : allowLocals = true → ∀ i (ha : i < equations.signature[a.head].binders.length)
      (hb : i < equations.signature[b.head].binders.length),
      Agree (mixedMeaning equations.graph η [a.bound ⟨i, ha⟩])
        (mixedMeaning equations.graph θ [b.bound ⟨i, hb⟩]) n)
    (ts : Types) (va : ts.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : ts.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : ts.lexical allowLocals = true) :
    Agree (mixedMeaning equations.graph η ((Types.instantiate a ts va).1.labels (Types.instantiate a ts va).2))
      (mixedMeaning equations.graph θ ((Types.instantiate b ts vb).1.labels (Types.instantiate b ts vb).2)) n := by
  cases ts with
  | nil =>
    intro m hm W x
    cases x <;> simp [Types.instantiate, Types.labels, mixedMeaning, mixedParameters, graphArguments, Tower.setSem]
  | cons t ts =>
    simp only [Types.instantiate]
    rw [Types.labels_append _ _ (Tree.instantiate a t (Bool.and_eq_true_iff.mp va).1).2
      (Types.instantiate a ts (Bool.and_eq_true_iff.mp va).2).2,
      Types.labels_append _ _ (Tree.instantiate b t (Bool.and_eq_true_iff.mp vb).1).2
      (Types.instantiate b ts (Bool.and_eq_true_iff.mp vb).2).2]
    exact mixed_append_agree _ _ _ _ _ _ _
      (Tree.instantiate_agree equations apps a b η θ args locals t
        (Bool.and_eq_true_iff.mp va).1 (Bool.and_eq_true_iff.mp vb).1 (Bool.and_eq_true_iff.mp lex).1)
      (Types.instantiate_agree equations apps a b η θ args locals ts
        (Bool.and_eq_true_iff.mp va).2 (Bool.and_eq_true_iff.mp vb).2 (Bool.and_eq_true_iff.mp lex).2)

theorem Args.instantiate_agree (equations : Equations) (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (locals : allowLocals = true → ∀ i (ha : i < equations.signature[a.head].binders.length)
      (hb : i < equations.signature[b.head].binders.length),
      Agree (mixedMeaning equations.graph η [a.bound ⟨i, ha⟩])
        (mixedMeaning equations.graph θ [b.bound ⟨i, hb⟩]) n)
    (ts : Args) (va : ts.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : ts.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : ts.lexical allowLocals = true) :
    equations.ArgumentsAgree η θ
      ((Args.instantiate a ts va).1.labels (Args.instantiate a ts va).2.1)
      ((Args.instantiate b ts vb).1.labels (Args.instantiate b ts vb).2.1) n := by
  cases ts with
  | nil => exact ⟨rfl, fun i hi _ => False.elim (Nat.not_lt_zero _ hi)⟩
  | cons t ts =>
    have hh := Types.instantiate_agree equations apps a b η θ args locals t
      (Bool.and_eq_true_iff.mp va).1 (Bool.and_eq_true_iff.mp vb).1 (Bool.and_eq_true_iff.mp lex).1
    have ht := Args.instantiate_agree equations apps a b η θ args locals ts
      (Bool.and_eq_true_iff.mp va).2 (Bool.and_eq_true_iff.mp vb).2 (Bool.and_eq_true_iff.mp lex).2
    refine ⟨by simpa only [Args.instantiate, Args.labels, List.length_cons] using congrArg Nat.succ ht.1, ?_⟩
    intro i hi hj
    cases i with
    | zero => exact hh
    | succ i =>
      exact ht.2 i
        (by simpa only [Args.instantiate, Args.labels, List.length_cons, Nat.succ_lt_succ_iff] using hi)
        (by simpa only [Args.instantiate, Args.labels, List.length_cons, Nat.succ_lt_succ_iff] using hj)
end

theorem Equations.ArgumentsAgree.mono {equations : Equations} {η θ As Bs n m}
    (h : equations.ArgumentsAgree η θ As Bs n) (hm : m ≤ n) :
    equations.ArgumentsAgree η θ As Bs m :=
  ⟨h.1, fun i hi hj => PositiveGraphs.Agree.mono (h.2 i hi hj) hm⟩

/-- Entering binders on both sides preserves agreement of captured arguments. -/
theorem Equations.ArgumentsAgree.assign {equations : Equations}
    {η θ : MixedAssignment (Label equations.signature)} {a b : Scope equations.signature}
    (h : equations.ArgumentsAgree η θ a.arguments b.arguments n) (As Bs : List MixedFamily) :
    equations.ArgumentsAgree (PositiveGraphs.assign η a.binders As)
      (PositiveGraphs.assign θ b.binders Bs) a.arguments b.arguments n := by
  refine ⟨h.1, ?_⟩
  intro i hi hj
  rw [equations.arguments_assign a η As _ (List.getElem_mem hi),
    equations.arguments_assign b θ Bs _ (List.getElem_mem hj)]
  exact h.2 i hi hj

/-- Signature expressions retain agreement after their applications quantify
corresponding locals. The application-congruence premise is the recursive
induction hypothesis, not an external semantic assumption. -/
theorem Equations.signature_expression_agree (equations : Equations)
    (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (head : a.head = b.head)
    (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (As : List MixedFamily) (hlen : As.length = equations.signature[a.head].binders.length)
    (t : Tree) (va : t.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : t.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : t.lexical true = true) :
    Agree (mixedMeaning equations.graph (assign η a.binders As)
      ((Tree.instantiate a t va).1.labels (Tree.instantiate a t va).2))
      (mixedMeaning equations.graph (assign θ b.binders As)
        ((Tree.instantiate b t vb).1.labels (Tree.instantiate b t vb).2)) n := by
  apply Tree.instantiate_agree equations apps a b _ _ (args.assign As As) _ t va vb lex
  intro _ i hi hj
  have he := equations.locals_assign a b head η θ As hlen i hi
  rw [he]
  exact fun _ _ _ _ => Iff.rfl

/-- Bound expressions are compared in their outer environments. They cannot
read a locally quantified parameter, so no local agreement premise is needed. -/
theorem Equations.bound_expression_agree (equations : Equations)
    (apps : equations.ApplicationsAgree n)
    (a b : Scope equations.signature) (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ a.arguments b.arguments n)
    (t : Tree) (va : t.scoped equations.signature equations.signature[a.head].parameters
      equations.signature[a.head].binders.length = true)
    (vb : t.scoped equations.signature equations.signature[b.head].parameters
      equations.signature[b.head].binders.length = true)
    (lex : t.lexical false = true) :
    Agree (mixedMeaning equations.graph η ((Tree.instantiate a t va).1.labels (Tree.instantiate a t va).2))
      (mixedMeaning equations.graph θ ((Tree.instantiate b t vb).1.labels (Tree.instantiate b t vb).2)) n :=
  Tree.instantiate_agree equations apps a b η θ args (fun h => Bool.noConfusion h) t va vb lex

private theorem mixed_flatMap_agree (G : NormalGraph ι) (η θ : MixedAssignment ι)
    (f g : α → List ι) (es : List α)
    (h : ∀ e ∈ es, Agree (mixedMeaning G η (f e)) (mixedMeaning G θ (g e)) n) :
    Agree (mixedMeaning G η (es.flatMap f)) (mixedMeaning G θ (es.flatMap g)) n := by
  induction es with
  | nil => intro m hm U x; cases x <;> simp [mixedMeaning, mixedParameters, graphArguments, Tower.setSem]
  | cons e es ih =>
    exact mixed_append_agree _ _ _ _ _ _ _ (h e List.mem_cons_self)
      (ih fun e he => h e (List.mem_cons_of_mem _ he))

private theorem mapped_sem_agree (G : NormalGraph ι) (η θ : MixedAssignment ι)
    (f g : α → List ι) (h : ∀ e, Agree (mixedMeaning G η (f e)) (mixedMeaning G θ (g e)) n)
    (c : Clause α) (W : WorldT n) (v : Val) :
    semWithArgs (mixedValues G η) (mixedArgs G η) (c.map f) n W v ↔
      semWithArgs (mixedValues G θ) (mixedArgs G θ) (c.map g) n W v := by
  rw [semWithArgs_map, semWithArgs_map]
  exact semWithArgs_congr _ _ _ _ n (fun e m hm U u => h e m hm U (.inl u))
    (fun e m hm U us => h e m hm U (.inr us)) c W v

/-- A clause reads its operand families below the current level. Mapping its
operands changes neither its shape nor the fixed array-realm requirement. -/
private theorem mapped_clause_agree (G : NormalGraph ι) (η θ : MixedAssignment ι)
    (f g : α → List ι) (h : ∀ e, Agree (mixedMeaning G η (f e)) (mixedMeaning G θ (g e)) n)
    (c : Clause α) (W : WorldT n) (v : Val) :
    mixedSem G η (c.map f) n W v ↔ mixedSem G θ (c.map g) n W v := by
  apply and_congr
  · exact mapped_sem_agree G η θ f g h c W v
  · unfold realmInvariant
    simp only [Clause.record_map]

/-- The value half of the application-congruence induction for a clause head.
All recursive operand reasoning is below the current step index. -/
theorem Equations.clauses_step (equations : Equations) (apps : equations.ApplicationsAgree n)
    (head : Fin equations.signature.length)
    (A B : List (List (Label equations.signature)))
    (ha : A.length = equations.signature[head].parameters)
    (hb : B.length = equations.signature[head].parameters)
    (η θ : MixedAssignment (Label equations.signature))
    (args : equations.ArgumentsAgree η θ A B n)
    (cs : List (Clause (List (Expression equations.signature equations.signature[head]))))
    (body : (equations.body head).1 = .clauses cs) (W : WorldT n) (v : Val) :
    qDenoteWithArgs equations.graph (mixedParameters equations.graph)
      (η, (Scope.mk head A ha).label) n W v ↔
    qDenoteWithArgs equations.graph (mixedParameters equations.graph)
      (θ, (Scope.mk head B hb).label) n W v := by
  let a : Scope equations.signature := ⟨head, A, ha⟩
  let b : Scope equations.signature := ⟨head, B, hb⟩
  have empty : equations.signature[head].binders = [] := by
    have h := (equations.body head).2
    simpa [body, RowTemplate.wellBound] using h
  have exprs : ∀ es : List (Expression equations.signature equations.signature[head]),
      Agree (mixedMeaning equations.graph η (es.flatMap (Expression.instantiate a)))
        (mixedMeaning equations.graph θ (es.flatMap (Expression.instantiate b))) n := by
    intro es
    apply mixed_flatMap_agree
    intro e _
    apply Tree.instantiate_agree equations apps a b η θ args _ e.1 e.2.1 e.2.1 e.2.2
    intro _ i hi hj
    have hlen := congrArg List.length empty
    have hi' : i < equations.signature[head].binders.length := hi
    simp only [List.length_nil] at hlen
    omega
  have plain (C) (hc : C.length = equations.signature[head].parameters) :
      equations.graph.plain (Scope.mk head C hc).label = true := by
    simp [NormalGraph.plain, NormalGraph.params, Equations.graph, NormalGraph.ofRowMap,
      Equations.row, Template.instantiate, body, GraphRow.map]
  have row (C) (hc : C.length = equations.signature[head].parameters) :
      equations.graph (Scope.mk head C hc).label =
        cs.map (Clause.map (fun es => es.flatMap (Expression.instantiate ⟨head, C, hc⟩))) := by
    simp [NormalGraph.clauses, NormalGraph.plain, NormalGraph.params, Equations.graph,
      NormalGraph.ofRowMap, Equations.row, Template.instantiate, body, GraphRow.map, GraphRow.union]
  rw [mixed_unfold_plain η (plain A ha), mixed_unfold_plain θ (plain B hb), row A ha, row B hb]
  constructor
  · rintro ⟨c', hc', hv⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, (mapped_clause_agree _ η θ _ _ exprs c W v).mp hv⟩
  · rintro ⟨c', hc', hv⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, (mapped_clause_agree _ η θ _ _ exprs c W v).mpr hv⟩

#print axioms Equations.arguments_assign
#print axioms Equations.locals_assign
#print axioms Equations.signature_expression_agree
#print axioms Equations.bound_expression_agree
#print axioms Equations.clauses_step

end Verification.Model.EquationGraphs
