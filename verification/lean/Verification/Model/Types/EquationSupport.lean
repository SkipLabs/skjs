import Verification.Model.Types.EquationGraphs
import Verification.Model.Types.PositiveRules

/-! Free-parameter support for equation graphs. These graphs use the same
recursive semantics and support theorem as checked finite tables. -/
namespace Verification.Model.EquationGraphs
open PositiveGraphs PositiveNormalization CallEffects PositiveRules

mutual
private theorem Tree.free_closed (t : Tree) (valid : t.scoped sig 0 0 = true)
    (p : Tree) (hp : p ∈ t.free) : p.scoped sig 0 0 = true := by
  cases t with
  | app h args => exact Args.free_closed args (Bool.and_eq_true_iff.mp valid).2 p hp
  | bound h args i => simpa [Tree.free] using List.mem_singleton.mp hp ▸ valid
  | argument i => simp [Tree.free] at hp
  | «local» i => simp [Tree.free] at hp
private theorem Types.free_closed (ts : Types) (valid : ts.scoped sig 0 0 = true)
    (p : Tree) (hp : p ∈ ts.free) : p.scoped sig 0 0 = true := by
  cases ts with
  | nil => simp [Types.free] at hp
  | cons t ts =>
    rcases List.mem_append.mp hp with hp | hp
    · exact Tree.free_closed t (Bool.and_eq_true_iff.mp valid).1 p hp
    · exact Types.free_closed ts (Bool.and_eq_true_iff.mp valid).2 p hp
private theorem Args.free_closed (args : Args) (valid : args.scoped sig 0 0 = true)
    (p : Tree) (hp : p ∈ args.free) : p.scoped sig 0 0 = true := by
  cases args with
  | nil => simp [Args.free] at hp
  | cons ts args =>
    rcases List.mem_append.mp hp with hp | hp
    · exact Types.free_closed ts (Bool.and_eq_true_iff.mp valid).1 p hp
    · exact Args.free_closed args (Bool.and_eq_true_iff.mp valid).2 p hp
end

def Label.free (label : Label sig) : List (Label sig) :=
  label.1.free.attach.map fun p => ⟨p.1, Tree.free_closed label.1 label.2 p.1 p.2⟩

@[simp] theorem Label.mem_free {label p : Label sig} : p ∈ label.free ↔ p.1 ∈ label.1.free := by
  simp only [free, List.mem_map, List.mem_attach, true_and]
  constructor
  · rintro ⟨p', rfl⟩; exact p'.2
  · intro hp; exact ⟨⟨p.1, hp⟩, rfl⟩

@[simp] theorem Types.free_ofList (ts : List Tree) : (ofList ts).free = ts.flatMap Tree.free := by
  induction ts <;> simp_all [ofList, free]

@[simp] theorem Args.free_ofList (ts : List Types) : (ofList ts).free = ts.flatMap Types.free := by
  induction ts <;> simp_all [ofList, free]

@[simp] theorem Types.free_append (xs ys : Types) : (xs.append ys).free = xs.free ++ ys.free := by
  cases xs with
  | nil => rfl
  | cons t ts => simp [append, free, free_append ts ys, List.append_assoc]

/-- Support available inside a template: its captured parameters and, only in
signature positions, the locals that this application will quantify. -/
def Scope.supports (scope : Scope sig) (locals : Bool) (p : Tree) : Prop :=
  p ∈ scope.rawArgs.free ∨ locals = true ∧
    ∃ slot : Fin sig[scope.head].binders.length, p = (scope.bound slot).1

private theorem Scope.argument_support (scope : Scope sig) (i : Nat)
    (hi : i < scope.arguments.length) (p : Tree)
    (hp : p ∈ (Types.ofList (scope.arguments[i].map Subtype.val)).free) :
    p ∈ scope.rawArgs.free := by
  simp only [Scope.rawArgs, Args.free_ofList, List.flatMap_map]
  exact List.mem_flatMap.mpr ⟨scope.arguments[i], List.getElem_mem hi, hp⟩

mutual
/-- Instantiation introduces only the parameters explicitly in scope. -/
theorem Tree.instantiate_support (scope : Scope sig) (t : Tree)
    (valid : t.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (lexical : t.lexical locals = true) (p : Tree)
    (hp : p ∈ (Tree.instantiate scope t valid).1.free) : scope.supports locals p := by
  cases t with
  | app h args =>
    apply Args.instantiate_support scope args (Bool.and_eq_true_iff.mp valid).2 lexical p
    simpa [Tree.instantiate, Types.free, Tree.free, Scope.bound] using hp
  | bound h args i => simp [Tree.lexical] at lexical
  | argument i =>
    left
    exact scope.argument_support i _ p hp
  | «local» i =>
    right
    refine ⟨lexical, ⟨⟨i, of_decide_eq_true valid⟩, ?_⟩⟩
    simpa [Tree.instantiate, Types.free, Tree.free, Scope.bound] using hp
theorem Types.instantiate_support (scope : Scope sig) (ts : Types)
    (valid : ts.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (lexical : ts.lexical locals = true) (p : Tree)
    (hp : p ∈ (Types.instantiate scope ts valid).1.free) : scope.supports locals p := by
  cases ts with
  | nil => simp [Types.instantiate, Types.free] at hp
  | cons t ts =>
    simp only [Types.instantiate, Types.free_append, List.mem_append] at hp
    rcases hp with hp | hp
    · exact Tree.instantiate_support scope t (Bool.and_eq_true_iff.mp valid).1
        (Bool.and_eq_true_iff.mp lexical).1 p hp
    · exact Types.instantiate_support scope ts (Bool.and_eq_true_iff.mp valid).2
        (Bool.and_eq_true_iff.mp lexical).2 p hp
theorem Args.instantiate_support (scope : Scope sig) (args : Args)
    (valid : args.scoped sig sig[scope.head].parameters sig[scope.head].binders.length = true)
    (lexical : args.lexical locals = true) (p : Tree)
    (hp : p ∈ (Args.instantiate scope args valid).1.free) : scope.supports locals p := by
  cases args with
  | nil => simp [Args.instantiate, Args.free] at hp
  | cons ts args =>
    rcases List.mem_append.mp hp with hp | hp
    · exact Types.instantiate_support scope ts (Bool.and_eq_true_iff.mp valid).1
        (Bool.and_eq_true_iff.mp lexical).1 p hp
    · exact Args.instantiate_support scope args (Bool.and_eq_true_iff.mp valid).2
        (Bool.and_eq_true_iff.mp lexical).2 p hp
end

private theorem clause_operands_map (f : α → β) (c : Clause α) :
    (c.map f).operands = c.operands.map f := by
  cases c <;> simp [Clause.map, Clause.operands, Tuple.map, Tuple.operands,
    mapFields, OptionalField.map, MethodMembers.Sig.map, MethodMembers.Sig.operands,
    Arrow.map, Arrow.operands, RestArrow.map, RestArrow.mapWith, RestArrow.operands,
    MethodArrow.map, MethodArrow.operands, MethodRestArrow.map,
    MethodRestArrow.mapWith, MethodRestArrow.operands, Contract.map,
    List.map_flatMap, List.flatMap_map, Function.comp_def, Option.toList_map]

private theorem Types.member_free (ts : Types) (valid : ts.scoped sig 0 0 = true)
    (l p : Label sig) (hl : l ∈ ts.labels valid) (hp : p ∈ l.free) : p.1 ∈ ts.free := by
  rw [← Types.labels_val ts valid, Types.free_ofList, List.flatMap_map]
  exact List.mem_flatMap.mpr ⟨l, hl, Label.mem_free.mp hp⟩

private theorem Expression.support (scope : Scope sig) (e : Expression sig sig[scope.head])
    (lexical : e.1.lexical locals = true) {l p : Label sig}
    (hl : l ∈ e.instantiate scope) (hp : p ∈ l.free) : scope.supports locals p.1 :=
  Tree.instantiate_support scope e.1 e.2.1 lexical p.1
    (Types.member_free _ _ l p hl hp)

private theorem expressions_support (scope : Scope sig) (es : List (Expression sig sig[scope.head]))
    (lexical : ∀ e ∈ es, e.1.lexical locals = true) {l p : Label sig}
    (hl : l ∈ es.flatMap (Expression.instantiate scope)) (hp : p ∈ l.free) :
    scope.supports locals p.1 := by
  obtain ⟨e, he, hl⟩ := List.mem_flatMap.mp hl
  exact e.support scope (lexical e he) hl hp

theorem Reference.instantiate_local (scope : Scope sig) (r : Reference sig sig[scope.head])
    (slot : Fin sig[scope.head].binders.length) (hr : r.1.1 = .local slot.val) :
    r.instantiate scope = scope.bound slot := by
  rcases r with ⟨⟨t, hv⟩, hs⟩
  dsimp only at hr
  subst t
  rfl

/-- The checked source order of local references is exactly the canonical
binder order, not merely a set containing the same names. -/
theorem Scope.instantiate_binders (scope : Scope sig) (bs : List (Reference sig sig[scope.head]))
    (hbs : bs.map (fun b => b.1.1) = (List.range sig[scope.head].binders.length).map Tree.local) :
    bs.map (Reference.instantiate scope) = scope.binders := by
  have hlen : bs.length = sig[scope.head].binders.length := by
    simpa using congrArg List.length hbs
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hj
    have hib : i < bs.length := by simpa using hi
    have hin : i < sig[scope.head].binders.length := by simpa [hlen] using hib
    have hget : (bs[i]).1.1 = Tree.local i := by
      have he := congrArg (fun xs : List Tree => xs[i]?) hbs
      simp only [List.getElem?_map] at he
      rw [List.getElem?_eq_getElem hib, List.getElem?_range hin] at he
      exact Option.some.inj he
    simpa [Scope.binders, List.getElem_map, List.getElem_finRange] using
      (bs[i]).instantiate_local scope ⟨i, hin⟩ hget

private theorem clause_reads_support (scope : Scope sig) (cs : List (Clause (List (Expression sig sig[scope.head]))))
    {l p : Label sig}
    (hl : l ∈ (cs.map (Clause.map (fun es => es.flatMap (Expression.instantiate scope)))).flatMap
      (fun c => c.operands.flatten)) (hp : p ∈ l.free) : scope.supports true p.1 := by
  obtain ⟨c', hc', hl⟩ := List.mem_flatMap.mp hl
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
  rw [clause_operands_map] at hl
  obtain ⟨es', hes', hl⟩ := List.mem_flatten.mp hl
  obtain ⟨es, hes, rfl⟩ := List.mem_map.mp hes'
  exact expressions_support scope es (fun e _ => e.2.2) hl hp

private theorem Equations.no_meets (equations : Equations) (label : Label equations.signature) :
    equations.graph.meets label = none ∧ equations.graph.meetParams label = [] := by
  apply label.cases
  · intro scope
    have hv := (equations.body scope.head).2
    cases hb : (equations.body scope.head).1 <;>
      simp_all [Equations.graph, NormalGraph.ofRowMap, Equations.row, Template.instantiate,
        RowTemplate.wellBound, GraphRow.map]
  · intro scope slot
    simp [Equations.graph, NormalGraph.ofRowMap, Equations.row]

/-- Computed syntax support satisfies the local closure conditions used by
both finite-table and equation-graph semantics. -/
theorem Equations.free_support (equations : Equations) :
    FreeSupport equations.graph (fun _ => True) Label.free := by
  refine ⟨?_, ?_, ?_⟩
  · intro label _
    apply label.cases
    · intro scope
      have hv := (equations.body scope.head).2
      cases hb : (equations.body scope.head).1 with
      | param p name kind => simp [hb, RowTemplate.wellBound] at hv
      | meet p cs ps => simp [hb, RowTemplate.wellBound] at hv
      | clauses cs =>
        have hlocals : equations.signature[scope.head].binders = [] := by
          simpa [hb, RowTemplate.wellBound] using hv
        simp only [NormalGraph.params, equations.kind_application, Option.isSome_none,
          Bool.false_eq_true, false_implies, true_and]
        constructor
        · intro l hl
          intro p hp
          have hreads : l ∈ (cs.map (Clause.map (fun es => es.flatMap (Expression.instantiate scope)))).flatMap
              (fun c => c.operands.flatten) := by
            simpa [reads, Equations.graph, NormalGraph.ofRowMap, Equations.row, Template.instantiate,
              hb, GraphRow.map, NormalGraph.clauses, NormalGraph.plain, NormalGraph.params,
              GraphRow.union, meetClauses] using hl
          rcases clause_reads_support scope cs hreads hp with h | ⟨_, slot, _⟩
          · left; simpa [Scope.label, Tree.free] using h
          · have hn := slot.isLt
            have hlen := congrArg List.length hlocals
            simp only [List.length_nil] at hlen
            omega
        · simp [boundReads, Equations.graph, NormalGraph.ofRowMap, Equations.row,
            Template.instantiate, hb, GraphRow.map]
      | scheme bs sigs bounds rests =>
        simp only [hb, RowTemplate.wellBound, Bool.and_eq_true_iff, decide_eq_true_eq] at hv
        simp only [NormalGraph.params, equations.kind_application, Option.isSome_none,
          Bool.false_eq_true, false_implies, true_and]
        constructor
        · intro l hl
          intro p hp
          have hreads : l ∈
              ((sigs.map (Arrow.map (fun es => es.flatMap (Expression.instantiate scope)))).flatMap
                (fun a => a.operands.flatten) ++
              (bounds.map (fun b => (b.1.instantiate scope, b.2.flatMap (Expression.instantiate scope)))).flatMap (·.2)) ++
              (rests.map (RestArrow.map (fun es => es.flatMap (Expression.instantiate scope)))).flatMap
                (fun a => a.operands.flatten) := by
            simpa only [reads, Equations.graph, NormalGraph.ofRowMap, Equations.row,
              Scope.view_label, Template.instantiate, hb, GraphRow.map] using hl
          have hs : scope.supports true p.1 := by
            rcases List.mem_append.mp hreads with h | h
            · rcases List.mem_append.mp h with h | h
              · apply clause_reads_support scope [.arrs sigs rests] (hp := hp)
                simpa only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
                  Clause.map, Clause.operands, List.flatten_append, List.append_nil, List.flatten_eq_flatMap, List.flatMap_append, List.flatMap_assoc] using
                  List.mem_append_left _ h
              · obtain ⟨b', hb', h⟩ := List.mem_flatMap.mp h
                obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb'
                exact expressions_support scope b.2 (fun e _ => e.2.2) h hp
            · apply clause_reads_support scope [.arrs sigs rests] (hp := hp)
              simpa only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
                Clause.map, Clause.operands, List.flatten_append, List.append_nil, List.flatten_eq_flatMap, List.flatMap_append, List.flatMap_assoc] using
                List.mem_append_right _ h
          rcases hs with h | ⟨_, slot, he⟩
          · left; simpa [Scope.label, Tree.free] using h
          · right
            simp only [Equations.graph, NormalGraph.ofRowMap, Equations.row, Scope.view_label,
              Template.instantiate, hb, GraphRow.map]
            refine ⟨_, rfl, ?_⟩
            have hp' : p = scope.bound slot := Subtype.ext he
            rw [hp']
            rw [scope.instantiate_binders bs hv.1]
            exact Scope.mem_binders.mpr ⟨slot, rfl⟩
        · intro l hl p hp
          have hbounds : l ∈ (bounds.map (fun b =>
              (b.1.instantiate scope, b.2.flatMap (Expression.instantiate scope)))).flatMap (·.2) := by
            simpa only [boundReads, Equations.graph, NormalGraph.ofRowMap, Equations.row,
              Scope.view_label, Template.instantiate, hb, GraphRow.map] using hl
          obtain ⟨b', hb', hl⟩ := List.mem_flatMap.mp hbounds
          obtain ⟨b, hbin, rfl⟩ := List.mem_map.mp hb'
          have hx := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hv.2 b hbin)).2
          have hs := expressions_support scope b.2 (List.all_eq_true.mp hx) hl hp
          rcases hs with h | ⟨h, _⟩
          · simpa [Scope.label, Tree.free] using h
          · cases h
    · intro scope slot
      simp only [Equations.graph, NormalGraph.ofRowMap, Equations.row, Scope.view_bound,
        NormalGraph.params, reads, boundReads, meetClauses, NormalGraph.clauses, NormalGraph.plain]
      simp [Scope.bound, Tree.free]
  · intro label _ p cs hm
    rw [(equations.no_meets label).1] at hm
    cases hm
  · intro label _ p hp
    rw [(equations.no_meets label).2] at hp
    cases hp

/-- An equation type depends only on the free parameters carried by its
application arguments. This covers both values and argument packs. -/
theorem Equations.agree_free (equations : Equations) (η θ : MixedAssignment (Label equations.signature))
    (S : List (Label equations.signature))
    (h : ∀ l ∈ S, ∀ p ∈ l.free, η.1 p = θ.1 p) :
    mixedMeaning equations.graph η S = mixedMeaning equations.graph θ S := by
  have hs := equations.free_support
  exact (mixed_respectsSupport hs).bound _
    (agree_supportWith hs (mixedParameters equations.graph) (mixed_respectsSupport hs))
    η θ S (fun _ _ => True.intro) (fun l hl p hp => congrArg _ (h l hl p hp))

#print axioms Equations.free_support
#print axioms Equations.agree_free

end Verification.Model.EquationGraphs
