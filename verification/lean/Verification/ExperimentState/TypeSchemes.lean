import Verification.ExperimentState.TypeParams

/-! Quantified callable contracts over the existing parametric graph semantics.

A scheme ranges over assignments of its own binders, retaining the outer
assignment elsewhere. Membership concerns ONE callable in ONE world, at all
admissible instantiations. This is stronger than independently obtaining a safe
allocation at each instantiation: those allocations could choose different
world contracts. The allocation rule below fixes the field contracts before
quantifying over call signatures.

These are semantic rules, not yet a source/evidence encoding or an inference
algorithm. Nested schemes still require a compositional type syntax. -/
namespace Verification.ExperimentState.TypeSchemes
open TypeParams PositiveNormalization PositiveGraphs PositiveRules Tower ProgramTyping

variable {ι : Type}

structure Scheme (ι : Type) where
  binders : List ι
  bounds : List (ι × List ι)
  signatures : List (List (List ι) × List ι)

/-- Outer rigid meanings cannot change when a nested callable is instantiated.
An executable scheme decoder must additionally check binder scope/well-formedness. -/
def Instance (G : NormalGraph ι) (P : ι → Bool) (outer : ι → Fam)
    (s : Scheme ι) (η : ι → Fam) : Prop :=
  ClosedAssign P η ∧ Satisfies G P η s.bounds ∧
    ∀ i, i ∉ s.binders → η i = outer i

def signatures (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam)
    (s : Scheme ι) : List (List Fam × Fam) :=
  s.signatures.map fun p => (p.1.map (meaningP G P η), meaningP G P η p.2)

/-- Callable shape is required even if the bounds have no satisfying assignment. -/
def schemeT (G : NormalGraph ι) (P : ι → Bool) (outer : ι → Fam)
    (s : Scheme ι) : Fam := fun n W v =>
  Callable v ∧ ∀ η, Instance G P outer s η → callsT (signatures G P η s) n W v

theorem scheme_adm (G : NormalGraph ι) (P : ι → Bool) (outer : ι → Fam)
    (s : Scheme ι) : Adm (schemeT G P outer s) := by
  constructor
  · intro n W v hv
    exact ⟨hv.1, fun η hη => (callsT_adm _).down n W v (hv.2 η hη)⟩
  · intro n W U hx v hv
    exact ⟨hv.1, fun η hη => (callsT_adm _).mono n W U hx v (hv.2 η hη)⟩

theorem scheme_valOnly (G : NormalGraph ι) (P : ι → Bool) (outer : ι → Fam)
    (s : Scheme ι) : ValOnly (schemeT G P outer s) :=
  fun _ _ _ hv => hv.1.val

/-- Schemes themselves satisfy the closed-value side condition used for type
arguments; higher-order use need not introduce a second semantic universe. -/
theorem scheme_closed (G : NormalGraph ι) (P : ι → Bool) (outer : ι → Fam)
    (s : Scheme ι) : Adm (schemeT G P outer s) ∧ ValOnly (schemeT G P outer s) ∧
      ∀ n W v, schemeT G P outer s n W v → Scoped 0 v :=
  ⟨scheme_adm G P outer s, scheme_valOnly G P outer s, fun _ _ _ hv => hv.1.scoped⟩

/-- Introduction must establish every interpretation for the SAME value. -/
theorem scheme_intro {G : NormalGraph ι} {P outer s n W v}
    (hc : Callable v)
    (h : ∀ η, Instance G P outer s η → callsT (signatures G P η s) n W v) :
    schemeT G P outer s n W v := ⟨hc, h⟩

/-- A call selects an assignment only after its bounds and outer scope hold. -/
theorem scheme_elim {G : NormalGraph ι} {P outer s η}
    (hη : Instance G P outer s η) :
    FamLe (schemeT G P outer s) (callsT (signatures G P η s)) :=
  fun _ _ _ hv => hv.2 η hη

theorem scheme_elim_safe {G : NormalGraph ι} {P outer s η n W h t}
    (hη : Instance G P outer s η)
    (ht : Safe (schemeT G P outer s) n W h t) :
    Safe (callsT (signatures G P η s)) n W h t :=
  Safe_mono n (fun j _ => scheme_elim hη j) W h t ht

/-- An instantiated signature is used only after effectful operands have been
checked. The existing call rule transfers both arguments and code through the
same future worlds, so scheme elimination adds no call-specific effect shortcut. -/
theorem scheme_call {G : NormalGraph ι} {P outer s η B}
    (hη : Instance G P outer s η) (xs : List (Fam × Tm))
    (hp : (xs.map Prod.fst, B) ∈ signatures G P η s)
    (hA : ∀ p ∈ xs, Adm p.1) (hAv : ∀ p ∈ xs, ValOnly p.1)
    {n W heap f} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe (schemeT G P outer s) n W heap f)
    (ha : ∀ p ∈ xs, FutureSafe p.1 n W p.2) :
    Safe B n W heap (.call f (xs.map Prod.snd)) := by
  apply call_safe xs hA hAv hw hh ?_ ha
  apply Safe_mono n _ W heap f (scheme_elim_safe hη hf)
  intro j hj U v hv
  exact callsT_select hv hp

/-- One allocation, fixed fields, universally checked immutable code. The same
world extension and storage contracts serve every subsequent instantiation. -/
theorem make_scheme_fields {G : NormalGraph ι} {P outer s}
    {As : List Fam} (hA : ∀ A ∈ As, Adm A)
    (arity n : Nat) (W : WorldT n) (h : Heap) (ns : List String) (vs : List Val) (b : Tm)
    (hnd : ns.Nodup) (hns : ns.length = vs.length) (hAs : As.length = vs.length)
    (hvals : ∀ v ∈ vs, isVal v = true) (hb : Scoped arity b)
    (hf : ∀ η, Instance G P outer s η → InvocationSpec arity (signatures G P η s) n W b)
    (hw : WorldAdm W) (hh : HeapOk n W h) (hv : ∀ p ∈ As.zip vs, p.1 n W p.2) :
    Safe (interT (bagT (ns.zip As)) (schemeT G P outer s)) n W h
      (.makeAt (.closure arity b) ns vs) := by
  apply make_fields_rule hA n W h (.closure arity b) ns vs hnd hns hAs hvals hw hh hv
  intro j hj U hx hrec
  refine ⟨⟨_, .closure arity b, rfl, rfl, hrec⟩, ⟨arity, b, _, rfl, hb⟩, ?_⟩
  intro η hη
  have hc := (callsT_code_iff (signatures G P η s) arity (slots h.length ns) b n W).mpr
    (hf η hη)
  exact (callsT_adm _).mono j _ U hx _
    ((callsT_adm _).down_le n j (Nat.le_of_lt hj) W _ hc)

/-- Body checking is universal in the new binders; the captured environment is
unchanged. In particular, the premise cannot retype a captured location per call. -/
theorem invocation_of_scheme_body {G : NormalGraph ι} {P outer s Γ ρ n W b arity}
    (he : ∀ η, Instance G P outer s η → EnvOkP G P η Γ ρ n W)
    (hlen : ∀ p ∈ s.signatures, p.1.length = arity)
    (hb : ∀ η, Instance G P outer s η → ∀ p ∈ s.signatures, ∀ j U heap env,
      EnvOkP G P η (p.1 ++ Γ) env j U → WorldAdm U → HeapOk j U heap →
      Safe (meaningP G P η p.2) j U heap (instantiate 0 env b)) :
    ∀ η, Instance G P outer s η →
      InvocationSpec arity (signatures G P η s) n W (instantiate arity ρ b) := by
  intro η hη
  exact invocation_of_bodyP hη.1 (he η hη) hlen (hb η hη)

#print axioms scheme_adm
#print axioms scheme_valOnly
#print axioms scheme_closed
#print axioms scheme_intro
#print axioms scheme_elim
#print axioms scheme_elim_safe
#print axioms scheme_call
#print axioms make_scheme_fields
#print axioms invocation_of_scheme_body
end Verification.ExperimentState.TypeSchemes
