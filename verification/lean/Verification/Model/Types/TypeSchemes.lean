import Verification.Model.Types.TypeParams

/-! Quantified callable contracts over the existing parametric graph semantics.

A scheme ranges over assignments of its own binders, retaining the outer
assignment elsewhere. Membership concerns ONE callable in ONE world, at all
admissible instantiations. This is stronger than independently obtaining a safe
allocation at each instantiation: those allocations could choose different
world contracts. The allocation rule below fixes the field contracts before
quantifying over call signatures.

These are semantic rules, not yet a source/evidence encoding or an inference
algorithm. Nested schemes still require a compositional type syntax. -/
namespace Verification.Model.TypeSchemes
open TypeParams PositiveNormalization PositiveGraphs PositiveRules Tower ProgramTyping

variable {ι : Type}

structure Scheme (ι : Type) where
  binders : List ι
  bounds : List (ι × List ι)
  /-- `(receiver, parameters, result)`. -/
  signatures : List (List ι × List (List ι) × List ι)
  /-- `(receiver, fixed parameters, element, result)`. -/
  variadic : List (List ι × List (List ι) × List ι × List ι) := []

/-- Outer rigid meanings cannot change when a nested callable is instantiated.
An executable scheme decoder must additionally check binder scope/well-formedness. -/
def Instance (G : NormalGraph ι) (P : ι → Bool) (outer : ι → Fam)
    (s : Scheme ι) (η : ι → Fam) : Prop :=
  ClosedAssign P η ∧ Satisfies G P η s.bounds ∧
    ∀ i, i ∉ s.binders → η i = outer i

def signatures (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam)
    (s : Scheme ι) : List (Fam × List Fam × Fam) :=
  s.signatures.map fun p => (meaningP G P η p.1, p.2.1.map (meaningP G P η), meaningP G P η p.2.2)

def restSignatures (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam)
    (s : Scheme ι) : List (Fam × List Fam × ArgFam × Fam) :=
  s.variadic.map fun p => (meaningP G P η p.1, p.2.1.map (meaningP G P η),
    packArgs (meaningP G P η p.2.2.1), meaningP G P η p.2.2.2)

/-- Fixed and rest clauses use the same behavioral promise on the same value. -/
def instanceT (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam) (s : Scheme ι) : Fam :=
  interT (callsT (signatures G P η s)) (restsT (restSignatures G P η s))

theorem instance_adm (G : NormalGraph ι) (P : ι → Bool) (η : ι → Fam) (s : Scheme ι) :
    Adm (instanceT G P η s) := interT_adm _ _ (callsT_adm _) (restsT_adm _)

/-- Callable shape is required even if the bounds have no satisfying assignment. -/
def schemeT (G : NormalGraph ι) (P : ι → Bool) (outer : ι → Fam)
    (s : Scheme ι) : Fam := fun n W v =>
  Invocable v ∧ ∀ η, Instance G P outer s η → instanceT G P η s n W v

theorem scheme_adm (G : NormalGraph ι) (P : ι → Bool) (outer : ι → Fam)
    (s : Scheme ι) : Adm (schemeT G P outer s) := by
  constructor
  · intro n W v hv
    exact ⟨hv.1, fun η hη => (instance_adm G P η s).down n W v (hv.2 η hη)⟩
  · intro n W U hx v hv
    exact ⟨hv.1, fun η hη => (instance_adm G P η s).mono n W U hx v (hv.2 η hη)⟩

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
    (hc : Invocable v)
    (h : ∀ η, Instance G P outer s η → instanceT G P η s n W v) :
    schemeT G P outer s n W v := ⟨hc, h⟩

/-- A call selects an assignment only after its bounds and outer scope hold. -/
theorem scheme_elim {G : NormalGraph ι} {P outer s η}
    (hη : Instance G P outer s η) :
    FamLe (schemeT G P outer s) (callsT (signatures G P η s)) :=
  fun _ _ _ hv => (hv.2 η hη).1

/-- Rest elimination selects the same admissible assignment as fixed elimination. -/
theorem scheme_rest_elim {G : NormalGraph ι} {P outer s η}
    (hη : Instance G P outer s η) :
    FamLe (schemeT G P outer s) (restsT (restSignatures G P η s)) :=
  fun _ _ _ hv => (hv.2 η hη).2

theorem scheme_elim_safe {G : NormalGraph ι} {P outer s η n W h t}
    (hη : Instance G P outer s η)
    (ht : Safe (schemeT G P outer s) n W h t) :
    Safe (callsT (signatures G P η s)) n W h t :=
  Safe_mono n (fun j _ => scheme_elim hη j) W h t ht

/-- An instantiated signature is used only after effectful operands have been
checked. The existing call rule transfers both arguments and code through the
same future worlds, so scheme elimination adds no call-specific effect shortcut. -/
theorem scheme_call {G : NormalGraph ι} {P outer s η Rc B}
    (hη : Instance G P outer s η) (xs : List (Fam × Tm))
    (hp : (Rc, xs.map Prod.fst, B) ∈ signatures G P η s)
    (hRc : Adm Rc) (hRcv : ValOnly Rc)
    (hA : ∀ p ∈ xs, Adm p.1) (hAv : ∀ p ∈ xs, ValOnly p.1)
    {n W heap f r} (hw : WorldAdm W) (hh : HeapOk n W heap)
    (hf : Safe (schemeT G P outer s) n W heap f)
    (hr : FutureSafe Rc n W r)
    (ha : ∀ p ∈ xs, FutureSafe p.1 n W p.2) :
    Safe B n W heap (.invoke f r (xs.map Prod.snd)) := by
  apply call_safe xs hRc hRcv hA hAv hw hh ?_ hr ha
  apply Safe_mono n _ W heap f (scheme_elim_safe hη hf)
  intro j hj U v hv
  exact callsT_select hv hp

/-- One allocation, fixed fields, universally checked immutable code. The same
world extension and storage contracts serve every subsequent instantiation. -/
theorem make_scheme_fields {G : NormalGraph ι} {P outer s}
    {As : List Fam} (hA : ∀ A ∈ As, Adm A)
    (arity n : Nat) (W : WorldT n) (h : Heap) (ns : List PropKey) (vs : List Val) (b : Tm)
    (hnd : ns.Nodup) (hns : ns.length = vs.length) (hAs : As.length = vs.length)
    (hvals : ∀ v ∈ vs, isVal v = true) (hb : Scoped (arity + 1) b)
    (hfixed : s.variadic = [])
    (hf : ∀ η, Instance G P outer s η → InvocationSpec arity (signatures G P η s) n W b)
    (hw : WorldAdm W) (hh : HeapOk n W h) (hv : ∀ p ∈ As.zip vs, p.1 n W p.2) :
    Safe (interT (bagT (ns.zip As)) (schemeT G P outer s)) n W h
      (.makeAt (.closure arity b) ns vs) := by
  apply make_fields_rule hA n W h (.closure arity b) ns vs hnd hns hAs hvals hw hh hv
  intro j hj U hx hrec
  refine ⟨⟨_, .closure arity b, rfl, rfl, hrec⟩,
    Callable.invocable ⟨arity, b, _, rfl, hb⟩, ?_⟩
  intro η hη
  have hc := callsT_of_invocationSpec (slots h.length ns) (hf η hη)
  refine ⟨(callsT_adm _).mono j _ U hx _
    ((callsT_adm _).down_le n j (Nat.le_of_lt hj) W _ hc), ?_⟩
  refine ⟨hc.1, ?_⟩
  simp [restSignatures, hfixed]

/-- Body checking is universal in the new binders; the captured environment is
unchanged. In particular, the premise cannot retype a captured location per call. -/
theorem invocation_of_scheme_body {G : NormalGraph ι} {P outer s Γ ρ n W b arity}
    (he : ∀ η, Instance G P outer s η → EnvOkP G P η Γ ρ n W)
    (hlen : ∀ p ∈ s.signatures, p.2.1.length = arity)
    (hb : ∀ η, Instance G P outer s η → ∀ p ∈ s.signatures, ∀ j U heap env,
      EnvOkP G P η (p.1 :: p.2.1 ++ Γ) env j U → WorldAdm U → HeapOk j U heap →
      Safe (meaningP G P η p.2.2) j U heap (instantiate 0 env b)) :
    ∀ η, Instance G P outer s η →
      InvocationSpec arity (signatures G P η s) n W (instantiate (arity + 1) ρ b) := by
  intro η hη
  exact invocation_of_bodyP hη.1 (he η hη) hlen (hb η hη)

/-! The executable source path starts with this scheme. The theorem states the
universal fact checked syntactically there: one allocated identity closure is
callable at every closed interpretation of its binder, in the same world. -/
def identityScheme : Scheme Nat :=
  { binders := [1], bounds := [], signatures := [TypeParams.idSig] }

theorem identity_scheme_safe (outer : Nat → Fam) (n : Nat) (W : WorldT n)
    (heap : Heap) (hw : WorldAdm W) (hh : HeapOk n W heap) :
    Safe (schemeT TypeParams.idG TypeParams.idP outer identityScheme) n W heap
      (.make (.closure 1 (.var 1)) .nul) := by
  have hbody : ∀ η, Instance TypeParams.idG TypeParams.idP outer identityScheme η →
      InvocationSpec 1 (signatures TypeParams.idG TypeParams.idP η identityScheme)
        n W (.var 1) := by
    intro η hη
    have henv : ∀ ζ, Instance TypeParams.idG TypeParams.idP outer identityScheme ζ →
        EnvOkP TypeParams.idG TypeParams.idP ζ [] (fun _ => .nul) n W := by
      intro ζ _
      exact ⟨fun _ => by simp [Scoped], fun i A hi => by cases hi⟩
    have hlen : ∀ p ∈ identityScheme.signatures, p.2.1.length = 1 := by
      intro p hp
      have : p = TypeParams.idSig := List.mem_singleton.mp hp
      subst this
      rfl
    have hb : ∀ ζ, Instance TypeParams.idG TypeParams.idP outer identityScheme ζ →
        ∀ p ∈ identityScheme.signatures, ∀ j U localHeap env,
          EnvOkP TypeParams.idG TypeParams.idP ζ (p.1 :: p.2.1 ++ []) env j U →
          WorldAdm U → HeapOk j U localHeap →
          Safe (meaningP TypeParams.idG TypeParams.idP ζ p.2.2) j U localHeap
            (instantiate 0 env (.var 1)) := by
      intro ζ hζ p hp j U localHeap env he hu hh
      have : p = TypeParams.idSig := List.mem_singleton.mp hp
      subst this
      exact TypeParams.var_safeP hζ.1 rfl he hu hh
    have hi := invocation_of_scheme_body (s := identityScheme) (Γ := [])
      (ρ := fun _ => .nul) (n := n) (W := W) (b := .var 1) (arity := 1)
      henv hlen hb η hη
    simpa [instantiate] using hi
  have both := make_scheme_fields (G := TypeParams.idG) (P := TypeParams.idP)
    (outer := outer) (s := identityScheme) (As := [nulT])
    (by
      intro A hA
      have : A = nulT := List.mem_singleton.mp hA
      subst A
      exact nulT_adm) 1 n W heap [valueField] [.nul] (.var 1)
    (by decide) rfl rfl (by simp [isVal]) (by simp [Scoped]) rfl hbody hw hh
    (by
      intro p hp
      have : p = (nulT, .nul) := List.mem_singleton.mp hp
      subst p
      rfl)
  exact Safe_mono n (fun _ _ _ _ h => h.2) W heap _ both

#print axioms scheme_adm
#print axioms scheme_valOnly
#print axioms scheme_closed
#print axioms scheme_intro
#print axioms scheme_elim
#print axioms scheme_rest_elim
#print axioms scheme_elim_safe
#print axioms scheme_call
#print axioms make_scheme_fields
#print axioms invocation_of_scheme_body
#print axioms identity_scheme_safe
end Verification.Model.TypeSchemes
