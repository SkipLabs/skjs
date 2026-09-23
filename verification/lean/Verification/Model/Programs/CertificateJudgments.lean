import Verification.Model.Types.GenericCertificate
import Verification.Model.Types.RigidJudgments

/-! # Declarative typing of direct certificates

`Typed ps Γ t A` is the typing judgment of the rigid fragment over calculus
terms: variables and cell reads from the slot environment, subsumption along
`RigidJudgments.Sub`, immutable `let`, closures, and calls whose arguments
meet the callable's parameters. It is stated by rules, without proof terms.
`GenericCertificate.Proof.check` is the executable certificate checker. This
module proves both directions between them: every accepted certificate is a
derivation, and on well-formed parameters every derivation has an accepted
certificate. Semantic safety of accepted certificates is
`Proof.check_safe`; through the reverse direction it is safety of every
derivation, and the judgment adds no acceptance path beside it. -/
namespace Verification.Model.CertificateJudgments
open DirectObligation GenericCertificate RigidJudgments

inductive Typed (ps : List Parameter) : List Slot → Tm → Ty → Prop
  | var {Γ : List Slot} {i : Nat} {A : Ty} (h : Γ[i]? = some (.value A)) :
      Typed ps Γ (.var i) A
  | read {Γ : List Slot} {i : Nat} {A : Ty} (h : Γ[i]? = some (.cell A)) :
      Typed ps Γ (.read (.var i)) A
  | nul {Γ : List Slot} : Typed ps Γ .nul (.ground [0])
  | undef {Γ : List Slot} : Typed ps Γ .undef (.ground [3])
  | tru {Γ : List Slot} : Typed ps Γ .tru (.ground [1])
  | fls {Γ : List Slot} : Typed ps Γ .fls (.ground [2])
  | sub {Γ : List Slot} {t : Tm} {A B : Ty} (h : Typed ps Γ t A) (hle : Sub ps A B) :
      Typed ps Γ t B
  | letE {Γ : List Slot} {a b : Tm} {A B : Ty}
      (ha : Typed ps Γ a A) (hb : Typed ps (.value A :: Γ) b B) :
      Typed ps Γ (.letE a b) B
  | defaultE {Γ : List Slot} {i : Nat} {B : Ty} {init : Tm}
      (hi : Γ[i]? = some (.argument B)) (hd : Typed ps Γ init B) :
      Typed ps Γ (.ite (.test .isUndef (.var i)) init (.var i)) B
  | lambda {Γ : List Slot} {receiver : Ty} {inputs : List Ty} {body : Tm} {B : Ty}
      (h : Typed ps (.value receiver :: (inputs.map Slot.value ++ Γ)) body B) :
      Typed ps Γ (.make (.closure inputs.length body) .nul) (.arrow receiver inputs B)
  /-- A plain call passes `undefined`, which the callee's receiver must admit. -/
  | call {Γ : List Slot} {fn : Tm} {args : List Tm} {rc : Ty} {inputs : List Ty} {result : Ty}
      (hf : Typed ps Γ fn (.arrow rc inputs result)) (hrecv : Sub ps (.ground [3]) rc)
      (hlen : args.length = inputs.length)
      (hargs : ∀ i (ha : i < args.length) (hi : i < inputs.length), Typed ps Γ args[i] inputs[i]) :
      Typed ps Γ (.call fn args) result

/-! ## Lists -/

theorem mapM_some_index {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ys.length = xs.length ∧ ∀ i (hx : i < xs.length) (hy : i < ys.length), f xs[i] = some ys[i]
  | [], ys, h => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun i hx => absurd hx (Nat.not_lt_zero _)⟩
  | x :: xs, ys, h => by
      cases hx : f x with
      | none => simp [List.mapM_cons, hx] at h
      | some y =>
        cases ht : xs.mapM f with
        | none => simp [List.mapM_cons, hx, ht] at h
        | some ys' =>
          simp [List.mapM_cons, hx, ht] at h
          subst h
          obtain ⟨hlen, hi⟩ := mapM_some_index ht
          refine ⟨by simp [hlen], fun i hx' hy' => ?_⟩
          cases i with
          | zero => exact hx
          | succ i => exact hi i (Nat.lt_of_succ_lt_succ hx') (Nat.lt_of_succ_lt_succ hy')

theorem mapM_of_index {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, ys.length = xs.length →
      (∀ i (hx : i < xs.length) (hy : i < ys.length), f xs[i] = some ys[i]) →
      xs.mapM f = some ys
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, hlen, h => by
      simp only [List.length_cons] at hlen
      have hx : f x = some y := h 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      have ht : xs.mapM f = some ys := mapM_of_index (Nat.add_right_cancel hlen)
        fun i hx' hy' => h (i + 1) (Nat.succ_lt_succ hx') (Nat.succ_lt_succ hy')
      simp [List.mapM_cons, hx, ht]

theorem exists_list : ∀ (n : Nat) (P : Nat → Proof → Prop), (∀ i, i < n → ∃ p, P i p) →
    ∃ ps : List Proof, ps.length = n ∧ ∀ i (hi : i < ps.length), P i ps[i]
  | 0, _, _ => ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | n + 1, P, h => by
      obtain ⟨p, hp⟩ := h 0 (Nat.zero_lt_succ _)
      obtain ⟨ps, hlen, hps⟩ := exists_list n (fun i q => P (i + 1) q)
        fun i hi => h (i + 1) (Nat.succ_lt_succ hi)
      refine ⟨p :: ps, by simp [hlen], fun i hi => ?_⟩
      cases i with
      | zero => exact hp
      | succ i => exact hps i (Nat.lt_of_succ_lt_succ hi)

/-! ## Every accepted certificate is a derivation -/

theorem Typed_of_check {ps : List Parameter} :
    ∀ (p : Proof) {Γ : List Slot} {t : Tm} {A : Ty},
      p.check ps Γ = some (t, A) → Typed ps Γ t A
  | .var i, Γ, t, A, hc => by
      cases hi : Γ[i]? with
      | none => simp [Proof.check, hi] at hc
      | some slot =>
        cases slot with
        | cell _ | argument _ => simp [Proof.check, hi] at hc
        | value B =>
          simp only [Proof.check, hi, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact .var hi
  | .read i, Γ, t, A, hc => by
      cases hi : Γ[i]? with
      | none => simp [Proof.check, hi] at hc
      | some slot =>
        cases slot with
        | value _ | argument _ => simp [Proof.check, hi] at hc
        | cell B =>
          simp only [Proof.check, hi, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact .read hi
  | .lit v, Γ, t, A, hc => by
      cases v with
      | vnull => simp only [Proof.check, Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc; exact .nul
      | vundef => simp only [Proof.check, Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc; exact .undef
      | vbool b =>
        cases b with
        | true => simp only [Proof.check, Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc; exact .tru
        | false => simp only [Proof.check, Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc; exact .fls
      | vnum _ => simp [Proof.check] at hc
      | vstr _ => simp [Proof.check] at hc
  | .widen expected body, Γ, t, A, hc => by
      cases hb : body.check ps Γ with
      | none => simp [Proof.check, hb] at hc
      | some pair =>
        obtain ⟨term, actual⟩ := pair
        simp only [Proof.check, hb] at hc
        split at hc
        · next hle =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact .sub (Typed_of_check body hb) (Sub_of_leUnder hle)
        · contradiction
  | .letE init body, Γ, t, A, hc => by
      cases ha : init.check ps Γ with
      | none => simp [Proof.check, ha] at hc
      | some pa =>
        obtain ⟨a, B⟩ := pa
        cases hb : body.check ps (.value B :: Γ) with
        | none => simp [Proof.check, ha, hb] at hc
        | some pb =>
          obtain ⟨b, C⟩ := pb
          simp only [Proof.check, ha, hb, Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact .letE (Typed_of_check init ha) (Typed_of_check body hb)
  | .defaultE i init, Γ, t, result, hc => by
      cases hi : Γ[i]? with
      | none => simp [Proof.check, hi] at hc
      | some slot =>
        cases slot with
        | cell _ | value _ => simp [Proof.check, hi] at hc
        | argument B =>
          cases hd : init.check ps Γ with
          | none => simp [Proof.check, hi, hd] at hc
          | some pair =>
            obtain ⟨term, actual⟩ := pair
            simp only [Proof.check, hi] at hc
            rw [hd] at hc
            change (if actual.leUnder ps B = true
              then some (Tm.ite (.test .isUndef (.var i)) term (.var i), B)
              else none) = some (t, result) at hc
            split at hc
            · next h =>
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
              exact .defaultE hi (.sub (Typed_of_check init hd) (Sub_of_leUnder h))
            · contradiction
  | .lambda receiver inputs body, Γ, t, A, hc => by
      cases hb : body.check ps (.value receiver :: (inputs.map Slot.value ++ Γ)) with
      | none => simp [Proof.check, hb] at hc
      | some pb =>
        obtain ⟨term, B⟩ := pb
        simp only [Proof.check, hb, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact .lambda (Typed_of_check body hb)
  | .call callee args, Γ, t, A, hc => by
      cases hf : callee.check ps Γ with
      | none => simp [Proof.check, hf] at hc
      | some pf =>
        obtain ⟨fn, F⟩ := pf
        cases F with
        | rigid _ | array _ | variadic _ _ _ _ | top => simp [Proof.check, hf] at hc
        | ground _ => simp [Proof.check, hf] at hc
        | arrow rc inputs result =>
          cases hm : args.mapM (fun arg => arg.check ps Γ) with
          | none => simp [Proof.check, hf, hm] at hc
          | some actuals =>
            by_cases hle : (Ty.arrow rc inputs result).leUnder ps
                (.arrow (.ground [3]) (actuals.map Prod.snd) result) = true
            · simp [Proof.check, hf, hm, hle] at hc
              obtain ⟨rfl, rfl⟩ := hc
              obtain ⟨hlen, hidx⟩ := mapM_some_index hm
              have hsub := Sub_of_leUnder hle
              cases hsub with
              | arrow hrecv hlen' hargs' _ =>
                refine .call (Typed_of_check callee hf) hrecv (by simpa using hlen'.symm) ?_
                intro i ha hi
                have hi' : i < actuals.length := by simpa using ha
                have hlt : i < args.length := by omega
                have hcheck := hidx i hlt hi'
                have hty := Typed_of_check (args[i]'hlt) hcheck
                have hle_i := hargs' i (by simpa using hi') hi
                simp only [List.getElem_map] at hle_i ⊢
                exact .sub hty hle_i
            · simp [Proof.check, hf, hm, hle] at hc
termination_by p => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem (List.getElem_mem ‹i < args.length›); omega)

/-! ## On well-formed parameters, every derivation has an accepted certificate -/

theorem check_of_Typed {ps : List Parameter} (hw : WellFormed ps) {Γ : List Slot} {t : Tm} {A : Ty}
    (h : Typed ps Γ t A) : ∃ p : Proof, p.check ps Γ = some (t, A) := by
  induction h with
  | @var Γ i A hi => exact ⟨.var i, by simp [Proof.check, hi]⟩
  | @read Γ i A hi => exact ⟨.read i, by simp [Proof.check, hi]⟩
  | nul => exact ⟨.lit .vnull, by simp [Proof.check]⟩
  | undef => exact ⟨.lit .vundef, by simp [Proof.check]⟩
  | tru => exact ⟨.lit (.vbool true), by simp [Proof.check]⟩
  | fls => exact ⟨.lit (.vbool false), by simp [Proof.check]⟩
  | @sub Γ t A B _ hle ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.widen B p, by simp [Proof.check, hp, leUnder_of_Sub hw hle]⟩
  | letE _ _ iha ihb =>
    obtain ⟨pa, hpa⟩ := iha
    obtain ⟨pb, hpb⟩ := ihb
    exact ⟨.letE pa pb, by simp [Proof.check, hpa, hpb]⟩
  | @defaultE Γ i B init hi _ ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨.defaultE i p, ?_⟩
    simp [Proof.check, hi, hp, leUnder_of_Sub hw (Sub.refl ps B)]
  | @lambda Γ receiver inputs body B _ ih =>
    obtain ⟨pb, hpb⟩ := ih
    exact ⟨.lambda receiver inputs pb, by simp [Proof.check, hpb]⟩
  | @call Γ fn args rc inputs result _ hrecv hlen _ ihf ihargs =>
    obtain ⟨pf, hpf⟩ := ihf
    obtain ⟨pargs, hplen, hpargs⟩ := exists_list args.length (fun i p =>
        ∀ (ha : i < args.length) (hi : i < inputs.length), p.check ps Γ = some (args[i], inputs[i]))
      (fun i hi => by
        obtain ⟨p, hp⟩ := ihargs i hi (by omega)
        exact ⟨p, fun _ _ => hp⟩)
    have hm : pargs.mapM (fun arg => arg.check ps Γ) = some (args.zip inputs) := by
      apply mapM_of_index
      · simp [List.length_zip, hplen, hlen]
      · intro i hx hy
        rw [List.getElem_zip]
        exact hpargs i hx (by omega) (by omega)
    refine ⟨.call pf pargs, ?_⟩
    have hfst : (args.zip inputs).map Prod.fst = args := List.map_fst_zip (by omega)
    have hsnd : (args.zip inputs).map Prod.snd = inputs := List.map_snd_zip (by omega)
    have hle : Ty.leUnder ps (.arrow rc inputs result) (.arrow (.ground [3]) inputs result) = true :=
      leUnder_of_Sub hw (.arrow hrecv rfl (fun i _ _ => Sub.refl ps inputs[i]) (Sub.refl ps result))
    simp [Proof.check, hpf, hm, hfst, hsnd, hle]

theorem check_iff_Typed {ps : List Parameter} (hw : WellFormed ps) {Γ : List Slot} {t : Tm} {A : Ty} :
    (∃ p : Proof, p.check ps Γ = some (t, A)) ↔ Typed ps Γ t A :=
  ⟨fun ⟨p, hp⟩ => Typed_of_check p hp, check_of_Typed hw⟩

/-- Safety of every derivation, through the accepted certificate it has. -/
theorem Typed.safe {G : PositiveGraphs.NormalGraph Nat} {ps : List Parameter} (hw : WellFormed ps)
    {Γ : List Slot} {t : Tm} {A : Ty} (h : Typed ps Γ t A) {η}
    (hC : ClosedAssign η) (hs : Satisfies G η ps) (hG : Primitives G) :
    ∀ n W heap ρ, EnvOk G η Γ ρ n W → WorldAdm W → HeapOk n W heap →
      Safe (A.denote G η) n W heap (instantiate 0 ρ t) := by
  obtain ⟨p, hp⟩ := check_of_Typed hw h
  exact Proof.check_safe hp hC hs hG

#print axioms check_iff_Typed
#print axioms Typed.safe
end Verification.Model.CertificateJudgments
