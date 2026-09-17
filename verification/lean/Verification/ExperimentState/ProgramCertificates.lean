import Verification.ExperimentState.ProgramTyping

/-! Finite program evidence checked against the declarative rules. Each node
states its sequent explicitly. The external entry point also checks that the
root is the requested closed program and type; evidence cannot change the task.
No proof search or semantic observation budget is involved. -/
namespace Verification.ExperimentState.ProgramCertificates
open ProgramTyping PositiveNormalization PositiveGraphs PositiveRules

structure Sequent (ι : Type) where
  context : List (Ty ι)
  term : Tm
  type : Ty ι
  deriving DecidableEq

inductive Rule (ι : Type) where
  | var | nul | undef | tru | fls | truLit | flsLit | numLit | num | strLit | str
  | funE | app | letE | alloc | read | write | arith | test
  | ifBool | ifTrue | ifFalse
  | ifKnown (answer : Bool)
  | ifBoolVar (trueType falseType : Ty ι)
  | unionVar (slot : Nat)
  | makeCallable | callCallable | readCallable | writeCallable
  | sub (proof : PositiveCertificates.Proof ι)

inductive Evidence (ι : Type) where
  | node (claim : Sequent ι) (rule : Rule ι) (premises : List (Evidence ι))

def claim : Evidence ι → Sequent ι
  | .node j _ _ => j

/-- The premises a function-creation node owes: one checked body per declared
signature, in the order the checker expects. -/
abbrev funEPremises [DecidableEq ι] (G : NormalGraph ι) (Γ : List (Ty ι)) (A : Ty ι)
    (arity : Nat) (b : Tm) (ps : List (Sequent ι)) : Prop :=
  match expand G A with
  | [.arrs L] => (∀ p ∈ L, p.1.length = arity) ∧ ps = L.map (fun p => ⟨p.1 ++ Γ, b, p.2⟩)
  | _ => False

/-- Only finite, syntactic premises of one rule. -/
def Local [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) (r : Rule ι) (ps : List (Sequent ι)) : Prop :=
  match r, j.term, ps with
  | .var, .var i, [] => j.context[i]? = some j.type
  | .nul, .nul, [] => Represents G j.type .nul
  | .undef, .undef, [] => Represents G j.type .undef
  | .tru, .tru, [] | .fls, .fls, [] => Represents G j.type .bool
  | .truLit, .tru, [] => Represents G j.type (.boolLit true)
  | .flsLit, .fls, [] => Represents G j.type (.boolLit false)
  | .numLit, .num b, [] => Represents G j.type (.numLit b)
  | .num, .num _, [] => Represents G j.type .num
  | .strLit, .str s, [] => Represents G j.type (.strLit s)
  | .str, .str _, [] => Represents G j.type .str
  -- A source function has no properties of its own; the model still gives it a
  -- bag, so the shape of that allocation is fixed here rather than claimed.
  | .funE, .makeAt (.closure arity b) ns inits, ps =>
    ns = [valueField] ∧ inits = [Tm.nul] ∧ funEPremises G j.context j.type arity b ps
  | .app, .call f args, jf :: jas =>
    jf.context = j.context ∧ jf.term = f ∧ jas.map Sequent.term = args ∧
    (∀ ja ∈ jas, ja.context = j.context) ∧
    match expand G jf.type with
    | [.arrs L] => (jas.map Sequent.type, j.type) ∈ L
    | _ => False
  | .letE, .letE a b, [ja, jb] =>
    ja.context = j.context ∧ ja.term = a ∧ jb = ⟨ja.type :: j.context, b, j.type⟩
  | .alloc, .makeAt .absent ns inits, ps =>
    match expand G j.type with
    | [.refs fs []] =>
      ns.Nodup ∧ ns.length = ps.length ∧ ps.map Sequent.term = inits ∧
      (∀ p ∈ ps, p.context = j.context) ∧ fs = ns.zip (ps.map Sequent.type)
    | _ => False
  | .read, .readAt f a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧
    (match expand G ja.type with
     | [.refs fs []] => (f, j.type) ∈ fs
     | _ => False)
  | .write, .writeAt f a b, [ja, jb] =>
    ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
    Represents G j.type .nul ∧
    (match expand G ja.type with
     | [.refs fs []] => (f, jb.type) ∈ fs
     | _ => False)
  | .arith, .arith _ a b, [ja, jb] =>
    ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
    Answers G ja.type .isNum true ∧ Answers G jb.type .isNum true ∧ Represents G j.type .num
  | .test, .test _ a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧
    (.boolLit true) ∈ expand G j.type ∧ (.boolLit false) ∈ expand G j.type
  | .ifBool, .ite c t e, [jc,jt,je] =>
    jc.context = j.context ∧ jc.term = c ∧ Answers G jc.type .isBool true ∧
    jt = ⟨j.context,t,j.type⟩ ∧ je = ⟨j.context,e,j.type⟩
  | .ifKnown q, .ite c t e, [jc,jb] =>
    jc.context = j.context ∧ jc.term = c ∧ Represents G jc.type (.boolLit q) ∧
    jb = ⟨j.context, (if q then t else e), j.type⟩
  | .ifBoolVar T F, .ite (.var i) t e, [jt,je] =>
    (match j.context[i]? with | some C => Answers G C .isBool true | none => False) ∧
    Represents G T (.boolLit true) ∧ Represents G F (.boolLit false) ∧
    jt = ⟨j.context.set i T,t,j.type⟩ ∧ je = ⟨j.context.set i F,e,j.type⟩
  | .ifTrue, .ite (.test tag (.var i)) u _, [ju] =>
    ju = ⟨j.context, u, j.type⟩ ∧
    match j.context[i]? with
    | some A => Answers G A tag true
    | none => False
  | .ifFalse, .ite (.test tag (.var i)) _ e, [je] =>
    je = ⟨j.context, e, j.type⟩ ∧
    match j.context[i]? with
    | some A => Answers G A tag false
    | none => False
  | .unionVar i, _, ps =>
    match j.context[i]? with
    | some C => ps = C.map (fun a => ⟨j.context.set i [a], j.term, j.type⟩)
    | none => False
  -- The bag's premises come first, one per named field, then the body's.
  | .makeCallable, .makeAt (.closure arity b) ns inits, ps =>
    match expand G j.type with
    | [.callable P [] L] =>
      ns.Nodup ∧ ns.length = inits.length ∧
      (ps.take ns.length).map Sequent.term = inits ∧
      (∀ p ∈ ps.take ns.length, p.context = j.context) ∧
      P = ns.zip ((ps.take ns.length).map Sequent.type) ∧
      (∀ p ∈ L, p.1.length = arity) ∧
      ps.drop ns.length = L.map (fun p => ⟨p.1 ++ j.context,b,p.2⟩)
    | _ => False
  | .callCallable, .call f args, jf :: jas =>
    jf.context = j.context ∧ jf.term = f ∧ jas.map Sequent.term = args ∧
    (∀ ja ∈ jas, ja.context = j.context) ∧
    match expand G jf.type with
    | [.callable _ _ L] => (jas.map Sequent.type,j.type) ∈ L
    | _ => False
  | .readCallable, .readAt f a, [ja] =>
    ja.context = j.context ∧ ja.term = a ∧
    match expand G ja.type with
    | [.callable P _ _] => (f, j.type) ∈ P
    | _ => False
  | .writeCallable, .writeAt f a b, [ja,jb] =>
    ja.context = j.context ∧ ja.term = a ∧ jb.context = j.context ∧ jb.term = b ∧
    Represents G j.type .nul ∧
    match expand G ja.type with
    | [.callable P _ _] => (f, jb.type) ∈ P
    | _ => False
  | .sub proof, _, [jt] =>
    jt.context = j.context ∧ jt.term = j.term ∧
    PositiveCertificates.check G jt.type j.type proof = true
  | _, _, _ => False

instance [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) (r : Rule ι) (ps) :
    Decidable (Local G j r ps) := by
  unfold Local
  split <;> try infer_instance
  all_goals try dsimp [Represents, Answers, funEPremises]
  all_goals first | infer_instance | (split <;> infer_instance)

def checkTree [DecidableEq ι] (G : NormalGraph ι) : Evidence ι → Bool
  | .node j r ps => decide (Local G j r (ps.map claim)) && ps.attach.all (fun e => checkTree G e.val)
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem e.property
  simp only [Evidence.node.sizeOf_spec]
  omega

mutual
def checkScope (d : Nat) : Tm → Bool
  | .var i => decide (i < d)
  | .objAt _ .absent => true
  | .objAt _ (.closure n b) => checkScope (d+n) b
  | .makeAt (.closure n b) _ args => checkScope (d+n) b && checkScopes d args
  | .makeAt .absent _ args => checkScopes d args
  | .letE a b => checkScope d a && checkScope (d+1) b
  | .call f args => checkScope d f && checkScopes d args
  | .writeAt _ a b | .arith _ a b => checkScope d a && checkScope d b
  | .readAt _ a | .test _ a => checkScope d a
  | .ite c a b => checkScope d c && checkScope d a && checkScope d b
  | _ => true

def checkScopes (d : Nat) : List Tm → Bool
  | [] => true
  | a :: args => checkScope d a && checkScopes d args
end

@[simp] theorem checkScopes_iff (d : Nat) (args : List Tm) :
    checkScopes d args = true ↔ ∀ a ∈ args, checkScope d a = true := by
  induction args <;> simp_all [checkScopes]

theorem checkScope_iff (d : Nat) (t : Tm) : checkScope d t = true ↔ Scoped d t := by
  induction t using Tm.induct generalizing d <;> simp_all [checkScope, Scoped, and_assoc]

/-- Bind evidence to the actual requested program, type and empty context.
Scope includes unselected branches and bodies of empty overloads. -/
def check [DecidableEq ι] (G : NormalGraph ι) (t : Tm) (A : Ty ι) (e : Evidence ι) : Bool :=
  decide (claim e = ⟨[], t, A⟩) && checkScope 0 t && checkTree G e

theorem local_sound [DecidableEq ι] {G : NormalGraph ι} {j r ps}
    (hl : Local G j r ps)
    (hp : ∀ p ∈ ps, HasTy G p.context p.term p.type) : HasTy G j.context j.term j.type := by
  rcases j with ⟨Γ, t, A⟩
  unfold Local at hl
  split at hl <;> (try dsimp only at *) <;> (try subst t)
  · exact .var hl
  · exact .nul hl
  · exact .undef hl
  · exact .tru hl
  · exact .fls hl
  · exact .truLit hl
  · exact .flsLit hl
  · exact .numLit hl
  · exact .num hl
  · exact .strLit hl
  · exact .str hl
  · rename_i ps arity b ns inits
    obtain ⟨rfl, rfl, hl⟩ := hl
    unfold funEPremises at hl
    split at hl
    · rename_i L hL
      apply HasTy.funE hL hl.1
      intro p hmem
      apply hp ⟨p.1 ++ Γ, b, p.2⟩
      rw [hl.2]
      exact List.mem_map.mpr ⟨p, hmem, rfl⟩
    · contradiction
  · rename_i f args jf jas
    rcases hl with ⟨hΓf, htf, hargs, hcontexts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    split at hL
    · rename_i L he
      have ha : ∀ p ∈ jas.map (fun ja => (ja.type,ja.term)), HasTy G Γ p.2 p.1 := by
        intro p hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ hja)
        rw [hcontexts ja hja] at h
        exact h
      have h := HasTy.app hf he (xs := jas.map (fun ja => (ja.type,ja.term)))
        (by simpa only [List.map_map,Function.comp_def] using hL) ha
      simpa only [List.map_map,Function.comp_def,hargs] using h
    · contradiction
  · rename_i a b ja jb
    rcases hl with ⟨hΓ, ht, rfl⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    exact .letE ha (hp ⟨ja.type :: Γ, b, A⟩ (by simp))
  · rename_i ps _ _ _ ns inits
    split at hl
    · rename_i fs he
      obtain ⟨hnd, hlen, hterms, hctx, rfl⟩ := hl
      have hzl : (ns.zip ps).length = ns.length := by simp [hlen]
      have hfst : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map Prod.fst = ns := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map (fun p => p.2.2)
          = inits := by
        rw [← hterms]
        simp only [List.map_map, Function.comp_def]
        calc (ns.zip ps).map (fun r => r.2.term)
            = ((ns.zip ps).map Prod.snd).map Sequent.term := by
              simp [List.map_map, Function.comp_def]
          _ = ps.map Sequent.term := by rw [List.map_snd_zip (by omega)]
      have htyp : ((ns.zip ps).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => (p.1, p.2.1)) = ns.zip (ps.map Sequent.type) := by
        rw [List.zip_map_right]
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro r _
        rfl
      have := HasTy.alloc (G := G) (Γ := Γ) (Ref := A)
        (parts := (ns.zip ps).map fun r => (r.1, r.2.type, r.2.term))
        (by rw [hfst]; exact hnd)
        (by
          intro q hq
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
          have hmem : r.2 ∈ ps := (List.of_mem_zip (by simpa using hr)).2
          have h := hp r.2 hmem
          rw [hctx r.2 hmem] at h
          exact h)
        (by rw [htyp]; exact he)
      rw [hfst, hsnd] at this
      exact this
    · contradiction
  · rename_i f a ja
    rcases hl with ⟨hΓ, ht, hr⟩
    have ha := hp ja (by simp)
    rw [hΓ, ht] at ha
    split at hr
    · rename_i fs he
      exact .read ha he hr
    · contradiction
  · rename_i f a b ja jb
    rcases hl with ⟨hΓa, hta, hΓb, htb, hn, hr⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa, hta] at ha
    rw [hΓb, htb] at hb
    split at hr
    · rename_i fs he
      exact .write ha he hr hb hn
    · contradiction
  · rename_i op a b ja jb
    rcases hl with ⟨hΓa, hta, hΓb, htb, hqa, hqb, hn⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa, hta] at ha
    rw [hΓb, htb] at hb
    exact .arith ha hqa hb hqb hn
  · rename_i k a ja
    rcases hl with ⟨hΓ, hta, ht, hf⟩
    have ha := hp ja (by simp)
    rw [hΓ, hta] at ha
    exact .test ha ht hf
  · rename_i c t e jc jt je
    rcases hl with ⟨hΓ, hc, hb, rfl, rfl⟩
    have hcond := hp jc (by simp)
    rw [hΓ, hc] at hcond
    exact .ifBool hcond hb (hp ⟨Γ,t,A⟩ (by simp)) (hp ⟨Γ,e,A⟩ (by simp))
  · rename_i q c t e jc jb
    rcases hl with ⟨hΓ,hc,hq,rfl⟩
    have hcond := hp jc (by simp)
    rw [hΓ,hc] at hcond
    exact .ifKnown hcond hq (hp ⟨Γ,(if q then t else e),A⟩ (by simp))
  · rename_i T F i t e jt je
    rcases hl with ⟨hb,hT,hF,rfl,rfl⟩
    split at hb
    · rename_i C hc
      exact .ifBoolVar hc hb hT hF (hp ⟨Γ.set i T,t,A⟩ (by simp)) (hp ⟨Γ.set i F,e,A⟩ (by simp))
    · contradiction
  · rename_i tag i u e ju
    rcases hl with ⟨rfl, hq⟩
    split at hq
    · rename_i D hd
      exact .ifTag hd hq (fun _ => hp ⟨Γ, u, A⟩ (by simp)) (by intro h; cases h)
    · contradiction
  · rename_i tag i u e je
    rcases hl with ⟨rfl, hq⟩
    split at hq
    · rename_i D hd
      exact .ifTag hd hq (by intro h; cases h) (fun _ => hp ⟨Γ, e, A⟩ (by simp))
    · contradiction
  · rename_i t ps i
    split at hl
    · rename_i C hi
      apply HasTy.unionVar hi
      intro a ha
      apply hp ⟨Γ.set i [a], _, A⟩
      rw [hl]
      exact List.mem_map.mpr ⟨a,ha,rfl⟩
    · contradiction
  · rename_i ps _ _ _ arity b ns inits
    split at hl
    · rename_i P L hr
      obtain ⟨hnd,hlen,hterms,hctx,rfl,harity,hbodies⟩ := hl
      have hplen : (ps.take ns.length).length = ns.length := by
        have : ns.length ≤ ps.length := by
          have := congrArg List.length hterms
          simp only [List.length_map, List.length_take] at this
          omega
        simp only [List.length_take]
        omega
      have hfst : ((ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)).map
          Prod.fst = ns := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_fst_zip (by omega)
      have hsnd : ((ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => p.2.2) = inits := by
        rw [← hterms]
        simp only [List.map_map, Function.comp_def]
        calc (ns.zip (ps.take ns.length)).map (fun r => r.2.term)
            = ((ns.zip (ps.take ns.length)).map Prod.snd).map Sequent.term := by
              simp [List.map_map, Function.comp_def]
          _ = (ps.take ns.length).map Sequent.term := by
              rw [List.map_snd_zip (by omega)]
      have htyp : ((ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term)).map
          (fun p => (p.1, p.2.1)) = ns.zip ((ps.take ns.length).map Sequent.type) := by
        rw [List.zip_map_right]
        simp only [List.map_map, Function.comp_def]
        apply List.map_congr_left
        intro r _
        rfl
      have := HasTy.makeCallable (G := G) (Γ := Γ) (F := A) (arity := arity) (b := b) (L := L)
        (parts := (ns.zip (ps.take ns.length)).map fun r => (r.1, r.2.type, r.2.term))
        (by rw [htyp]; exact hr)
        (by rw [hfst]; exact hnd)
        (by
          intro q hq
          obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
          have hmem : r.2 ∈ ps := List.mem_of_mem_take (List.of_mem_zip (by simpa using hr')).2
          have h := hp r.2 hmem
          rw [hctx r.2 (List.of_mem_zip (by simpa using hr')).2] at h
          exact h)
        harity
        (by
          intro q hq
          apply hp ⟨q.1 ++ Γ, b, q.2⟩
          have : (⟨q.1 ++ Γ, b, q.2⟩ : Sequent ι) ∈ ps.drop ns.length := by
            rw [hbodies]
            exact List.mem_map.mpr ⟨q, hq, rfl⟩
          exact List.mem_of_mem_drop this)
      rw [hfst, hsnd] at this
      exact this
    · contradiction
  · rename_i f args jf jas
    rcases hl with ⟨hΓf, htf, hargs, hcontexts, hL⟩
    have hf := hp jf (by simp)
    rw [hΓf, htf] at hf
    split at hL
    · rename_i P Ps L he
      have ha : ∀ p ∈ jas.map (fun ja => (ja.type,ja.term)), HasTy G Γ p.2 p.1 := by
        intro p hm
        obtain ⟨ja,hja,rfl⟩ := List.mem_map.mp hm
        have h := hp ja (List.mem_cons_of_mem _ hja)
        rw [hcontexts ja hja] at h
        exact h
      have h := HasTy.callCallable hf he (xs := jas.map (fun ja => (ja.type,ja.term)))
        (by simpa only [List.map_map,Function.comp_def] using hL) ha
      simpa only [List.map_map,Function.comp_def,hargs] using h
    · contradiction
  · rename_i a ja
    rcases hl with ⟨hΓ,ht,hL⟩
    have ha := hp ja (by simp)
    rw [hΓ,ht] at ha
    split at hL
    · rename_i P Ps L he
      exact .readCallable ha he hL
    · contradiction
  · rename_i a b ja jb
    rcases hl with ⟨hΓa,hta,hΓb,htb,hn,hL⟩
    have ha := hp ja (by simp)
    have hb := hp jb (by simp)
    rw [hΓa,hta] at ha
    rw [hΓb,htb] at hb
    split at hL
    · rename_i P Ps L he
      exact .writeCallable ha he hL hb hn
    · contradiction
  · rename_i proof t jt
    rcases hl with ⟨hΓ, ht, hc⟩
    have hj := hp jt (by simp)
    rw [hΓ, ht] at hj
    exact .sub hj hc

theorem checkTree_sound [DecidableEq ι] {G : NormalGraph ι} (e : Evidence ι)
    (he : checkTree G e = true) : HasTy G (claim e).context (claim e).term (claim e).type := by
  cases e with
  | node j r ps =>
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at he
    apply local_sound he.1
    intro p hp
    obtain ⟨e, he', rfl⟩ := List.mem_map.mp hp
    exact checkTree_sound e (he.2 ⟨e, he'⟩ (by simp))
termination_by sizeOf e

theorem check_sound [DecidableEq ι] {G : NormalGraph ι} {t A e}
    (he : check G t A e = true) : Scoped 0 t ∧ HasTy G [] t A := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at he
  refine ⟨(checkScope_iff 0 t).mp he.1.2, ?_⟩
  have ht := checkTree_sound e he.2
  simpa only [he.1.1] using ht

theorem accepted_safe [DecidableEq ι] {G : NormalGraph ι} {t A e}
    (he : check G t A e = true) (n W h) (hw : WorldAdm W) (hh : HeapOk n W h) :
    Safe (meaning G A) n W h t :=
  (check_sound he).2.closed_safe (check_sound he).1 n W h hw hh

def Representable [DecidableEq ι] (G : NormalGraph ι) (j : Sequent ι) : Prop :=
  ∃ e, claim e = j ∧ checkTree G e = true

private theorem gather [DecidableEq ι] {G : NormalGraph ι} (js : List (Sequent ι))
    (h : ∀ j ∈ js, Representable G j) :
    ∃ es : List (Evidence ι), es.map claim = js ∧ ∀ e ∈ es, checkTree G e = true := by
  induction js with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons j js ih =>
    obtain ⟨e, he, hc⟩ := h j (by simp)
    obtain ⟨es, hes, hcs⟩ := ih (fun k hk => h k (by simp [hk]))
    refine ⟨e :: es, by simp [he, hes], ?_⟩
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | hm
    · exact hc
    · exact hcs e' hm

private theorem node_complete [DecidableEq ι] {G : NormalGraph ι} {j r js}
    (hl : Local G j r js) (h : ∀ p ∈ js, Representable G p) : Representable G j := by
  obtain ⟨es, hes, hcs⟩ := gather js h
  refine ⟨.node j r es, rfl, ?_⟩
  simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨by simpa only [hes] using hl, fun e _ => hcs e.val e.property⟩

/-- Every declarative derivation has finite accepted evidence. This is coverage
of the rules, not semantic completeness and not a proof-search algorithm. -/
theorem checkTree_complete [DecidableEq ι] {G : NormalGraph ι} {Γ t A}
    (ht : HasTy G Γ t A) : Representable G ⟨Γ, t, A⟩ := by
  induction ht with
  | var hi => exact node_complete (r := .var) (js := []) hi (by simp)
  | nul hr => exact node_complete (r := .nul) (js := []) hr (by simp)
  | undef hr => exact node_complete (r := .undef) (js := []) hr (by simp)
  | tru hr => exact node_complete (r := .tru) (js := []) hr (by simp)
  | fls hr => exact node_complete (r := .fls) (js := []) hr (by simp)
  | truLit hr => exact node_complete (r := .truLit) (js := []) hr (by simp)
  | flsLit hr => exact node_complete (r := .flsLit) (js := []) hr (by simp)
  | numLit hr => exact node_complete (r := .numLit) (js := []) hr (by simp)
  | num hr => exact node_complete (r := .num) (js := []) hr (by simp)
  | strLit hr => exact node_complete (r := .strLit) (js := []) hr (by simp)
  | str hr => exact node_complete (r := .str) (js := []) hr (by simp)
  | @funE F L arity Γ b hr hlen hb ih =>
    apply node_complete (r := .funE) (js := L.map (fun p => ⟨p.1 ++ Γ, b, p.2⟩))
    · refine ⟨rfl, rfl, ?_⟩
      show funEPremises G Γ F arity b _
      simpa only [funEPremises, show expand G F = [.arrs L] from hr, and_true] using hlen
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @makeCallable F L Γ arity b parts hr hnd hpart hlen hb ih ihb =>
    apply node_complete (r := .makeCallable)
      (j := ⟨Γ, .makeAt (.closure arity b) (parts.map Prod.fst) (parts.map fun p => p.2.2), F⟩)
      (js := (parts.map fun p => ⟨Γ, p.2.2, p.2.1⟩) ++ L.map (fun p => ⟨p.1 ++ Γ,b,p.2⟩))
    · simp only [Local,
        show expand G F = [.callable (parts.map fun p => (p.1, p.2.1)) [] L] from hr]
      have hlenp : (parts.map fun p => (⟨Γ, p.2.2, p.2.1⟩ : Sequent ι)).length
          = (parts.map Prod.fst).length := by simp
      refine ⟨hnd, by simp, ?_, ?_, ?_, hlen, ?_⟩
      · rw [List.take_left' hlenp]
        simp [List.map_map, Function.comp_def]
      · rw [List.take_left' hlenp]
        intro q hq
        obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq
        rfl
      · rw [List.take_left' hlenp]
        simp only [List.map_map, Function.comp_def]
        rw [List.zip_map']
      · rw [List.drop_left' hlenp]
    · intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
        exact ih p hp
      · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
        exact ihb p hp
  | @callCallable Γ f F P Ps L xs B hf hr hp ha ihf iha =>
    apply node_complete (r := .callCallable)
      (js := ⟨Γ,f,F⟩ :: xs.map (fun p => ⟨Γ,p.2,p.1⟩))
    · refine ⟨rfl,rfl,?_,?_,?_⟩
      · simp only [List.map_map,Function.comp_def]
      · intro ja hj
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
        rfl
      · simpa only [show expand G F = [.callable P Ps L] from hr,List.map_map,Function.comp_def] using hp
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihf
      · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
        exact iha p hp
  | @readCallable Γ a F P Ps L f A ha hr hm ih =>
    apply node_complete (G := G) (j := ⟨Γ,.readAt f a,A⟩) (r := .readCallable) (js := [⟨Γ,a,F⟩])
    · simpa [Local,show expand G F = [.callable P Ps L] from hr] using hm
    · simpa using ih
  | @writeCallable Γ a F P Ps L f A b N ha hr hm hb hn iha ihb =>
    apply node_complete (G := G) (j := ⟨Γ,.writeAt f a b,N⟩) (r := .writeCallable)
      (js := [⟨Γ,a,F⟩,⟨Γ,b,A⟩])
    · exact ⟨rfl,rfl,rfl,rfl,hn,by
        simp only [show expand G F = [.callable P Ps L] from hr]
        exact hm⟩
    · intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl
      · exact iha
      · exact ihb
  | @app Γ f F L xs B hf hr hp ha ihf iha =>
    apply node_complete (r := .app)
      (js := ⟨Γ,f,F⟩ :: xs.map (fun p => ⟨Γ,p.2,p.1⟩))
    · refine ⟨rfl,rfl,?_,?_,?_⟩
      · simp only [List.map_map,Function.comp_def]
      · intro ja hj
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
        rfl
      · simpa only [show expand G F = [.arrs L] from hr,List.map_map,Function.comp_def] using hp
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ihf
      · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hj
        exact iha p hp
  | @letE Γ a A b B ha hb iha ihb =>
    apply node_complete (r := .letE) (js := [⟨Γ,a,A⟩, ⟨A::Γ,b,B⟩])
    · exact ⟨rfl, rfl, rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact iha
      · exact ihb
  | @alloc Γ Ref parts hnd hpart hr ih =>
    apply node_complete (G := G)
      (j := ⟨Γ, .makeAt .absent (parts.map Prod.fst) (parts.map fun p => p.2.2), Ref⟩)
      (r := .alloc) (js := parts.map fun p => ⟨Γ, p.2.2, p.2.1⟩)
    · simp only [Local, show expand G Ref = [.refs (parts.map fun p => (p.1, p.2.1)) []] from hr]
      refine ⟨hnd, by simp, by simp [List.map_map, Function.comp_def], by
        intro q hq; obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hq; rfl, ?_⟩
      simp only [List.map_map, Function.comp_def]
      rw [List.zip_map']
    · intro j hj
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hj
      exact ih p hp
  | @read Γ a Ref fs f A ha hr hm ih =>
    apply node_complete (G := G) (j := ⟨Γ, .readAt f a, A⟩) (r := .read) (js := [⟨Γ,a,Ref⟩])
      ⟨rfl,rfl,by simp only [show expand G Ref = [.refs fs []] from hr]; exact hm⟩
    simpa using ih
  | @test Γ a A B k ha ht hf ih =>
    apply node_complete (G := G) (j := ⟨Γ, .test k a, B⟩) (r := .test) (js := [⟨Γ,a,A⟩])
      ⟨rfl,rfl,ht,hf⟩
    simpa using ih
  | @arith Γ a A b B N op ha hqa hb hqb hn iha ihb =>
    apply node_complete (G := G) (j := ⟨Γ, .arith op a b, N⟩) (r := .arith)
      (js := [⟨Γ,a,A⟩, ⟨Γ,b,B⟩]) ⟨rfl,rfl,rfl,rfl,hqa,hqb,hn⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihb
  | @write Γ a Ref fs f A b N ha hr hm hb hn iha ihb =>
    apply node_complete (G := G) (j := ⟨Γ, .writeAt f a b, N⟩) (r := .write)
      (js := [⟨Γ,a,Ref⟩, ⟨Γ,b,A⟩])
      ⟨rfl,rfl,rfl,rfl,hn,by simp only [show expand G Ref = [.refs fs []] from hr]; exact hm⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact iha
    · exact ihb
  | @ifBool Γ c C t A e hc hb ht he ihc iht ihe =>
    apply node_complete (r := .ifBool) (js := [⟨Γ,c,C⟩,⟨Γ,t,A⟩,⟨Γ,e,A⟩])
    · exact ⟨rfl,rfl,hb,rfl,rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl
      · exact ihc
      · exact iht
      · exact ihe
  | @ifKnown Γ c C q t e A hc hq ht ihc iht =>
    apply node_complete (r := .ifKnown q) (js := [⟨Γ,c,C⟩,⟨Γ,(if q then t else e),A⟩])
    · exact ⟨rfl,rfl,hq,rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact ihc
      · exact iht
  | @ifBoolVar Γ i C T F t A e hi hb hT hF ht he iht ihe =>
    apply node_complete (r := .ifBoolVar T F) (js := [⟨Γ.set i T,t,A⟩,⟨Γ.set i F,e,A⟩])
    · exact ⟨by simpa only [Local, hi] using hb,hT,hF,rfl,rfl⟩
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact iht
      · exact ihe
  | @ifTag Γ i A tag q u B e hi hq ht he iht ihe =>
    cases q with
    | true =>
      apply node_complete (r := .ifTrue) (js := [⟨Γ,u,B⟩])
      · simpa only [Local, hi, true_and] using hq
      · simpa using iht rfl
    | false =>
      apply node_complete (r := .ifFalse) (js := [⟨Γ,e,B⟩])
      · simpa only [Local, hi, true_and] using hq
      · simpa using ihe rfl
  | @unionVar Γ i C t A hi ht ih =>
    apply node_complete (r := .unionVar i)
      (js := C.map (fun a => ⟨Γ.set i [a], t, A⟩))
    · simp [Local,hi]
    · intro j hj
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hj
      exact ih a ha
  | @sub Γ t A B cert ht hc ih =>
    apply node_complete (G := G) (j := ⟨Γ, t, B⟩) (r := .sub cert) (js := [⟨Γ,t,A⟩]) ⟨rfl,rfl,hc⟩
    simpa using ih

theorem derivable_iff_checked [DecidableEq ι] (G : NormalGraph ι) (t : Tm) (A : Ty ι) :
    (Scoped 0 t ∧ HasTy G [] t A) ↔ ∃ e, check G t A e = true := by
  constructor
  · rintro ⟨hs, ht⟩
    obtain ⟨e, he, hc⟩ := checkTree_complete ht
    exact ⟨e, by simp [check, he, (checkScope_iff 0 t).mpr hs, hc]⟩
  · rintro ⟨e, he⟩; exact check_sound he

#print axioms checkTree_sound
#print axioms derivable_iff_checked
#print axioms accepted_safe
end Verification.ExperimentState.ProgramCertificates
