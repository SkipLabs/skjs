/-
  Obligation generation and discharge for the core calculus.

  It walks a span-carrying syntax tree, because that is what the claims are
  keyed to. Everything it concludes is a statement about the ERASURE of that
  tree into `Verification.Core`, which has no spans and no JSON. `checkFile_sound`
  is the whole point of this file:

      checkFile funs typeClaims = .ok ()  →  ProgOk (eraseProg funs)

  and `Core.sound` then says what `ProgOk` buys: a call cannot go wrong, and any
  value it returns inhabits the declared return type.

  Generation and discharge are fused: the traversal constructs each Obligation
  and immediately calls Obligation.discharge, storing no list of obligations.
  Expression type claims supply intermediate facts; source annotations specify
  required types. Environment claims are audited as well; the traversal
  propagates its own environment. Input validation associates claims with
  declarations and checks that required entries exist.

  The proofs below establish that this generation/checking traversal suffices
  for the calculus. Obligation.discharge_sound separately establishes the
  meaning of a successful type comparison. Neither theorem establishes that
  the exporter faithfully reports SKJS's internal state.
-/
import Verification.SkjsTypeClaims
import Verification.Lowering

namespace Verification

open Core hiding Fn

structure Ctx where
  /-- The erased program: the object every judgement below is about. -/
  prog : Core.Prog
  typeClaims : FunTypeClaims

/-! ### Expression obligations

Each `.subtype actual required` is one obligation (a verification condition,
in the standard terminology). For example a variable's derived binding must
fit its claimed expression type; a call argument's claimed type must fit the
callee's source parameter type. Discharging as we traverse
preserves the first failing obligation and avoids allocating a separate list. -/

private def mismatch (s : Span) : String :=
  s!"the type claimed at {spanStr s} does not contain every value that can reach it"

mutual

def checkExp (c : Ctx) (σ : Scope) (G : TEnv) (e : Expr) : Except String Ty :=
  match claimTy c.typeClaims e.span with
  | .error m => .error m
  | .ok t =>
    match e with
    | .var pos x =>
        match tenvGet G (slotOf σ x) with
        | none => .error s!"unbound variable '{x}' at {spanStr pos}"
        | some t0 => if Obligation.discharge (.subtype t0 t) then .ok t else .error (mismatch pos)
    | .lit pos v =>
        if Obligation.discharge (.subtype (ofAtom (atomOfVal v)) t) then .ok t else .error (mismatch pos)
    | .neg pos e1 =>
        match checkExp c σ G e1 with
        | .error m => .error m
        | .ok t1 =>
            if Obligation.discharge (.subtype t1 bool_) then
              (if Obligation.discharge (.subtype bool_ t) then .ok t else .error (mismatch pos))
            else .error "the operand of `!` must be a boolean"
    | .tyof pos e1 =>
        match checkExp c σ G e1 with
        | .error m => .error m
        | .ok t1 => if Obligation.discharge (.subtype (tagsOf t1) t) then .ok t else .error (mismatch pos)
    | .bin pos op l r =>
        match checkExp c σ G l with
        | .error m => .error m
        | .ok tl =>
          match op with
          | .eq =>
              match checkExp c σ G r with
              | .error m => .error m
              | .ok _ => if Obligation.discharge (.subtype bool_ t) then .ok t else .error (mismatch pos)
          | .ne =>
              match checkExp c σ G r with
              | .error m => .error m
              | .ok _ => if Obligation.discharge (.subtype bool_ t) then .ok t else .error (mismatch pos)
          | .and =>
              if Obligation.discharge (.subtype tl bool_) then
                match checkExp c σ (narrow G (eraseExp σ l) true) r with
                | .error m => .error m
                | .ok tr =>
                    if Obligation.discharge (.subtype tr bool_) then
                      (if Obligation.discharge (.subtype bool_ t) then .ok t else .error (mismatch pos))
                    else .error "the right operand of `&&` must be a boolean"
              else .error "the left operand of `&&` must be a boolean"
          | .or =>
              if Obligation.discharge (.subtype tl bool_) then
                match checkExp c σ (narrow G (eraseExp σ l) false) r with
                | .error m => .error m
                | .ok tr =>
                    if Obligation.discharge (.subtype tr bool_) then
                      (if Obligation.discharge (.subtype bool_ t) then .ok t else .error (mismatch pos))
                    else .error "the right operand of `||` must be a boolean"
              else .error "the left operand of `||` must be a boolean"
    | .call pos f args =>
        match lookupFun c.prog f with
        | none => .error s!"call to '{f}', which is not a function of this file"
        | some fn =>
            match checkArgs c σ G args fn.params with
            | .error m => .error m
            | .ok _ => if Obligation.discharge (.subtype fn.ret t) then .ok t else .error (mismatch pos)

def checkArgs (c : Ctx) (σ : Scope) (G : TEnv) : List Expr → List (String × Ty) → Except String Unit
  | [], [] => .ok ()
  | a :: as, (_, pt) :: ps =>
      match checkExp c σ G a with
      | .error m => .error m
      | .ok ta =>
          if Obligation.discharge (.subtype ta pt) then checkArgs c σ G as ps
          else .error "an argument is not within the declared parameter type"
  | _, _ => .error "wrong number of arguments"

end

/-! ### Expression checking is sound -/

mutual

theorem checkExp_sound (c : Ctx) (σ : Scope) (G : TEnv) (e : Expr) (t : Ty)
    (h : checkExp c σ G e = .ok t) : HasTy c.prog G (eraseExp σ e) t := by
  rw [checkExp] at h
  split at h
  · exact absurd h (by simp)
  · next tc hc =>
    split at h
    -- var
    · next pos x =>
      split at h
      · exact absurd h (by simp)
      · next t0 ht =>
        split at h
        · next hs => cases h; exact .var ht hs
        · exact absurd h (by simp)
    -- lit
    · next pos v =>
      split at h
      · next hs => cases h; exact .lit hs
      · exact absurd h (by simp)
    -- !
    · next pos e1 =>
      split at h
      · exact absurd h (by simp)
      · next t1 h1 =>
        split at h
        · next hb =>
          split at h
          · next hs =>
            cases h
            exact .not (HasTy_sub (checkExp_sound c σ G e1 t1 h1) hb) hs
          · exact absurd h (by simp)
        · exact absurd h (by simp)
    -- typeof
    · next pos e1 =>
      split at h
      · exact absurd h (by simp)
      · next t1 h1 =>
        split at h
        · next hs => cases h; exact .tyof (checkExp_sound c σ G e1 t1 h1) hs
        · exact absurd h (by simp)
    -- binary
    · next pos op l r =>
      split at h
      · exact absurd h (by simp)
      · next tl hl =>
        split at h
        -- ===
        · split at h
          · exact absurd h (by simp)
          · next tr hr =>
            split at h
            · next hs =>
              cases h
              exact .eq (checkExp_sound c σ G l tl hl) (checkExp_sound c σ G r tr hr) hs
            · exact absurd h (by simp)
        -- !==
        · split at h
          · exact absurd h (by simp)
          · next tr hr =>
            split at h
            · next hs =>
              cases h
              exact .ne (checkExp_sound c σ G l tl hl) (checkExp_sound c σ G r tr hr) hs
            · exact absurd h (by simp)
        -- &&
        · split at h
          · next hlb =>
            split at h
            · exact absurd h (by simp)
            · next tr hr =>
              split at h
              · next hrb =>
                split at h
                · next hs =>
                  cases h
                  exact .and (HasTy_sub (checkExp_sound c σ G l tl hl) hlb)
                    (HasTy_sub (checkExp_sound c σ _ r tr hr) hrb) hs
                · exact absurd h (by simp)
              · exact absurd h (by simp)
          · exact absurd h (by simp)
        -- ||
        · split at h
          · next hlb =>
            split at h
            · exact absurd h (by simp)
            · next tr hr =>
              split at h
              · next hrb =>
                split at h
                · next hs =>
                  cases h
                  exact .or (HasTy_sub (checkExp_sound c σ G l tl hl) hlb)
                    (HasTy_sub (checkExp_sound c σ _ r tr hr) hrb) hs
                · exact absurd h (by simp)
              · exact absurd h (by simp)
          · exact absurd h (by simp)
    -- call
    · next pos f args =>
      split at h
      · exact absurd h (by simp)
      · next fn hlk =>
        split at h
        · exact absurd h (by simp)
        · next hca =>
          split at h
          · next hs => cases h; exact .call hlk (checkArgs_sound c σ G args fn.params hca) hs
          · exact absurd h (by simp)

theorem checkArgs_sound (c : Ctx) (σ : Scope) (G : TEnv) (as : List Expr)
    (ps : List (String × Ty))
    (h : checkArgs c σ G as ps = .ok ()) : HasTyArgs c.prog G (eraseExps σ as) ps := by
  match as, ps with
  | [], [] => exact .nil
  | a :: as', (x, pt) :: ps' =>
    rw [checkArgs] at h
    split at h
    · exact absurd h (by simp)
    · next ta hta =>
      split at h
      · next hsub =>
        exact .cons (HasTy_sub (checkExp_sound c σ G a ta hta) hsub)
          (checkArgs_sound c σ G as' ps' h)
      · exact absurd h (by simp)
  | [], _ :: _ => exact absurd h (by simp [checkArgs])
  | _ :: _, [] => exact absurd h (by simp [checkArgs])

end

/-! ### Environment implication

`Covers G H` is semantic: every value environment agreeing with `G` agrees
with `H`. Forgetting a fact is sound; a binding `H` requires but `G` cannot
supply is not. The check ranges over the bindings `H` makes *effective* --
`tenvGet` takes the first match, so a shadowed entry is checked through the
one that shadows it rather than on its own. -/

def coversB (G H : TEnv) : Bool :=
  H.all (fun q =>
    match tenvGet H q.1 with
    | none => false
    | some required =>
      match tenvGet G q.1 with
      | none => false
      | some actual => Obligation.discharge (.subtype actual required))

private theorem tenvGet_mem {H : TEnv} {x : String} {t : Ty}
    (h : tenvGet H x = some t) : ∃ q ∈ H, q.1 = x := by
  induction H with
  | nil => simp [tenvGet] at h
  | cons q rest ih =>
    by_cases hq : q.1 = x
    · exact ⟨q, List.mem_cons_self .., hq⟩
    · have : (q.1 == x) = false := by simp [hq]
      rw [tenvGet, this] at h
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨r, hr, hrx⟩ := ih h
      exact ⟨r, List.mem_cons_of_mem _ hr, hrx⟩

theorem coversB_sound {G H : TEnv} (h : coversB G H = true) : Covers G H := by
  intro ρ hG x t ht
  obtain ⟨q, hq, hqx⟩ := tenvGet_mem ht
  have hall := (List.all_eq_true.mp h) q hq
  rw [hqx, ht] at hall
  simp only at hall
  split at hall
  · exact absurd hall (by simp)
  · rename_i actual hactual
    obtain ⟨v, hv, hm⟩ := hG x actual hactual
    exact ⟨v, hv, sub_sound hall hm⟩

/-! ### Node obligations

Every node's entry environment is supplied by the claim at the source
statement it came from; the checks below justify using it. An edge carries
the environment its source derived and must cover the environment its target
was given, so both predecessors of a join independently justify the join --
which is what lets a merge be checked without a least upper bound on types.
The function's entry edge is checked the same way. -/

def checkEdge (I : List TEnv) (G : TEnv) : Option Nat → Except String Unit
  | none => .error "control leaves the function without returning"
  | some k =>
    match I[k]? with
    | none => .error s!"no environment established for node {k}"
    | some H =>
        if coversB G H then .ok ()
        else .error s!"the environment claimed at node {k} is not justified by every edge into it"

private theorem checkEdge_sound {f : Core.Fn} {I : List TEnv} {G : TEnv} {o : Option Nat}
    (h : checkEdge I G o = .ok ()) : Edge f I G o := by
  cases o with
  | none => exact absurd h (by simp [checkEdge])
  | some k =>
    rw [checkEdge] at h
    split at h
    · exact absurd h (by simp)
    · rename_i H hH
      split at h
      · exact ⟨H, hH, coversB_sound (by assumption)⟩
      · exact absurd h (by simp)

/-- Check one node against the environment established for it. -/
def checkNode (c : Ctx) (f : Core.Fn) (I : List TEnv) (G : TEnv) (i : NodeInfo) :
    Except String Unit :=
  match checkExp c i.resolve G i.src with
  | .error m => .error m
  | .ok t =>
    match i.kind with
    | .ret =>
        if Obligation.discharge (.subtype t f.ret) then .ok ()
        else .error "the returned type is not within the declared return type"
    | .set slot next =>
        match i.annot with
        | none => checkEdge I (tenvSet G slot t) next
        | some a =>
            if Obligation.discharge (.subtype t a) then checkEdge I (tenvSet G slot a) next
            else .error s!"the initialiser of '{slot}' is not within its annotation"
    | .branch yes no =>
        if Obligation.discharge (.subtype t bool_) then
          match checkEdge I (narrow G (eraseExp i.resolve i.src) true) yes with
          | .error m => .error s!"on the true edge: {m}"
          | .ok _ =>
            match checkEdge I (narrow G (eraseExp i.resolve i.src) false) no with
            | .error m => .error s!"on the false edge: {m}"
            | .ok _ => .ok ()
        else .error "an `if` condition must be a boolean"

theorem checkNode_sound {c : Ctx} {f : Core.Fn} {I : List TEnv} {G : TEnv} {i : NodeInfo}
    (h : checkNode c f I G i = .ok ()) : NodeOk c.prog f I G i.toNode := by
  rw [checkNode] at h
  split at h
  · exact absurd h (by simp)
  · rename_i t ht
    have hty : HasTy c.prog G (eraseExp i.resolve i.src) t :=
      checkExp_sound c i.resolve G i.src t ht
    show NodeOk c.prog f I G (NodeInfo.toNode i)
    rw [NodeInfo.toNode]
    cases hk : i.kind with
    | ret =>
      rw [hk] at h
      cases hd : Obligation.discharge (.subtype t f.ret) with
      | false => rw [hd] at h; simp at h
      | true => exact .ret (HasTy_sub hty hd)
    | set slot next =>
      rw [hk] at h
      dsimp only at h
      cases ha : i.annot with
      | none => rw [ha] at h; exact .set hty (checkEdge_sound h)
      | some a =>
        rw [ha] at h
        dsimp only at h
        cases hd : Obligation.discharge (.subtype t a) with
        | false => rw [hd] at h; simp at h
        | true =>
          rw [hd] at h
          simp only [if_true] at h
          exact .set (HasTy_sub hty hd) (checkEdge_sound h)
    | branch yes no =>
      rw [hk] at h
      cases hb : Obligation.discharge (.subtype t bool_) with
      | false => rw [hb] at h; simp at h
      | true =>
        rw [hb] at h
        simp only [if_true] at h
        cases hyes : checkEdge I (narrow G (eraseExp i.resolve i.src) true) yes with
        | error m => rw [hyes] at h; simp at h
        | ok _ =>
          rw [hyes] at h
          cases hno : checkEdge I (narrow G (eraseExp i.resolve i.src) false) no with
          | error m => rw [hno] at h; simp at h
          | ok _ =>
            exact .branch (HasTy_sub hty hb) (checkEdge_sound hyes) (checkEdge_sound hno)


/-! ### Checking a whole graph

`I` is the environment assignment: one entry per node, taken from the claim
at the source statement that node came from and read in that node's scope.
Whatever it says, the checks below are what justify using it. -/

/-- The claim at `off`, translated from source names into the slots in scope
there. Bindings SKJS could not express in the fragment are dropped; a program
that reads one is rejected at the read. -/
def claimEnvAt (fc : FunTypeClaims) (off : Nat) (σ : Scope) : Except String TEnv :=
  match lookupEnv fc.envs off with
  | none => .error s!"no claimed environment for the statement at offset {off}"
  | some vars =>
      .ok (vars.filterMap fun (x, t) => t.map (fun ty => (slotOf σ x, ty)))

/-- A binding in scope but shadowed here, so no claim at this node names it.
Its type is read from where it was last visible: the claim at `from_`, or the
signature for a shadowed parameter. Bindings are immutable, so its type cannot
have changed in between.

Without this a shadowing block would drop the outer binding's type, and the
edge leaving the block could not re-establish what its target still needs. -/
def hiddenBinding (fc : FunTypeClaims) (h : Hidden) : Except String (String × Ty) :=
  match lookupEnv fc.envs h.from_ with
  | none => .error s!"no claimed environment for the statement at offset {h.from_}"
  | some vars =>
    match vars.find? (fun q => q.1 == h.as) with
    | some (_, some ty) => .ok (h.slot, ty)
    | some (_, none) =>
        .error s!"the claimed type of '{h.as}' is outside the supported fragment"
    | none =>
        .error s!"the environment claimed at offset {h.from_} does not describe '{h.as}', which is shadowed from there on but still in scope"

def nodeEnv (fc : FunTypeClaims) (i : NodeInfo) : Except String TEnv := do
  let visible ← claimEnvAt fc i.offset i.visible
  let hidden ← i.hidden.mapM (hiddenBinding fc)
  return visible ++ hidden

def buildEnvs (fc : FunTypeClaims) (infos : List NodeInfo) : Except String (List TEnv) :=
  infos.mapM (nodeEnv fc)

def checkNodes (c : Ctx) (f : Core.Fn) (I : List TEnv) :
    Nat → List TEnv → List NodeInfo → Except String Unit
  | _, [], [] => .ok ()
  | pc, G :: Is, i :: is =>
      match checkNode c f I G i with
      | .error m => .error s!"at node {pc}: {m}"
      | .ok _ => checkNodes c f I (pc + 1) Is is
  | _, _, _ => .error "the environment assignment does not match the graph"

theorem checkNodes_len (c : Ctx) (f : Core.Fn) (I : List TEnv) :
    ∀ (Is : List TEnv) (is : List NodeInfo) (pc : Nat),
      checkNodes c f I pc Is is = .ok () → Is.length = is.length
  | [], [], _, _ => rfl
  | G :: Is, i :: is, pc, h => by
    rw [checkNodes] at h
    split at h
    · exact absurd h (by simp)
    · simpa using checkNodes_len c f I Is is (pc + 1) h
  | [], _ :: _, _, h => absurd h (by simp [checkNodes])
  | _ :: _, [], _, h => absurd h (by simp [checkNodes])

theorem checkNodes_sound (c : Ctx) (f : Core.Fn) (I : List TEnv) :
    ∀ (Is : List TEnv) (is : List NodeInfo) (pc : Nat),
      checkNodes c f I pc Is is = .ok () →
      ∀ (k : Nat) G i, Is[k]? = some G → is[k]? = some i →
        NodeOk c.prog f I G i.toNode
  | [], [], _, _, k, _, _, hG, _ => absurd hG (by simp)
  | G :: Is, i :: is, pc, h, k, G', i', hG, hi => by
    rw [checkNodes] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hnode
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hG hi
        subst hG; subst hi
        exact checkNode_sound hnode
      | succ k =>
        simp only [List.getElem?_cons_succ] at hG hi
        exact checkNodes_sound c f I Is is (pc + 1) h k G' i' hG hi
  | [], _ :: _, _, h, _, _, _, _, _ => absurd h (by simp [checkNodes])
  | _ :: _, [], _, h, _, _, _, _, _ => absurd h (by simp [checkNodes])

/-! ### Verification entry points

Input validation requires the claimed signature to agree with the source. The
body is checked against the source annotation regardless, so that comparison
audits the claims rather than carrying the soundness argument. -/

def checkFun (p : Core.Prog) (f : Fn) (fc : FunTypeClaims) : Except String Unit :=
  match claimsBind f fc with
  | .error m => .error m
  | .ok _ =>
    let lw := lowerFn f
    match buildEnvs fc lw.infos with
    | .error m => .error m
    | .ok I =>
      match checkEdge I lw.fn.params (some 0) with
      | .error m => .error s!"at the function entry: {m}"
      | .ok _ => checkNodes { prog := p, typeClaims := fc } lw.fn I 0 I lw.infos

theorem checkFun_sound {p : Core.Prog} {f : Fn} {fc : FunTypeClaims}
    (h : checkFun p f fc = .ok ()) : ∃ I, Core.FnOk p (lowerFn f).fn I := by
  rw [checkFun] at h
  split at h
  · exact absurd h (by simp)
  · dsimp only at h
    split at h
    · exact absurd h (by simp)
    · rename_i I hI
      split at h
      · exact absurd h (by simp)
      · rename_i hentry
        refine ⟨I, ?_, ?_, ?_⟩
        · exact checkEdge_sound hentry
        · intro pc G hpc
          have hlen := checkNodes_len _ _ I I (lowerFn f).infos 0 h
          have : pc < (lowerFn f).infos.length := by
            rw [← hlen]; exact List.getElem?_eq_some_iff.mp hpc |>.1
          show ∃ node, ((lowerFn f).infos.map NodeInfo.toNode)[pc]? = some node
          rw [List.getElem?_map]
          simp [List.getElem?_eq_getElem this]
        · intro pc G node hpc hnode
          show NodeOk p (lowerFn f).fn I G node
          rw [lowerFn_code, List.getElem?_map] at hnode
          cases hi : (lowerFn f).infos[pc]? with
          | none => rw [hi] at hnode; exact absurd hnode (by simp)
          | some i =>
            rw [hi] at hnode
            simp only [Option.map_some, Option.some.injEq] at hnode
            subst hnode
            exact checkNodes_sound _ _ I I (lowerFn f).infos 0 h pc G i hpc hi

def checkAll (p : Core.Prog) (typeClaims : List FunTypeClaims) (funs : List Fn) :
    Except String Unit :=
  match funs with
  | [] => .ok ()
  | f :: rest =>
      match typeClaims.find? (fun fc => fc.namePos == f.namePos) with
      | none => .error s!"no claims for the function '{f.name}'"
      | some fc =>
          match checkFun p f fc with
          | .error m => .error s!"{f.name}: {m}"
          | .ok _ => checkAll p typeClaims rest

theorem checkAll_sound (p : Core.Prog) (typeClaims : List FunTypeClaims) :
    ∀ (funs : List Fn), checkAll p typeClaims funs = .ok () →
      ∀ f ∈ funs, ∃ I, Core.FnOk p (lowerFn f).fn I
  | [], _, _, hf => absurd hf (by simp)
  | g :: rest, h, f, hf => by
    rw [checkAll.eq_def] at h
    dsimp only at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · rename_i hfun
        rcases List.mem_cons.mp hf with rfl | hrest
        · exact checkFun_sound hfun
        · exact checkAll_sound p typeClaims rest h f hrest

def checkFile (funs : List Fn) (typeClaims : List FunTypeClaims) : Except String Unit :=
  if funs.length == typeClaims.length then checkAll (lowerProg funs) typeClaims funs
  else .error s!"the claims cover {typeClaims.length} functions but the file declares {funs.length}"

/-- **Verifier soundness.** Accepted claims mean the lowered program satisfies
the calculus. Nothing about spans, JSON or SKJS survives into the conclusion. -/
theorem checkFile_sound {funs : List Fn} {typeClaims : List FunTypeClaims}
    (h : checkFile funs typeClaims = .ok ()) : Core.ProgOk (lowerProg funs) := by
  intro fn hfn
  rw [checkFile] at h
  split at h
  · simp only [lowerProg, List.mem_map] at hfn
    obtain ⟨g, hg, rfl⟩ := hfn
    exact checkAll_sound _ _ _ h g hg
  · exact absurd h (by simp)

/-! ### What acceptance buys

Composing verifier soundness with calculus soundness: for a program whose
claims were accepted, calling any of its functions on arguments that inhabit
its parameter types cannot go wrong, and any value it returns inhabits the
declared return type. -/

theorem accepted_never_stuck {funs : List Fn} {typeClaims : List FunTypeClaims}
    (h : checkFile funs typeClaims = .ok ()) {fn : Core.Fn} (hfn : fn ∈ lowerProg funs)
    {vs : List Val} (hma : MemAll vs fn.params) (n : Nat) :
    Core.run (lowerProg funs) n fn 0 (bindParams fn.params vs) ≠ .stuck :=
  call_never_stuck (checkFile_sound h) hfn hma n

theorem accepted_returns_in_type {funs : List Fn} {typeClaims : List FunTypeClaims}
    (h : checkFile funs typeClaims = .ok ()) {fn : Core.Fn} (hfn : fn ∈ lowerProg funs)
    {vs : List Val} (hma : MemAll vs fn.params) (n : Nat) {v : Val}
    (hv : Core.run (lowerProg funs) n fn 0 (bindParams fn.params vs) = .ok v) :
    mem v fn.ret :=
  call_returns_in_type (checkFile_sound h) hfn hma n hv

end Verification
