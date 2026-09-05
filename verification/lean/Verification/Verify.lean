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

/-! ### A fact about source translation -/

theorem eraseEls_eq (els : Option (List Stmt)) : eraseEls els = eraseStms (elseBody els) := by
  cases els <;> simp [eraseEls, eraseStms, elseBody]

/-- SKJS's environment must contain every binding the checker derived, no
narrower than the checker derived it. This is a check ON THE CLAIMS: the
checker reasons with its own environment, which is never wider, so a failure
here means SKJS narrowed further than the typing rules justify. -/
def envCoversAt (at_ : Nat) (derived claimed : TEnv) : List String → Except String Unit
  | [] => .ok ()
  | x :: xs =>
      -- `tenvSet` shadows rather than replaces, so a name can appear more than
      -- once in `derived`; only the first binding is live, and `tenvGet` picks
      -- exactly that one. Checking the raw list instead would test bindings the
      -- program can no longer see.
      match tenvGet derived x with
      | none => envCoversAt at_ derived claimed xs
      | some t =>
        match tenvGet claimed x with
        | none => .error s!"the environment claimed at offset {at_} is missing the binding '{x}'"
        | some rt =>
            if Obligation.discharge (.subtype t rt) then envCoversAt at_ derived claimed xs
            else .error ("the type claimed for '" ++ x ++ "' at offset " ++ toString at_ ++
              " does not contain every value that can reach it: it narrows further" ++
              " than the typing rules justify")

def envCovers (at_ : Nat) (derived : TEnv) (claimed : TEnv) : Except String Unit :=
  envCoversAt at_ derived claimed (derived.map Prod.fst)

/-! ### Expression obligations

Each `.subtype actual required` is one obligation (a verification condition,
in the standard terminology). For example a variable's derived binding must
fit its claimed expression type; a call argument's claimed type must fit the
callee's source parameter type. Discharging as we traverse
preserves the first failing obligation and avoids allocating a separate list. -/

private def mismatch (s : Span) : String :=
  s!"the type claimed at {spanStr s} does not contain every value that can reach it"

mutual

def checkExp (c : Ctx) (G : TEnv) (e : Expr) : Except String Ty :=
  match claimTy c.typeClaims e.span with
  | .error m => .error m
  | .ok t =>
    match e with
    | .var pos x =>
        match tenvGet G x with
        | none => .error s!"unbound variable '{x}' at {spanStr pos}"
        | some t0 => if Obligation.discharge (.subtype t0 t) then .ok t else .error (mismatch pos)
    | .lit pos v =>
        if Obligation.discharge (.subtype (ofAtom (atomOfVal v)) t) then .ok t else .error (mismatch pos)
    | .neg pos e1 =>
        match checkExp c G e1 with
        | .error m => .error m
        | .ok t1 =>
            if Obligation.discharge (.subtype t1 bool_) then
              (if Obligation.discharge (.subtype bool_ t) then .ok t else .error (mismatch pos))
            else .error "the operand of `!` must be a boolean"
    | .tyof pos e1 =>
        match checkExp c G e1 with
        | .error m => .error m
        | .ok t1 => if Obligation.discharge (.subtype (tagsOf t1) t) then .ok t else .error (mismatch pos)
    | .bin pos op l r =>
        match checkExp c G l with
        | .error m => .error m
        | .ok tl =>
          match op with
          | .eq =>
              match checkExp c G r with
              | .error m => .error m
              | .ok _ => if Obligation.discharge (.subtype bool_ t) then .ok t else .error (mismatch pos)
          | .ne =>
              match checkExp c G r with
              | .error m => .error m
              | .ok _ => if Obligation.discharge (.subtype bool_ t) then .ok t else .error (mismatch pos)
          | .and =>
              if Obligation.discharge (.subtype tl bool_) then
                match checkExp c (narrow G (eraseExp l) true) r with
                | .error m => .error m
                | .ok tr =>
                    if Obligation.discharge (.subtype tr bool_) then
                      (if Obligation.discharge (.subtype bool_ t) then .ok t else .error (mismatch pos))
                    else .error "the right operand of `&&` must be a boolean"
              else .error "the left operand of `&&` must be a boolean"
          | .or =>
              if Obligation.discharge (.subtype tl bool_) then
                match checkExp c (narrow G (eraseExp l) false) r with
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
            match checkArgs c G args fn.params with
            | .error m => .error m
            | .ok _ => if Obligation.discharge (.subtype fn.ret t) then .ok t else .error (mismatch pos)

def checkArgs (c : Ctx) (G : TEnv) : List Expr → List (String × Ty) → Except String Unit
  | [], [] => .ok ()
  | a :: as, (_, pt) :: ps =>
      match checkExp c G a with
      | .error m => .error m
      | .ok ta =>
          if Obligation.discharge (.subtype ta pt) then checkArgs c G as ps
          else .error "an argument is not within the declared parameter type"
  | _, _ => .error "wrong number of arguments"

end

/-! ### Expression checking is sound -/

mutual

theorem checkExp_sound (c : Ctx) (G : TEnv) (e : Expr) (t : Ty)
    (h : checkExp c G e = .ok t) : HasTy c.prog G (eraseExp e) t := by
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
            exact .not (HasTy_sub (checkExp_sound c G e1 t1 h1) hb) hs
          · exact absurd h (by simp)
        · exact absurd h (by simp)
    -- typeof
    · next pos e1 =>
      split at h
      · exact absurd h (by simp)
      · next t1 h1 =>
        split at h
        · next hs => cases h; exact .tyof (checkExp_sound c G e1 t1 h1) hs
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
              exact .eq (checkExp_sound c G l tl hl) (checkExp_sound c G r tr hr) hs
            · exact absurd h (by simp)
        -- !==
        · split at h
          · exact absurd h (by simp)
          · next tr hr =>
            split at h
            · next hs =>
              cases h
              exact .ne (checkExp_sound c G l tl hl) (checkExp_sound c G r tr hr) hs
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
                  exact .and (HasTy_sub (checkExp_sound c G l tl hl) hlb)
                    (HasTy_sub (checkExp_sound c _ r tr hr) hrb) hs
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
                  exact .or (HasTy_sub (checkExp_sound c G l tl hl) hlb)
                    (HasTy_sub (checkExp_sound c _ r tr hr) hrb) hs
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
          · next hs => cases h; exact .call hlk (checkArgs_sound c G args fn.params hca) hs
          · exact absurd h (by simp)

theorem checkArgs_sound (c : Ctx) (G : TEnv) (as : List Expr) (ps : List (String × Ty))
    (h : checkArgs c G as ps = .ok ()) : HasTyArgs c.prog G (eraseExps as) ps := by
  match as, ps with
  | [], [] => exact .nil
  | a :: as', (x, pt) :: ps' =>
    rw [checkArgs] at h
    split at h
    · exact absurd h (by simp)
    · next ta hta =>
      split at h
      · next hsub =>
        exact .cons (HasTy_sub (checkExp_sound c G a ta hta) hsub)
          (checkArgs_sound c G as' ps' h)
      · exact absurd h (by simp)
  | [], _ :: _ => exact absurd h (by simp [checkArgs])
  | _ :: _, [] => exact absurd h (by simp [checkArgs])

end

/-! ### Statement obligations

An `if` must have both edges leave the function, or (with no `else`) the
`then` edge must, which is the discipline of a calculus with no join points. That
also means the checker never walks a branch concatenated with what follows:
`BlockOk_append` discharges the `thn ++ rest` obligation from the branch
alone, so every recursive call here is on a sub-term. -/

def checkStmts (c : Ctx) (G : TEnv) (tr : Ty) (b : List Stmt) : Except String Unit :=
  match b with
  | [] => .error "the body must end in `return`"
  | s :: rest =>
      match claimEnv c.typeClaims s.start with
      | .error m => .error m
      | .ok claimed =>
        match envCovers s.start G claimed with
        | .error m => .error m
        | .ok _ =>
          match s with
          | .ret _ e =>
              match checkExp c G e with
              | .error m => .error m
              | .ok t =>
                  if Obligation.discharge (.subtype t tr) then
                    (if rest.isEmpty then .ok ()
                     else .error "unreachable statement after `return`")
                  else .error "the returned type is not within the declared return type"
          | .cst _ x annot init =>
              match checkExp c G init with
              | .error m => .error m
              | .ok t =>
                match annot with
                | none => checkStmts c (tenvSet G x t) tr rest
                | some a =>
                    if Obligation.discharge (.subtype t a) then checkStmts c (tenvSet G x a) tr rest
                    else .error s!"the initialiser of '{x}' is not within its annotation"
          | .ite _ cond thn els =>
              match checkExp c G cond with
              | .error m => .error m
              | .ok tc =>
                  if Obligation.discharge (.subtype tc bool_) then
                    match checkStmts c (narrow G (eraseExp cond) true) tr thn with
                    | .error m => .error s!"in the `then` branch (which must return, since the calculus has no join points): {m}"
                    | .ok _ =>
                      match els with
                      | some e =>
                          match checkStmts c (narrow G (eraseExp cond) false) tr e with
                          | .error m => .error s!"in the `else` branch (which must return, since the calculus has no join points): {m}"
                          | .ok _ =>
                              if rest.isEmpty then .ok ()
                              else .error "unreachable statement after an `if` that always returns"
                      | none => checkStmts c (narrow G (eraseExp cond) false) tr rest
                  else .error "an `if` condition must be a boolean"

theorem checkStmts_sound (c : Ctx) (G : TEnv) (tr : Ty) :
    ∀ (b : List Stmt), checkStmts c G tr b = .ok () → BlockOk c.prog G tr (eraseStms b)
  | [], h => absurd h (by simp [checkStmts])
  | s :: rest, h => by
    rw [checkStmts.eq_def] at h
    dsimp only at h
    cases s with
    | ret pos e =>
      dsimp only at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · rename_i t ht
            split at h
            · rename_i hsub
              split at h
              · show BlockOk c.prog G tr (.ret (eraseExp e) :: eraseStms rest)
                exact .ret (HasTy_sub (checkExp_sound c G e t ht) hsub)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
    | cst pos x annot init =>
      dsimp only at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · rename_i t ht
            cases annot with
            | none =>
              dsimp only at h
              show BlockOk c.prog G tr (.cst x none (eraseExp init) :: eraseStms rest)
              exact .cst (checkExp_sound c G init t ht)
                (checkStmts_sound c (tenvSet G x t) tr rest h)
            | some a =>
              dsimp only at h
              split at h
              · rename_i hsub
                show BlockOk c.prog G tr (.cst x (some a) (eraseExp init) :: eraseStms rest)
                exact .cst (HasTy_sub (checkExp_sound c G init t ht) hsub)
                  (checkStmts_sound c (tenvSet G x a) tr rest h)
              · exact absurd h (by simp)
    | ite pos cond thn els =>
      dsimp only at h
      split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · rename_i tc htc
            split at h
            · rename_i hb
              split at h
              · exact absurd h (by simp)
              · rename_i hthn
                show BlockOk c.prog G tr
                  (.ite (eraseExp cond) (eraseStms thn) (eraseEls els) :: eraseStms rest)
                refine .ite (HasTy_sub (checkExp_sound c G cond tc htc) hb)
                  (BlockOk_append (checkStmts_sound c _ tr thn hthn) _) ?_
                cases els with
                | some e =>
                  dsimp only at h
                  split at h
                  · exact absurd h (by simp)
                  · rename_i hels
                    split at h
                    · exact BlockOk_append (checkStmts_sound c _ tr e hels) _
                    · exact absurd h (by simp)
                | none =>
                  dsimp only at h
                  show BlockOk c.prog _ tr ([] ++ eraseStms rest)
                  rw [List.nil_append]
                  exact checkStmts_sound c _ tr rest h
            · exact absurd h (by simp)

/-! ### Input validation and verification entry points

Input validation requires the claimed signature to agree with the source.
The body uses the source signature regardless, so this consistency requirement
is additional to the obligations used by the program-soundness proof. -/

def checkFun (p : Core.Prog) (f : Fn) (fc : FunTypeClaims) : Except String Unit :=
  match claimsBind f fc with
  | .error m => .error m
  | .ok _ => checkStmts { prog := p, typeClaims := fc } (eraseFn f).params f.ret f.body

theorem checkFun_sound {p : Core.Prog} {f : Fn} {fc : FunTypeClaims} (h : checkFun p f fc = .ok ()) :
    Core.FnOk p (eraseFn f) := by
  rw [checkFun] at h
  split at h
  · exact absurd h (by simp)
  · exact checkStmts_sound { prog := p, typeClaims := fc } _ _ f.body h

def checkAll (p : Core.Prog) (typeClaims : List FunTypeClaims) (funs : List Fn) : Except String Unit :=
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
    ∀ (funs : List Fn), checkAll p typeClaims funs = .ok () → ∀ f ∈ funs, Core.FnOk p (eraseFn f)
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
  if funs.length == typeClaims.length then checkAll (eraseProg funs) typeClaims funs
  else .error s!"the claims cover {typeClaims.length} functions but the file declares {funs.length}"

/-- **Verifier soundness.** Accepted claims mean the erased program
satisfies the calculus. Nothing about spans, JSON or SKJS survives into the
conclusion. -/
theorem checkFile_sound {funs : List Fn} {typeClaims : List FunTypeClaims}
    (h : checkFile funs typeClaims = .ok ()) : ProgOk (eraseProg funs) := by
  intro fn hfn
  rw [checkFile] at h
  split at h
  · simp only [eraseProg, List.mem_map] at hfn
    obtain ⟨f, hf, rfl⟩ := hfn
    exact checkAll_sound _ _ _ h f hf
  · exact absurd h (by simp)

/-! ### What acceptance buys

Composing verifier soundness with calculus soundness: for a program whose claims were accepted,
calling any of its functions on arguments that inhabit its parameter types
cannot go wrong, and any value it returns inhabits the declared return type. -/

theorem accepted_never_stuck {funs : List Fn} {typeClaims : List FunTypeClaims}
    (h : checkFile funs typeClaims = .ok ()) {fn : Core.Fn} (hfn : fn ∈ eraseProg funs)
    {vs : List Val} (hma : MemAll vs fn.params) (n : Nat) :
    execB (eraseProg funs) n (bindParams fn.params vs) fn.body ≠ .stuck :=
  call_never_stuck (checkFile_sound h) hfn hma n

theorem accepted_returns_in_type {funs : List Fn} {typeClaims : List FunTypeClaims}
    (h : checkFile funs typeClaims = .ok ()) {fn : Core.Fn} (hfn : fn ∈ eraseProg funs)
    {vs : List Val} (hma : MemAll vs fn.params) (n : Nat) {v : Val}
    (hv : execB (eraseProg funs) n (bindParams fn.params vs) fn.body = .ok v) :
    mem v fn.ret :=
  call_returns_in_type (checkFile_sound h) hfn hma n hv

end Verification
