import Verification.Calculus.Typing

namespace Verification
namespace Core

/-! ## A type checker

A decision procedure for the rules above. `checkProg_sound` says acceptance
implies `ProgOk`; with `sound`, that is the guarantee an accepted program
carries. -/

mutual

def inferExp (p : Prog) (G : TEnv) (e : Exp) : Except String Ty :=
  match e with
  | .var x =>
      match tenvGet G x with
      | some t => .ok t
      | none => .error s!"unbound variable '{x}'"
  | .lit v => .ok (ofAtom (atomOfVal v))
  | .not e1 =>
      match inferExp p G e1 with
      | .error m => .error m
      | .ok t1 =>
          if sub t1 bool_ then .ok bool_
          else .error "the operand of `!` must be a boolean"
  | .eq l r =>
      match inferExp p G l with
      | .error m => .error m
      | .ok _ =>
        match inferExp p G r with
        | .error m => .error m
        | .ok _ => .ok bool_
  | .ne l r =>
      match inferExp p G l with
      | .error m => .error m
      | .ok _ =>
        match inferExp p G r with
        | .error m => .error m
        | .ok _ => .ok bool_
  | .tyof e1 =>
      match inferExp p G e1 with
      | .error m => .error m
      | .ok t1 => .ok (tagsOf t1)
  | .and l r =>
      match inferExp p G l with
      | .error m => .error m
      | .ok tl =>
          if sub tl bool_ then
            match inferExp p (narrow G l true) r with
            | .error m => .error m
            | .ok tr =>
                if sub tr bool_ then .ok bool_
                else .error "the right operand of `&&` must be a boolean"
          else .error "the left operand of `&&` must be a boolean"
  | .or l r =>
      match inferExp p G l with
      | .error m => .error m
      | .ok tl =>
          if sub tl bool_ then
            match inferExp p (narrow G l false) r with
            | .error m => .error m
            | .ok tr =>
                if sub tr bool_ then .ok bool_
                else .error "the right operand of `||` must be a boolean"
          else .error "the left operand of `||` must be a boolean"
  | .call f args =>
      match lookupFun p f with
      | none => .error s!"call to an unknown function '{f}'"
      | some fn =>
          match inferArgs p G args fn.params with
          | .error m => .error m
          | .ok _ => .ok fn.ret

def inferArgs (p : Prog) (G : TEnv) : List Exp → List (String × Ty) → Except String Unit
  | [], [] => .ok ()
  | a :: as, (_, pt) :: ps =>
      match inferExp p G a with
      | .error m => .error m
      | .ok ta =>
          if sub ta pt then inferArgs p G as ps
          else .error "an argument is not within the declared parameter type"
  | _, _ => .error "wrong number of arguments"

end

mutual

theorem inferExp_sound (p : Prog) (G : TEnv) (e : Exp) (t : Ty)
    (h : inferExp p G e = .ok t) : HasTy p G e t := by
  cases e with
  | var x =>
    rw [inferExp] at h
    split at h
    · rename_i t0 ht; cases h; exact .var ht (sub_refl _)
    · exact absurd h (by simp)
  | lit v =>
    rw [inferExp] at h
    cases h; exact .lit (sub_refl _)
  | not e1 =>
    rw [inferExp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i t1 ht1
      split at h
      · rename_i hb
        cases h
        exact .not (HasTy_sub (inferExp_sound p G e1 t1 ht1) hb) (sub_refl _)
      · exact absurd h (by simp)
  | eq l r =>
    rw [inferExp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tl htl
      split at h
      · exact absurd h (by simp)
      · rename_i tr htr
        cases h
        exact .eq (inferExp_sound p G l tl htl) (inferExp_sound p G r tr htr) (sub_refl _)
  | ne l r =>
    rw [inferExp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tl htl
      split at h
      · exact absurd h (by simp)
      · rename_i tr htr
        cases h
        exact .ne (inferExp_sound p G l tl htl) (inferExp_sound p G r tr htr) (sub_refl _)
  | tyof e1 =>
    rw [inferExp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i t1 ht1
      cases h
      exact .tyof (inferExp_sound p G e1 t1 ht1) (sub_refl _)
  | and l r =>
    rw [inferExp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tl htl
      split at h
      · rename_i hlb
        split at h
        · exact absurd h (by simp)
        · rename_i tr htr
          split at h
          · rename_i hrb
            cases h
            exact .and (HasTy_sub (inferExp_sound p G l tl htl) hlb)
              (HasTy_sub (inferExp_sound p (narrow G l true) r tr htr) hrb) (sub_refl _)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  | or l r =>
    rw [inferExp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i tl htl
      split at h
      · rename_i hlb
        split at h
        · exact absurd h (by simp)
        · rename_i tr htr
          split at h
          · rename_i hrb
            cases h
            exact .or (HasTy_sub (inferExp_sound p G l tl htl) hlb)
              (HasTy_sub (inferExp_sound p (narrow G l false) r tr htr) hrb) (sub_refl _)
          · exact absurd h (by simp)
      · exact absurd h (by simp)
  | call f args =>
    rw [inferExp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i fn hlk
      split at h
      · exact absurd h (by simp)
      · rename_i hia
        cases h
        exact .call hlk (inferArgs_sound p G args fn.params hia) (sub_refl _)

theorem inferArgs_sound (p : Prog) (G : TEnv) (as : List Exp) (ps : List (String × Ty))
    (h : inferArgs p G as ps = .ok ()) : HasTyArgs p G as ps := by
  match as, ps with
  | [], [] => exact .nil
  | a :: as', (x, pt) :: ps' =>
    rw [inferArgs] at h
    split at h
    · exact absurd h (by simp)
    · rename_i ta hta
      split at h
      · rename_i hsub
        exact .cons (HasTy_sub (inferExp_sound p G a ta hta) hsub)
          (inferArgs_sound p G as' ps' h)
      · exact absurd h (by simp)
  | [], _ :: _ => exact absurd h (by simp [inferArgs])
  | _ :: _, [] => exact absurd h (by simp [inferArgs])

end

/-- Both edges of an `if` must leave the function, so the rest of the block is
never reached from a branch and `BlockOk_append` discharges the concatenation
in `BlockOk.ite` from the branch alone. -/
def checkBlock (p : Prog) (G : TEnv) (tr : Ty) (b : List Stm) : Except String Unit :=
  match b with
  | [] => .error "the block must end in `return`"
  | .ret e :: _ =>
      match inferExp p G e with
      | .error m => .error m
      | .ok t =>
          if sub t tr then .ok ()
          else .error "the returned type is not within the declared return type"
  | .cst x annot init :: rest =>
      match inferExp p G init with
      | .error m => .error m
      | .ok t =>
        match annot with
        | none => checkBlock p (tenvSet G x t) tr rest
        | some a =>
            if sub t a then checkBlock p (tenvSet G x a) tr rest
            else .error s!"the initialiser of '{x}' is not within its annotation"
  | .ite c thn els :: rest =>
      match inferExp p G c with
      | .error m => .error m
      | .ok tc =>
          if sub tc bool_ then
            match checkBlock p (narrow G c true) tr thn with
            | .error m => .error s!"in the `then` branch, which must return: {m}"
            | .ok _ =>
              match els with
              | [] => checkBlock p (narrow G c false) tr rest
              | e :: es =>
                match checkBlock p (narrow G c false) tr (e :: es) with
                | .error m => .error s!"in the `else` branch, which must return: {m}"
                | .ok _ => .ok ()
          else .error "an `if` condition must be a boolean"

theorem checkBlock_sound (p : Prog) (G : TEnv) (tr : Ty) :
    ∀ (b : List Stm), checkBlock p G tr b = .ok () → BlockOk p G tr b
  | [], h => absurd h (by simp [checkBlock])
  | s :: rest, h => by
    rw [checkBlock.eq_def] at h
    cases s with
    | ret e =>
      dsimp only at h
      split at h
      · exact absurd h (by simp)
      · rename_i t ht
        split at h
        · rename_i hsub
          exact .ret (HasTy_sub (inferExp_sound p G e t ht) hsub)
        · exact absurd h (by simp)
    | cst x annot init =>
      dsimp only at h
      split at h
      · exact absurd h (by simp)
      · rename_i t ht
        cases annot with
        | none =>
          dsimp only at h
          exact .cst (inferExp_sound p G init t ht)
            (checkBlock_sound p (tenvSet G x t) tr rest h)
        | some a =>
          dsimp only at h
          split at h
          · rename_i hsub
            exact .cst (HasTy_sub (inferExp_sound p G init t ht) hsub)
              (checkBlock_sound p (tenvSet G x a) tr rest h)
          · exact absurd h (by simp)
    | ite c thn els =>
      dsimp only at h
      split at h
      · exact absurd h (by simp)
      · rename_i tc htc
        split at h
        · rename_i hb
          split at h
          · exact absurd h (by simp)
          · rename_i hthn
            refine .ite (HasTy_sub (inferExp_sound p G c tc htc) hb)
              (BlockOk_append (checkBlock_sound p _ tr thn hthn) _) ?_
            cases els with
            | nil =>
              dsimp only at h
              rw [List.nil_append]
              exact checkBlock_sound p _ tr rest h
            | cons e es =>
              dsimp only at h
              split at h
              · exact absurd h (by simp)
              · rename_i hels
                exact BlockOk_append (checkBlock_sound p _ tr (e :: es) hels) _
        · exact absurd h (by simp)

def checkFns (p : Prog) (fs : List Fn) : Except String Unit :=
  match fs with
  | [] => .ok ()
  | fn :: rest =>
      match checkBlock p fn.params fn.ret fn.body with
      | .error m => .error s!"{fn.name}: {m}"
      | .ok _ => checkFns p rest

theorem checkFns_sound (p : Prog) :
    ∀ (fs : List Fn), checkFns p fs = .ok () → ∀ fn ∈ fs, FnOk p fn
  | [], _, _, hf => absurd hf (by simp)
  | g :: rest, h, fn, hf => by
    rw [checkFns.eq_def] at h
    dsimp only at h
    split at h
    · exact absurd h (by simp)
    · rename_i hg
      rcases List.mem_cons.mp hf with rfl | hrest
      · exact checkBlock_sound p _ _ _ hg
      · exact checkFns_sound p rest h fn hrest

def checkProg (p : Prog) : Except String Unit := checkFns p p

theorem checkProg_sound {p : Prog} (h : checkProg p = .ok ()) : ProgOk p :=
  checkFns_sound p p h

/-- What an accepted program guarantees: calling any of its functions on
arguments that inhabit its parameter types cannot go wrong, and any value the
call produces inhabits the declared return type. -/
theorem checked_never_stuck {p : Prog} (h : checkProg p = .ok ())
    {fn : Fn} (hfn : fn ∈ p) {vs : List Val} (hma : MemAll vs fn.params) (n : Nat) :
    execB p n (bindParams fn.params vs) fn.body ≠ .stuck :=
  call_never_stuck (checkProg_sound h) hfn hma n

theorem checked_returns_in_type {p : Prog} (h : checkProg p = .ok ())
    {fn : Fn} (hfn : fn ∈ p) {vs : List Val} (hma : MemAll vs fn.params) (n : Nat)
    {v : Val} (hv : execB p n (bindParams fn.params vs) fn.body = .ok v) :
    mem v fn.ret :=
  call_returns_in_type (checkProg_sound h) hfn hma n hv

end Core
end Verification
