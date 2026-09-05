/-
Translation from the TypeScript source AST (SourceAst.lean) into the core
calculus (Calculus/Programs.lean). Start at eraseProg for a whole program,
eraseFn for a function, eraseStm for a statement, or eraseExp for an expression.

The erase* names reflect the current translation: it removes source locations
and normalizes source forms, such as an absent else branch. As TypeScript
support grows, more source forms may lower to existing calculus constructs.
This mapping must preserve source behavior; the verifier's theorem describes
the translated core program, not a separate TypeScript execution semantics.
-/
import Verification.SourceAst
import Verification.Calculus.Programs

namespace Verification

open Core hiding Fn

/-! ## Translation to calculus syntax -/

mutual

def eraseExp : Expr → Core.Exp
  | .var _ x => .var x
  | .lit _ v => .lit v
  | .bin _ .eq l r => .eq (eraseExp l) (eraseExp r)
  | .bin _ .ne l r => .ne (eraseExp l) (eraseExp r)
  | .bin _ .and l r => .and (eraseExp l) (eraseExp r)
  | .bin _ .or l r => .or (eraseExp l) (eraseExp r)
  | .neg _ e => .not (eraseExp e)
  | .tyof _ e => .tyof (eraseExp e)
  | .call _ f args => .call f (eraseExps args)

def eraseExps : List Expr → List Core.Exp
  | [] => []
  | a :: as => eraseExp a :: eraseExps as

end

/-- The statements of an `else` branch that is absent. -/
def elseBody : Option (List Stmt) → List Stmt
  | none => []
  | some b => b

mutual

def eraseStm : Stmt → Core.Stm
  | .ret _ e => .ret (eraseExp e)
  | .cst _ x annot init => .cst x annot (eraseExp init)
  | .ite _ c thn els => .ite (eraseExp c) (eraseStms thn) (eraseEls els)

def eraseStms : List Stmt → List Core.Stm
  | [] => []
  | s :: rest => eraseStm s :: eraseStms rest

def eraseEls : Option (List Stmt) → List Core.Stm
  | none => []
  | some b => eraseStms b

end

def eraseFn (f : Fn) : Core.Fn :=
  { name := f.name
    params := f.params.map (fun p => (p.name, p.ty))
    ret := f.ret
    body := eraseStms f.body }

def eraseProg (fs : List Fn) : Core.Prog := fs.map eraseFn

end Verification
