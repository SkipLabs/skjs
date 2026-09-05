/-
The AST for the supported TypeScript source fragment, including source locations.
Lowering.lean translates this representation into programs in the core calculus
whose syntax and execution are defined in Calculus/Programs.lean.
JSON decoding lives in JsonDecode.lean.
-/
import Verification.Calculus.Types

namespace Verification

open Core

abbrev Span := Nat × Nat

/-- The binary operators of the supported fragment. An operator outside this
list is rejected while decoding, so the syntax tree cannot represent a program
outside the calculus. -/
inductive BinOp where
  | eq | ne | and | or
  deriving Repr, DecidableEq

inductive Expr where
  | var (pos : Span) (name : String)
  | lit (pos : Span) (v : Val)
  | bin (pos : Span) (op : BinOp) (l r : Expr)
  | neg (pos : Span) (e : Expr)
  | tyof (pos : Span) (e : Expr)
  | call (pos : Span) (callee : String) (args : List Expr)
  deriving Repr

def Expr.span : Expr → Span
  | .var p _ | .lit p _ | .bin p _ _ _ | .neg p _ | .tyof p _ | .call p _ _ => p

inductive Stmt where
  | ret (pos : Span) (e : Expr)
  | cst (pos : Span) (name : String) (annot : Option Ty) (init : Expr)
  | ite (pos : Span) (cond : Expr) (thn : List Stmt) (els : Option (List Stmt))
  deriving Repr

def Stmt.start : Stmt → Nat
  | .ret p _ | .cst p _ _ _ | .ite p _ _ _ => p.1

structure Param where
  name : String
  ty : Ty
  deriving Repr

structure Fn where
  name : String
  namePos : Span
  params : List Param
  ret : Ty
  body : List Stmt
  deriving Repr

end Verification
