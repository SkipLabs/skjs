import Verification.Calculus.Types

/-!
The core calculus's program language: its syntax and execution semantics.
This is distinct from the TypeScript source AST in Verification/SourceAst.lean,
which Verification/Lowering.lean translates into these core programs.
-/

namespace Verification
namespace Core

/-! ## Program syntax -/

inductive Exp where
  | var (x : String)
  | lit (v : Val)
  | not (e : Exp)
  | eq (l r : Exp)
  | ne (l r : Exp)
  | tyof (e : Exp)
  | and (l r : Exp)
  | or (l r : Exp)
  | call (f : String) (args : List Exp)
  deriving Repr

inductive Stm where
  | ret (e : Exp)
  | cst (x : String) (annot : Option Ty) (init : Exp)
  | ite (c : Exp) (thn els : List Stm)
  deriving Repr

structure Fn where
  name : String
  params : List (String × Ty)
  ret : Ty
  body : List Stm

abbrev Prog := List Fn

def lookupFun (p : Prog) (f : String) : Option Fn := p.find? (fun g => g.name == f)

/-! ## Environments

`const` is the only binding form, so a new binding shadows rather than
updates, and lookup takes the first match. -/

abbrev VEnv := List (String × Val)

def venvGet : VEnv → String → Option Val
  | [], _ => none
  | (y, v) :: rest, x => if y == x then some v else venvGet rest x

def venvSet (ρ : VEnv) (x : String) (v : Val) : VEnv := (x, v) :: ρ

def bindParams : List (String × Ty) → List Val → VEnv
  | (x, _) :: ps, v :: vs => (x, v) :: bindParams ps vs
  | _, _ => []

/-! ## Primitive observations

Numbers use double bit patterns. The model treats NaN as truthy and compares
values by their representation; this differs from JavaScript for NaN inputs.
The soundness theorem is about these definitions. -/

def zeroBits : UInt64 := (0.0 : Float).toBits

/-- The tag of a value: what `typeof` yields for it. -/
def typeofVal : Val → String
  | .vnull => "object"
  | .vundef => "undefined"
  | .vnum _ => "number"
  | .vstr _ => "string"
  | .vbool _ => "boolean"

/-- Which values count as true in a condition. -/
def truthy : Val → Bool
  | .vnull => false
  | .vundef => false
  | .vnum b => b != zeroBits
  | .vstr s => s != ""
  | .vbool b => b

/-! ## Evaluation

Fuel bounds the recursion, so these are ordinary total functions. `timeout`
is "ran out of fuel", `stuck` is "went wrong". Soundness will say that a
well-typed program never reports `stuck`, and that any value it does report
inhabits its type; `timeout` is the escape hatch that lets a non-terminating
program have no value without the semantics being partial. -/

inductive Res (α : Type) where
  | ok (v : α)
  | stuck
  | timeout
  deriving Repr

mutual

def evalE (p : Prog) (n : Nat) (ρ : VEnv) (e : Exp) : Res Val :=
  match n with
  | 0 => .timeout
  | n + 1 =>
    match e with
    | .var x =>
        match venvGet ρ x with
        | some v => .ok v
        | none => .stuck
    | .lit v => .ok v
    | .not e =>
        match evalE p n ρ e with
        | .ok (.vbool b) => .ok (.vbool (!b))
        | .ok _ => .stuck
        | .stuck => .stuck
        | .timeout => .timeout
    -- `===` is equality of values.
    | .eq l r =>
        match evalE p n ρ l with
        | .ok u =>
            match evalE p n ρ r with
            | .ok w => .ok (.vbool (u == w))
            | .stuck => .stuck
            | .timeout => .timeout
        | .stuck => .stuck
        | .timeout => .timeout
    | .ne l r =>
        match evalE p n ρ l with
        | .ok u =>
            match evalE p n ρ r with
            | .ok w => .ok (.vbool (!(u == w)))
            | .stuck => .stuck
            | .timeout => .timeout
        | .stuck => .stuck
        | .timeout => .timeout
    | .tyof e =>
        match evalE p n ρ e with
        | .ok u => .ok (.vstr (typeofVal u))
        | .stuck => .stuck
        | .timeout => .timeout
    -- Boolean operands, and the right one is evaluated only on the edge
    -- where the left does not already decide the answer.
    | .and l r =>
        match evalE p n ρ l with
        | .ok (.vbool false) => .ok (.vbool false)
        | .ok (.vbool true) =>
            match evalE p n ρ r with
            | .ok (.vbool b) => .ok (.vbool b)
            | .ok _ => .stuck
            | .stuck => .stuck
            | .timeout => .timeout
        | .ok _ => .stuck
        | .stuck => .stuck
        | .timeout => .timeout
    | .or l r =>
        match evalE p n ρ l with
        | .ok (.vbool true) => .ok (.vbool true)
        | .ok (.vbool false) =>
            match evalE p n ρ r with
            | .ok (.vbool b) => .ok (.vbool b)
            | .ok _ => .stuck
            | .stuck => .stuck
            | .timeout => .timeout
        | .ok _ => .stuck
        | .stuck => .stuck
        | .timeout => .timeout
    | .call f args =>
        match lookupFun p f with
        | none => .stuck
        | some fn =>
            match evalArgs p n ρ args with
            | .ok vs =>
                if vs.length == fn.params.length then
                  execB p n (bindParams fn.params vs) fn.body
                else .stuck
            | .stuck => .stuck
            | .timeout => .timeout

def evalArgs (p : Prog) (n : Nat) (ρ : VEnv) (as : List Exp) : Res (List Val) :=
  match n with
  | 0 => .timeout
  | n + 1 =>
    match as with
    | [] => .ok []
    | a :: as =>
        match evalE p n ρ a with
        | .ok v =>
            match evalArgs p n ρ as with
            | .ok vs => .ok (v :: vs)
            | .stuck => .stuck
            | .timeout => .timeout
        | .stuck => .stuck
        | .timeout => .timeout

/-- Running a block yields the value it returns. Falling off the end without
returning is `stuck`: every path must return, and this is where that
obligation lives. An `if` runs its branch followed by whatever came after,
so a branch that returns simply never reaches the rest. -/
def execB (p : Prog) (n : Nat) (ρ : VEnv) (b : List Stm) : Res Val :=
  match n with
  | 0 => .timeout
  | n + 1 =>
    match b with
    | [] => .stuck
    | .ret e :: _ => evalE p n ρ e
    | .cst x _ init :: rest =>
        match evalE p n ρ init with
        | .ok v => execB p n (venvSet ρ x v) rest
        | .stuck => .stuck
        | .timeout => .timeout
    | .ite c thn els :: rest =>
        match evalE p n ρ c with
        | .ok (.vbool true) => execB p n ρ (thn ++ rest)
        | .ok (.vbool false) => execB p n ρ (els ++ rest)
        | .ok _ => .stuck
        | .stuck => .stuck
        | .timeout => .timeout

end

end Core
end Verification
