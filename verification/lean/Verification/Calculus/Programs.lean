import Verification.Calculus.Types

/-!
The core calculus's program language: its syntax and execution semantics.
This is distinct from the TypeScript source AST in Verification/SourceAst.lean,
which Verification/Lowering.lean translates into these core programs.

A function body is a **control-flow graph**: a list of nodes, indexed by
position, each naming its successors. Joins are ordinary edges, and so are
the loop heads and back edges a later fragment will add.  Nothing here reads
a claim; execution is defined independently of what anyone says about the
program.

There is one evaluator. The block representation this replaced is gone rather
than retained for comparison: it could not describe a branch that falls
through, so it was never a specification for the programs the graph exists to
accept. What keeps `Lowering` honest is `Tests/Lowering.lean`, which pins the
control flow and the slot resolution directly.
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

/-- One node of a function's control-flow graph. Successors are `Option Nat`:
`none` is control leaving the graph without returning, which `run` reports as
`stuck` and which no edge check can justify. That is where "a function may not
fall off the end" now lives -- stated once, rather than once per branch. -/
inductive Node where
  | ret (e : Exp)
  | set (x : String) (e : Exp) (next : Option Nat)
  | branch (c : Exp) (yes no : Option Nat)
  deriving Repr

structure Fn where
  name : String
  params : List (String × Ty)
  ret : Ty
  code : List Node
  deriving Repr

abbrev Prog := List Fn

def lookupFun (p : Prog) (f : String) : Option Fn := p.find? (fun g => g.name == f)

/-! ## Environments

Every binding is a distinct slot -- lowering resolves source shadowing to
fresh names -- so a write prepends and lookup takes the first match. -/

abbrev VEnv := List (String × Val)

def venvGet : VEnv → String → Option Val
  | [], _ => none
  | (y, v) :: rest, x => if y == x then some v else venvGet rest x

def venvSet (ρ : VEnv) (x : String) (v : Val) : VEnv := (x, v) :: ρ

def bindParams : List (String × Ty) → List Val → VEnv
  | (x, _) :: ps, v :: vs => (x, v) :: bindParams ps vs
  | _, _ => []

/-! ## Primitive observations

Numbers use double bit patterns. The model compares values by their
representation, which differs from JavaScript for NaN. The soundness theorem
is about these definitions. -/

def zeroBits : UInt64 := (0.0 : Float).toBits

/-- The tag of a value: what `typeof` yields for it. -/
def typeofVal : Val → String
  | .vnull => "object"
  | .vundef => "undefined"
  | .vnum _ => "number"
  | .vstr _ => "string"
  | .vbool _ => "boolean"

/-- Which values count as true in a condition. Conditions in this fragment
must already be booleans, so nothing below depends on the other cases. -/
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
program have no value without the semantics being partial.

Fuel is a depth bound, and each graph step spends one unit, so it also bounds
path length: a longer path needs more fuel. The theorem quantifies over every
fuel, so nothing rests on a particular bound. -/

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
                  run p n fn 0 (bindParams fn.params vs)
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

/-- Run `f` from node `pc`. A missing node, or a successor that leaves the
graph, is `stuck`: control may not fall out of a function without returning. -/
def run (p : Prog) (n : Nat) (f : Fn) (pc : Nat) (ρ : VEnv) : Res Val :=
  match n with
  | 0 => .timeout
  | n + 1 =>
    match f.code[pc]? with
    | none => .stuck
    | some (.ret e) => evalE p n ρ e
    | some (.set x e next) =>
        match evalE p n ρ e with
        | .ok v =>
            match next with
            | some k => run p n f k (venvSet ρ x v)
            | none => .stuck
        | .stuck => .stuck
        | .timeout => .timeout
    | some (.branch c yes no) =>
        match evalE p n ρ c with
        | .ok (.vbool b) =>
            match (if b then yes else no) with
            | some k => run p n f k ρ
            | none => .stuck
        | .ok _ => .stuck
        | .stuck => .stuck
        | .timeout => .timeout

end

end Core
end Verification
