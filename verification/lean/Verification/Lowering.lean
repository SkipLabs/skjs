/-
Translation from the TypeScript source AST (SourceAst.lean) into the core
calculus's control-flow graphs (Calculus/Programs.lean).

Two things this must preserve, and the second is easy to get wrong:

**Control flow.** A block is lowered right to left, so each statement's node
already knows the label of its continuation. An `if` lowers to a `branch`
whose two arms both continue to the *same* label -- the entry of whatever
followed the `if`. That label is a genuine join: two predecessors, no
duplicated continuation. When nothing follows, the continuation is `none`,
which `run` reports as stuck and no edge check can justify, so a function
still may not fall off the end.

**Lexical binding.** Core slots are not source names. Each `const` allocates a
fresh slot, and `Scope` maps source names to the slots in scope at each point.
Without this, connecting a branch to its continuation would let a binding
declared inside the branch escape:

    const x = "outer";
    if (b) { const x = "inner"; }
    return x;          -- must read the outer slot

Both `x`s here have type `string`, so no edge check would notice. Renaming is
what makes the continuation read `x@0` rather than whatever the branch bound
last.

Each node records the source offset and scope it came from, so the verifier
can key a name-based claim to the node and translate it into slots. The claim
JSON is unchanged.
-/
import Verification.SourceAst
import Verification.Calculus.Programs

namespace Verification

open Core hiding Fn

/-- Source name to core slot, innermost first. -/
abbrev Scope := List (String × String)

def slotOf (σ : Scope) (x : String) : String :=
  match σ.find? (fun p => p.1 == x) with
  | some (_, s) => s
  | none => x

/-! ## Expressions

Structure is preserved exactly; only variable references are resolved. -/

mutual

def eraseExp (σ : Scope) : Expr → Core.Exp
  | .var _ x => .var (slotOf σ x)
  | .lit _ v => .lit v
  | .bin _ .eq l r => .eq (eraseExp σ l) (eraseExp σ r)
  | .bin _ .ne l r => .ne (eraseExp σ l) (eraseExp σ r)
  | .bin _ .and l r => .and (eraseExp σ l) (eraseExp σ r)
  | .bin _ .or l r => .or (eraseExp σ l) (eraseExp σ r)
  | .neg _ e => .not (eraseExp σ e)
  | .tyof _ e => .tyof (eraseExp σ e)
  | .call _ f args => .call f (eraseExps σ args)

def eraseExps (σ : Scope) : List Expr → List Core.Exp
  | [] => []
  | a :: as => eraseExp σ a :: eraseExps σ as

end

/-! ## Graph construction -/

/-- What the verifier needs about the node at each label: the source offset
whose claim supplies its entry environment, the scope that claim is read in,
and the source expression the node evaluates.

The node itself is *derived* from these rather than stored beside them, so a
node and the source it is checked against cannot drift apart. -/
inductive NodeKind where
  | ret
  | set (slot : String) (next : Option Nat)
  | branch (yes no : Option Nat)
  deriving Repr

/-- A binding that is in scope at a node but shadowed there, so no claim
names it. Its type comes from the claim at `from_` under the source name it
had before the shadowing block -- or from the signature, when `from_` is
`none` and the shadowed binding is a parameter.

Reading it from there is exact: bindings are immutable, so a shadowed slot's
type cannot change while it is shadowed. Without this the type would simply
be lost, and an edge leaving the block could not re-establish the binding its
target still needs. -/
structure Hidden where
  slot : String
  from_ : Nat
  as : String
  deriving Repr

structure NodeInfo where
  kind : NodeKind
  offset : Nat
  /-- How a source name in `src` resolves to a slot. Block-scoped: a
  declaration binds throughout its block, including before its own statement,
  where the slot is not yet set and a read is therefore an error. -/
  resolve : Scope
  /-- How a source name in the *claim* at `offset` resolves. Declaration-scoped,
  which is what SKJS records: a name refers to the outer binding until the
  inner declaration is reached. These differ exactly in the window where a
  binding is shadowed but not yet initialized. -/
  visible : Scope
  /-- Slots in scope here that the claim at `offset` cannot name. -/
  hidden : List Hidden
  src : Expr
  /-- The source annotation on a `const`, if it had one. The core has no place
  for it -- `Node.set` binds whatever the initialiser has -- but it is still a
  requirement the source makes, so the verifier checks it here. -/
  annot : Option Ty := none
  deriving Repr

def NodeInfo.toNode (i : NodeInfo) : Core.Node :=
  match i.kind with
  | .ret => .ret (eraseExp i.resolve i.src)
  | .set slot next => .set slot (eraseExp i.resolve i.src) next
  | .branch yes no => .branch (eraseExp i.resolve i.src) yes no

/-- Nodes emitted so far, in label order, plus the next fresh slot number. -/
structure LState where
  nodes : Array NodeInfo
  fresh : Nat

def LState.empty : LState := { nodes := #[], fresh := 0 }

/-- Append a node; its label is its index. -/
def emit (st : LState) (i : NodeInfo) : Nat × LState :=
  (st.nodes.size, { st with nodes := st.nodes.push i })

def freshSlot (st : LState) (x : String) : String × LState :=
  (x ++ "@" ++ toString st.fresh, { st with fresh := st.fresh + 1 })

/-! ### Block scope

A declaration binds throughout its block, not from its own statement onward.
So the slots for a block are allocated before any of its statements is
lowered, and a read that precedes the declaration resolves to the *new* slot:

```ts
const x = "outer";
if (b) {
  return x;            // the inner x, which has no value yet
  const x = "inner";
}
```

Nothing writes that slot before the read, so no environment can supply it and
the edge check rejects the program -- and were it run, `venvGet` would find
nothing and `run` would report `stuck`. JavaScript throws `ReferenceError`
there, and TypeScript rejects it too. Resolving the declaration only from its
own statement onward would instead have silently read the outer binding. -/

def declNames : List Stmt → List String
  | [] => []
  | .cst _ x _ _ :: rest => x :: declNames rest
  | _ :: rest => declNames rest

/-- Allocate a slot for each name a block declares, before lowering it. -/
def hoist : Scope → LState → List String → Scope × LState
  | σ, st, [] => (σ, st)
  | σ, st, x :: xs =>
      let (slot, st) := freshSlot st x
      hoist ((x, slot) :: σ) st xs

/-! ### Reachability

A statement after one that always leaves the block is not lowered: it cannot
run, so it is not part of the program the theorem is about, and giving it a
node would saddle it with the obligations of reachable code -- a `const` after
a `return` would be required to have somewhere to continue to. Its
declaration is still hoisted, because it still shadows. -/

mutual

def stmtLeaves : Stmt → Bool
  | .ret _ _ => true
  | .cst _ _ _ _ => false
  | .ite _ _ thn els =>
      blockLeaves thn && (match els with | none => false | some e => blockLeaves e)

def blockLeaves : List Stmt → Bool
  | [] => false
  | s :: rest => stmtLeaves s || blockLeaves rest

end

/-! ### Lowering

Right to left, so every successor label already exists when the node naming it
is emitted. -/

mutual

/-- Lower a block: allocate slots for everything it declares, then lower its
statements so that falling out continues at `k`. `resolve` is extended for the
whole block; `visible` and `hidden` change only as declarations are reached. -/
def lowerBlock (resolve visible : Scope) (h : List Hidden) (k : Option Nat)
    (st : LState) (b : List Stmt) : Option Nat × LState :=
  let (resolve, st) := hoist resolve st (declNames b)
  lowerStmts resolve visible h k st b
termination_by (sizeOf b, 1)

def lowerStmts (resolve visible : Scope) (h : List Hidden) (k : Option Nat) (st : LState) :
    List Stmt → Option Nat × LState
  | [] => (k, st)
  | s :: rest => lowerStmt resolve visible h k st s rest
termination_by b => (sizeOf b, 0)

def lowerStmt (resolve visible : Scope) (h : List Hidden) (k : Option Nat) (st : LState)
    (s : Stmt) (rest : List Stmt) : Option Nat × LState :=
  match s with
  | .ret pos e =>
      -- Nothing after a `return` is lowered: it cannot run, so it is not part
      -- of the program, and giving it a node would burden it with the
      -- obligations of reachable code. Its declaration is still hoisted above,
      -- because it still shadows.
      let (lbl, st) := emit st { kind := .ret, offset := pos.1, resolve := resolve,
                                 visible := visible, hidden := h, src := e }
      (some lbl, st)
  | .cst pos x annot init =>
      let slot := slotOf resolve x
      -- From here on the name means the new slot, and the one it shadowed --
      -- still live, still readable through no name -- carries its type from
      -- the claim at this statement, where it was last visible.
      let h' := match visible.find? (fun q => q.1 == x) with
        | some (_, old) => h ++ [{ slot := old, from_ := pos.1, as := x }]
        | none => h
      let (kRest, st) := lowerStmts resolve ((x, slot) :: visible) h' k st rest
      let (lbl, st) := emit st { kind := .set slot kRest, offset := pos.1,
                                 resolve := resolve, visible := visible, hidden := h,
                                 src := init, annot := annot }
      (some lbl, st)
  | .ite pos c thn els =>
      -- Nothing after an `if` both of whose arms leave the block is lowered.
      let leaves := blockLeaves thn && (match els with | none => false | some e => blockLeaves e)
      let (kRest, st) := if leaves then (none, st) else lowerStmts resolve visible h k st rest
      -- Both arms are their own blocks, entered in the enclosing scope, so a
      -- binding either introduces cannot reach `kRest`.
      let (kThen, st) := lowerBlock resolve visible h kRest st thn
      let (kEls, st) := match els with
        | none => (kRest, st)
        | some e => lowerBlock resolve visible h kRest st e
      let (lbl, st) := emit st { kind := .branch kThen kEls, offset := pos.1,
                                 resolve := resolve, visible := visible, hidden := h,
                                 src := c }
      (some lbl, st)
termination_by (sizeOf s + sizeOf rest, 0)

end

def paramScope (ps : List Param) : Scope := ps.map (fun p => (p.name, p.name))

structure Lowered where
  fn : Core.Fn
  infos : List NodeInfo
  deriving Repr

def lowerFn (f : Fn) : Lowered :=
  let σ := paramScope f.params
  let (entry, st) := lowerBlock σ σ [] none LState.empty f.body
  -- Entry must be label 0 for `FnOk.entry`; lowering right to left puts the
  -- first statement last, so reverse and renumber. `fixup` rewrites every
  -- successor label under the same reversal.
  let n := st.nodes.size
  let flip : Option Nat → Option Nat := fun o => o.map (fun l => n - 1 - l)
  let infos := (st.nodes.toList.reverse).map (fun i =>
    { i with kind :=
        match i.kind with
        | .ret => .ret
        | .set x next => .set x (flip next)
        | .branch yes no => .branch (flip yes) (flip no) })
  let _ := entry
  { fn := { name := f.name
            params := f.params.map (fun p => (p.name, p.ty))
            ret := f.ret
            code := infos.map NodeInfo.toNode }
    infos := infos }

/-- The graph and the per-node information are built together, so a node and
the source it will be checked against are always the same index. -/
theorem lowerFn_code (f : Fn) :
    (lowerFn f).fn.code = (lowerFn f).infos.map NodeInfo.toNode := rfl

def lowerProg (fs : List Fn) : Core.Prog := fs.map (fun f => (lowerFn f).fn)

end Verification
