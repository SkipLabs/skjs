import Verification.Model.Types.EquationFamilies

/-! Family subtyping on recursive equations: the examples and required
controls of RECURSIVE-EQUATIONS §4, as concrete checks. `Promise` is
covariant by the variance the checker computes, and a use relates two of its
applications by `Var` without unfolding `Promise`. What a pipeline case
cannot show is kept here: premises no source reaches alone, and the
controls of the variance computation's steps. -/
namespace Verification.Model.EquationFamilyTests
open PositiveNormalization PositiveGraphs PositiveRules PositiveCertificates EquationGraphs
  CallEffects

/-! ### Building equations

Rows are written as raw trees and validated when the equations are built;
`build` refuses a row it would have to change. -/

inductive Raw where
  | clauses (cs : List (Clause (List Tree)))
  /-- A scheme binding all its head's locals, without bounds. -/
  | scheme (sigs : List (Arrow (List Tree)))

def exprs (sig : Signature) (h : Header) (ts : List Tree) : List (Expression sig h) :=
  ts.filterMap fun t =>
    if hv : t.scoped sig h.parameters h.binders.length = true ∧ t.lexical true = true then
      some ⟨t, hv⟩ else none

def localRef (sig : Signature) (h : Header) (i : Fin h.binders.length) : Reference sig h :=
  ⟨⟨.local i.val, by simp [Tree.scoped, Tree.lexical, i.isLt]⟩, rfl⟩

def row (sig : Signature) (head : Fin sig.length) : Raw → RowTemplate sig head
  | .clauses cs => .clauses (cs.map (Clause.map (exprs sig sig[head])))
  | .scheme sigs => .scheme ((List.finRange sig[head].binders.length).map (localRef sig sig[head]))
      (sigs.map (Arrow.map (exprs sig sig[head]))) [] []

def erase {sig : Signature} {head : Fin sig.length} (r : RowTemplate sig head) :
    GraphRow Tree (List Tree) :=
  r.map (fun ref => ref.1.1) (fun es => es.map (·.1))

def rawRow (h : Header) : Raw → GraphRow Tree (List Tree)
  | .clauses cs => .clauses cs
  | .scheme sigs => .scheme ((List.range h.binders.length).map Tree.local) sigs [] []

def build (sig : Signature) (rows : List Raw) : Option Equations :=
  if hlen : rows.length = sig.length then
    let body := fun (head : Fin sig.length) => row sig head (rows[head.val]'(by omega))
    if hall : (List.finRange sig.length).all (fun head => (body head).wellBound head) = true then
      if (List.finRange sig.length).all (fun head =>
          erase (body head) == rawRow sig[head] (rows[head.val]'(by omega))) then
        some { signature := sig, body := fun head =>
          ⟨body head, List.all_eq_true.mp hall head (List.mem_finRange head)⟩ }
      else none
    else none
  else none

def app (h : Nat) (args : List (List Tree)) : Tree := .app h (Args.ofList (args.map Types.ofList))
def arg (i : Nat) : Tree := .argument i
def loc (i : Nat) : Tree := .local i
def fv (o s : Nat) : Tree := .var o s .value

def plain (params : Nat) : Header := ⟨params, [], List.replicate params .value⟩
def generic (params : Nat) : Header := ⟨params, [⟨"R", .value⟩], List.replicate params .value⟩

/-- Heads: 0 `number`, 1 `string`, 2 `unknown`, 3 `(x: A) => R`,
4 `then<R>(f: (x: T) => R): Promise<R>`, 5 `catch<R>(f: (e: unknown) => R): Promise<T | R>`,
6 `Promise<T>` with views `then` and `catch`, 7 `PromiseLike<T>` with `then`,
8 `Cell<T>` with a writable field, 9 `Box<T>` with a readonly view,
10 `{p: Promise<number>}`, 11 `{p: PromiseLike<number | string>}`,
12 `<R>() => R`, 13 `<S>() => T`, 14 `{q: number}`, 15 `{q: number | string}`,
16 `{p: Promise<14>}`, 17 `{p: Promise<15>}`, 18 `{p: Promise<number | string>}`,
19 `{p: Promise<number>}`, 20 `<R>() => R` again, 21 `ReadonlyArray<T>`,
22 `readonly [A, B]`, 23 `InputDefinition<K, V>` with the view
`initial: ReadonlyArray<readonly [K, V]>`. -/
def signature : Signature :=
  [plain 0, plain 0, plain 0, plain 2, generic 1, generic 1, plain 1,
   plain 1, plain 1, plain 1, plain 0, plain 0, generic 0, generic 1,
   plain 0, plain 0, plain 0, plain 0, plain 0, plain 0, generic 0, plain 1, plain 2,
   plain 2]

def num : Tree := app 0 []
def str : Tree := app 1 []
def unk : Tree := app 2 []

def rows : List Raw :=
  [.clauses [.num], .clauses [.str], .clauses [.top],
   .clauses [.arrs [⟨[unk], [[arg 0]], [arg 1], .unrestricted⟩] []],
   .scheme [⟨[unk], [[app 3 [[arg 0], [loc 0]]]], [app 6 [[loc 0]]], .unrestricted⟩],
   .scheme [⟨[unk], [[app 3 [[unk], [loc 0]]]], [app 6 [[arg 0, loc 0]]], .unrestricted⟩],
   .clauses [.refs [] [] [("then", [app 4 [[arg 0]]]), ("catch", [app 5 [[arg 0]]])]],
   .clauses [.refs [] [] [("then", [app 4 [[arg 0]]])]],
   .clauses [.refs [("v", [arg 0])] [] []],
   .clauses [.refs [] [] [("v", [arg 0])]],
   .clauses [.refs [] [] [("p", [app 6 [[num]]])]],
   .clauses [.refs [] [] [("p", [app 7 [[num, str]]])]],
   .scheme [⟨[unk], [], [loc 0], .unrestricted⟩],
   .scheme [⟨[unk], [], [arg 0], .unrestricted⟩],
   .clauses [.refs [] [] [("q", [num])]],
   .clauses [.refs [] [] [("q", [num, str])]],
   .clauses [.refs [] [] [("p", [app 6 [[app 14 []]]])]],
   .clauses [.refs [] [] [("p", [app 6 [[app 15 []]]])]],
   .clauses [.refs [] [] [("p", [app 6 [[num, str]]])]],
   .clauses [.refs [] [] [("p", [app 6 [[num]]])]],
   .scheme [⟨[unk], [], [loc 0], .unrestricted⟩],
   .clauses [.list ⟨[], [], some [arg 0], true, .dense⟩ []],
   .clauses [.list ⟨[[arg 0], [arg 1]], [], none, true, .dense⟩ []],
   .clauses [.refs [] [] [("initial", [app 21 [[app 22 [[arg 0], [arg 1]]]]])]]]

def good? : Option Equations := build signature rows

/-! ### Certificates -/

section
variable (E : Equations)

def lbl (t : Tree) : Label E.signature :=
  if h : t.scoped E.signature 0 0 = true then ⟨t, h⟩ else Label.familyVar 999 0 .value

def lbls (ts : List Tree) : List (Label E.signature) := ts.map (lbl E)

/-- `Var` on two labels with one subset proof per hypothesis. -/
def var (S T : List Tree) (hyps : Nat) : Bool :=
  E.checkVar E.variances (lbls E S) (lbls E T) (List.replicate hyps .subset)

/-- A family certificate: its arrow evidence proposed for its pairs. -/
def family (entries : List (Entry (Label E.signature))) (S T : List Tree) : Bool :=
  E.checkFamily E.variances (lbls E S) (lbls E T)
    { entries, arrows := E.arrowCandidates (entries.flatMap (·.pairs)) }

/-- A claim checked as the goal of one variable-free entry. -/
def claim (S T : List Tree) (pairs : List (List Tree × List Tree) := [])
    (named : List (Nat × List (List Tree)) := []) (more : List (Entry (Label E.signature)) := []) :
    Bool :=
  let goal : Entry (Label E.signature) :=
    { source := lbls E S
      target := lbls E T
      table := pairs.map (fun p => (lbls E p.1, lbls E p.2))
      instances := named.map (fun w => (w.1, w.2.map (lbls E))) }
  family E (more ++ [goal]) S T

end

/-- The index of a certificate's first entry: the heads' variances come
first. -/
def first (E : Equations) : Nat := E.signature.length

def run (f : Equations → Bool) : Bool := match good? with
  | some E => f E
  | none => false

/-! ### The equations and their variances -/

-- Every row is kept as written, and every test label is closed.
#guard good?.isSome
#guard [num, str, app 6 [[num]], app 6 [[num, str]], app 6 [[]], app 8 [[num]],
  app 8 [[num, str]], app 10 [], app 11 [], app 12 [], app 20 []].all
  fun t => t.scoped signature 0 0

-- The computed variances (§4.3): the callback `(x: A) => R` contravariant
-- in its parameter and covariant in its result; `Promise`, `PromiseLike`,
-- `then` and `catch` covariant, `Promise` and its methods one component
-- checked together with no table; `Cell`'s writable field invariant, `Box`'s
-- readonly view covariant; `InputDefinition` covariant in both through
-- `ReadonlyArray<readonly [K, V]>`, by nested instances (`Inst`).
#guard run fun E =>
  let v := E.variances
  v.of 3 == some [.contra, .co] && v.of 4 == some [.co] && v.of 5 == some [.co] &&
  v.of 6 == some [.co] && v.of 7 == some [.co] && v.of 8 == some [.inv] && v.of 9 == some [.co] &&
  v.of 21 == some [.co] && v.of 22 == some [.co, .co] && v.of 23 == some [.co, .co]
-- `Promise` and its methods are one component, dependencies first.
#guard run fun E =>
  let cs := E.components
  let pos (h : Nat) := (cs.findIdx? (·.contains h)).getD cs.size
  pos 4 == pos 6 && pos 5 == pos 6 && decide (pos 3 < pos 6) && decide (pos 0 < pos 3)
-- Step 4: a candidate that fails `Valid` becomes `inv` at every parameter.
-- `Cell` covariant, or the callback covariant in its parameter, fails.
#guard run fun E => E.settle (fun _ => none) 3 [(8, [.co])] == [(8, [.inv])]
#guard run fun E => E.settle (fun _ => none) 3 [(3, [.co, .co])] == [(3, [.inv, .inv])]
#guard run fun E => E.settle (fun _ => none) 3 [(8, [.inv])] == [(8, [.inv])]

/-! ### §7.6 examples -/

-- `Promise<number> ≤ Promise<number | string>` by `Var`, whose one premise
-- is a subset: `Promise` is not unfolded.
#guard run fun E => var E [app 6 [[num]]] [app 6 [[num, str]]] 1
-- `Promise<never> ≤ Promise<number>`: the premise is the empty union.
#guard run fun E => var E [app 6 [[]]] [app 6 [[num]]] 1
-- The negative control: the premise `number | string ≤ number` fails.
#guard run fun E => !var E [app 6 [[num, str]]] [app 6 [[num]]] 1
-- Unfolding with an ordinary core table cannot relate `then` members, whose
-- binders differ; the finite rule needs the same binder rows.
#guard run fun E => !E.checkSubtype (lbls E [app 6 [[num]]]) (lbls E [app 6 [[num, str]]])
  (.core ⟨[(lbls E [app 6 [[num]]], lbls E [app 6 [[num, str]]]),
    (lbls E [app 4 [[num]]], lbls E [app 4 [[num, str]]])], []⟩)

-- Writable positions: `Cell` declared invariant checks; its `Var` needs both
-- directions, so `Cell<number>` is below itself and not below
-- `Cell<number | string>`.
#guard run fun E => var E [app 8 [[num]]] [app 8 [[num]]] 2
#guard run fun E => !var E [app 8 [[num]]] [app 8 [[num, str]]] 2

-- Different heads: a certificate entry `Promise(a) ≤ PromiseLike(b)` with
-- `a ≤ b`, checked by `Var` on `then`; the claim
-- `{p: Promise<number>} ≤ {p: PromiseLike<number | string>}` uses it as a
-- premise instance.
def a := fv 100 0
def b := fv 100 1
def promiseLike (E : Equations) : Entry (Label E.signature) :=
  { source := lbls E [app 6 [[a]]], target := lbls E [app 7 [[b]]],
    variables := lbls E [a, b], hypotheses := [(lbl E a, lbl E b)] }
#guard run fun E => claim E [app 10 []] [app 11 []] [] [(first E, [[num], [num, str]])] [promiseLike E]
-- Without the entry the instance has nothing to name.
#guard run fun E => !claim E [app 10 []] [app 11 []] [] [(first E, [[num], [num, str]])]

-- Quantified-α renames binders: `<R>() => R` is below another head's
-- `<R>() => R`.
#guard run fun E => claim E [app 12 []] [app 20 []]

-- Recursive instance discharge (§4.2 `Inst`): `InputDefinition<K, V>` is
-- covariant in both through `ReadonlyArray<readonly [K, V]>`, with no table:
-- the view's premise is an instance of `ReadonlyArray`'s variance whose
-- hypothesis is an instance of the tuple's, whose hypotheses are hypotheses.
#guard run fun E => var E [app 23 [[num], [num]]] [app 23 [[num], [num, str]]] 2
-- A nested hypothesis that is false is refused at its instance: the tuple's
-- `number ≤ string`, inside `ReadonlyArray`'s.
#guard run fun E => claim E [app 21 [[app 22 [[num], [num]]]]] [app 21 [[app 22 [[num], [num, str]]]]]
#guard run fun E => !claim E [app 21 [[app 22 [[num], [num]]]]] [app 21 [[app 22 [[num], [str]]]]]
-- Recursion never loops: an entry whose instance would discharge its own
-- premise again at the same types is refused, since `Inst`'s premises must
-- be smaller; the check ends.
def loopy (E : Equations) : Entry (Label E.signature) :=
  { source := lbls E [a], target := lbls E [b], variables := lbls E [a, b],
    hypotheses := [(lbl E a, lbl E b)] }
#guard run fun E => !claim E [app 9 [[num]]] [app 9 [[str]]] [] [(first E, [[num], [str]])] [loopy E]
#guard run fun E => !claim E [app 9 [[num]]] [app 9 [[str]]] [] [] [loopy E]

/-! ### §7.7 controls -/

-- A `Var` use whose premise fails is the negative control above.

-- An instance whose hypothesis pair is missing from the table:
-- `Promise<{q: number}> ≤ Promise<{q: number | string}>` inside a claim needs
-- the pair `{q: number} ≤ {q: number | string}` in the claim's table.
#guard run fun E => claim E [app 16 []] [app 17 []] [([app 14 []], [app 15 []])]
#guard run fun E => !claim E [app 16 []] [app 17 []]

-- A hypothesis false at the instance (`invalid-promise-covariance`): with
-- or without a table pair for `number | string ≤ number`.
#guard run fun E => !claim E [app 18 []] [app 19 []]
#guard run fun E => !claim E [app 18 []] [app 19 []] [([num, str], [num])]

-- A writable field with a covariant hypothesis only.
def c := fv 101 0
def d := fv 101 1
def cell (E : Equations) (hyps : List (Tree × Tree)) : Entry (Label E.signature) :=
  { source := lbls E [app 8 [[c]]], target := lbls E [app 8 [[d]]], variables := lbls E [c, d],
    hypotheses := hyps.map (fun h => (lbl E h.1, lbl E h.2)) }
#guard run fun E => claim E [num] [num] [] [] [cell E [(c, d), (d, c)]]
#guard run fun E => !claim E [num] [num] [] [] [cell E [(c, d)]]

-- A family variable that also occurs in a claim.
#guard run fun E => claim E [app 6 [[num]]] [app 6 [[num]]] [] [] [promiseLike E]
#guard run fun E => !claim E [app 6 [[a]]] [app 6 [[a]]] [] [] [promiseLike E]


-- Meet parts through hypotheses (§3.3, §7.3): `x & {q: number}` below
-- `y & {q: number}` in an entry with `x ≤ y`, the target part `y` covered by
-- the source part `x`. Without the hypothesis, or with only `y ≤ x`, `y` is
-- covered by nothing. A meet with a scheme part is read part by part the
-- same way.
def meetEntry (E : Equations) (S T : Tree) (hyps : List (Tree × Tree)) : Entry (Label E.signature) :=
  { source := lbls E [S], target := lbls E [T], variables := lbls E [c, d],
    hypotheses := hyps.map (fun h => (lbl E h.1, lbl E h.2)) }
def cq := canonMeet [c, app 14 []]
def dq := canonMeet [d, app 14 []]
#guard run fun E => claim E [num] [num] [] [] [meetEntry E cq dq [(c, d)]]
#guard run fun E => !claim E [num] [num] [] [] [meetEntry E cq dq []]
#guard run fun E => !claim E [num] [num] [] [] [meetEntry E cq dq [(d, c)]]
def cs := canonMeet [c, app 12 []]
def ds := canonMeet [d, app 12 []]
#guard run fun E => claim E [num] [num] [] [] [meetEntry E cs ds [(c, d)]]
#guard run fun E => !claim E [num] [num] [] [] [meetEntry E cs ds []]
#guard run fun E => !claim E [num] [num] [] [] [meetEntry E cs ds [(d, c)]]
-- A premise reads meets the same way: `Box<x & {q: number}>` below
-- `Box<y & {q: number}>` by its readonly view, with no table pair.
#guard run fun E => claim E [num] [num] [] [] [meetEntry E (app 9 [[cq]]) (app 9 [[dq]]) [(c, d)]]
#guard run fun E => !claim E [num] [num] [] [] [meetEntry E (app 9 [[cq]]) (app 9 [[dq]]) [(d, c)]]
-- A clause part is not covered by a hypothesis: `x ≤ y & {q: number}` and
-- `x & {q: number | string} ≤ y & {q: number}` stay refused under `x ≤ y`.
#guard run fun E => !claim E [num] [num] [] [] [meetEntry E c dq [(c, d)]]
#guard run fun E => !claim E [num] [num] [] [] [meetEntry E (canonMeet [c, app 15 []]) dq [(c, d)]]

-- Quantified-α with a source binder free in the target: `<R>() => R` is not
-- related to `<S>() => R` for the source's own `R`, though the renamed
-- signatures would cover.
def binder : Tree := .bound 12 .nil 0
#guard run fun E => !claim E [app 12 []] [app 13 [[binder]]]

end Verification.Model.EquationFamilyTests
