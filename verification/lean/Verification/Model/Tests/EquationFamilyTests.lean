import Verification.Model.Types.EquationFamilies

/-! Family subtyping on recursive equations: the examples and required
controls of RECURSIVE-EQUATIONS §7.6–§7.7, as concrete checks. `Promise`
is covariant by a checked declaration, and a use relates two of its
applications by `Var` without unfolding `Promise`. The source pipeline
cannot reach these checks until equations are lowered from source, so they
are tests of the kernel checker. -/
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

def plain (params : Nat) (variance : List (ParameterKind × Variance) := []) : Header :=
  ⟨params, [], variance⟩
def generic (params : Nat) (variance : List (ParameterKind × Variance) := []) : Header :=
  ⟨params, [⟨"R", .value⟩], variance⟩

def co : ParameterKind × Variance := (.value, .co)

/-- Heads: 0 `number`, 1 `string`, 2 `unknown`, 3 `(x: A) => R`,
4 `then<R>(f: (x: T) => R): Promise<R>`, 5 `catch<R>(f: (e: unknown) => R): Promise<T | R>`,
6 `Promise<T>` with views `then` and `catch`, 7 `PromiseLike<T>` with `then`,
8 `Cell<T>` with a writable field, 9 `Box<T>` with a readonly view,
10 `{p: Promise<number>}`, 11 `{p: PromiseLike<number | string>}`,
12 `<R>() => R`, 13 `<S>() => T`, 14 `{q: number}`, 15 `{q: number | string}`,
16 `{p: Promise<14>}`, 17 `{p: Promise<15>}`, 18 `{p: Promise<number | string>}`,
19 `{p: Promise<number>}`, 20 `<R>() => R` again. -/
def signature (fnV cellV boxV : List (ParameterKind × Variance)) : Signature :=
  [plain 0, plain 0, plain 0, plain 2 fnV, generic 1 [co], generic 1 [co], plain 1 [co],
   plain 1 [co], plain 1 cellV, plain 1 boxV, plain 0, plain 0, generic 0, generic 1 [co],
   plain 0, plain 0, plain 0, plain 0, plain 0, plain 0, generic 0]

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
   .scheme [⟨[unk], [], [loc 0], .unrestricted⟩]]

def contraCo : List (ParameterKind × Variance) := [(.value, .contra), co]
def inv : List (ParameterKind × Variance) := [(.value, .inv)]

/-- The equations as the producer should declare them. -/
def good? : Option Equations := build (signature contraCo inv [co]) rows

/-! ### Certificates -/

section
variable (E : Equations)

def lbl (t : Tree) : Label E.signature :=
  if h : t.scoped E.signature 0 0 = true then ⟨t, h⟩ else Label.familyVar 999 0 .value

def lbls (ts : List Tree) : List (Label E.signature) := ts.map (lbl E)

/-- Arrow evidence proposed for a family's pairs: every source signature for
every target signature, the target's renamed to the source's binders. The
checker accepts only the evidence it checks. -/
def arrowCandidates (pairs : List (List (Label E.signature) × List (Label E.signature))) :
    Evidence (Label E.signature) :=
  pairs.flatMap fun (A, B) =>
    ((sourceClauses E.graph A).flatMap fun a => (clausesOf E.graph B).flatMap fun b =>
      match a, b with
      | .arrs L _, .arrs M _ => M.flatMap fun q => L.map fun p => (L, (q, ArrowCert.source p))
      | _, _ => []) ++
    (A.flatMap fun i => B.flatMap fun j => match E.graph.schemes i, E.graph.schemes j with
      | some s, some s' =>
        let σ := s'.binders.zip (s.binders.map fun p => [p])
        (s'.signatures.map (Arrow.map (E.renaming.substitute σ)) ++ s'.signatures).flatMap fun q =>
          s.signatures.map fun p => (s.signatures, (q, ArrowCert.source p))
      | _, _ => [])

def varianceEvidence (tables : List (Nat × Table (Label E.signature)) := []) :
    VarianceEvidence E.signature :=
  let entries := varianceEntries (sig := E.signature) { tables }
  { tables, arrows := arrowCandidates E (entries.flatMap (·.pairs)) }

def variances? : Option (Variances E) := Variances.check? E (varianceEvidence E)

/-- `Var` on two labels with one subset proof per hypothesis. -/
def var (S T : List Tree) (hyps : Nat) : Bool :=
  match variances? E with
  | some v => E.checkVar v (lbls E S) (lbls E T) (List.replicate hyps .subset)
  | none => false

/-- A family certificate: its arrow evidence proposed for its pairs. -/
def family (entries : List (Entry (Label E.signature))) (S T : List Tree) : Bool :=
  match variances? E with
  | some v => E.checkFamily v (lbls E S) (lbls E T)
      { entries, arrows := arrowCandidates E (entries.flatMap (·.pairs)) }
  | none => false

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

def run (f : Equations → Bool) : Bool := match good? with
  | some E => f E
  | none => false

/-! ### The equations and their declarations -/

-- Every row is kept as written, and every test label is closed.
#guard good?.isSome
#guard [num, str, app 6 [[num]], app 6 [[num, str]], app 6 [[]], app 8 [[num]],
  app 8 [[num, str]], app 10 [], app 11 [], app 12 [], app 20 []].all
  fun t => t.scoped (signature contraCo inv [co]) 0 0

-- The declarations check once, together: `Promise` and `then` rely on each
-- other and on `(x: A) => R` through `Var`, with no table.
#guard run fun E => (variances? E).isSome
#guard run fun E => E.varianceRefused (varianceEvidence E) = []

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
#guard run fun E => claim E [app 10 []] [app 11 []] [] [(21, [[num], [num, str]])] [promiseLike E]
-- Without the entry the instance has nothing to name.
#guard run fun E => !claim E [app 10 []] [app 11 []] [] [(21, [[num], [num, str]])]

-- Quantified-α renames binders: `<R>() => R` is below another head's
-- `<R>() => R`.
#guard run fun E => claim E [app 12 []] [app 20 []]

/-! ### §7.7 controls -/

-- A declaration the body contradicts is refused, located at its head:
-- `Cell` declared covariant (its field is writable), a callback parameter
-- declared covariant (`then` relies on it, and fails with it), `Box`'s
-- read parameter declared unused.
#guard match build (signature contraCo [co] [co]) rows with
  | some E => (variances? E).isNone && E.varianceRefused (varianceEvidence E) = [8]
  | none => false
#guard match build (signature [co, co] inv [co]) rows with
  | some E => (variances? E).isNone && E.varianceRefused (varianceEvidence E) = [3, 4]
  | none => false
#guard match build (signature contraCo inv [(.value, .none)]) rows with
  | some E => (variances? E).isNone && E.varianceRefused (varianceEvidence E) = [9]
  | none => false

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

-- Two entries that share a variable, or an entry reusing a declaration's.
#guard run fun E => !claim E [num] [num] [] [] [promiseLike E, promiseLike E]
#guard run fun E => !claim E [num] [num] [] []
  [{ source := lbls E [app 6 [[fv 6 0]]], target := lbls E [app 6 [[fv 6 0]]],
     variables := lbls E [fv 6 0] }]

-- Quantified-α with a source binder free in the target: `<R>() => R` is not
-- related to `<S>() => R` for the source's own `R`, though the renamed
-- signatures would cover.
def binder : Tree := .bound 12 .nil 0
#guard run fun E => !claim E [app 12 []] [app 13 [[binder]]]

end Verification.Model.EquationFamilyTests
