import Lean.Data.Json
import Verification.Model.Types.GraphRows

/-! What the source path asks of the labels it types a program with, and of
the store that gives them meaning. Extraction, the source claims' readers and
the checked requests are written against these two interfaces, not against a
representation: the finite table of rows, indexed by position, is one store
(`SourceTypes`), and the equation labels of RECURSIVE-EQUATIONS §8 are to be
another. Neither interface carries a proof obligation: a store's graph is
what the checked requests are proved safe over, whatever store built it. -/
namespace Verification.Model.LabelStore
open Lean PositiveGraphs PositiveNormalization CallEffects

/-- A label, apart from any store: decidable equality and hashing (search
caches are keyed by types), a total order for the canonical order of unions,
its JSON spelling, and the four primitive values' labels, which every store
holds as they are. -/
class Labels (ι : Type) extends Hashable ι, Ord ι, ToJson ι, FromJson ι, Repr ι where
  decEq : DecidableEq ι
  nul : ι
  tru : ι
  fls : ι
  undef : ι

instance (priority := low) {ι : Type} [Labels ι] : DecidableEq ι := Labels.decEq

namespace Labels
variable {ι : Type} [Labels ι]

/-- The order of a canonical union: sorted by `compare`, each label once. -/
def le (a b : ι) : Bool := compare a b != .gt

def lt (a b : ι) : Bool := compare a b == .lt

/-- Lexicographic order on unions, for the canonical order of their lists. -/
def before : List ι → List ι → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => lt a b || (a == b && before as bs)

end Labels

/-- What a diagnostic shows of a store: a finite table of rows over its own
positions, the position each label the diagnostic mentions is shown at, and a
source-like spelling of the positions that stand for applications
(`Promise<number | R>`). The table holds the mentioned labels and what their
rows name, to a depth bound; past it, an application is an opaque named
reference: a `names` entry whose row has no clauses. A diagnostic is display
data: nothing checks or trusts a projection. -/
structure Projection (ι : Type) where
  /-- The table under `types`, rows naming positions in it. -/
  rows : List (GraphRow Nat)
  /-- Where a mentioned label is shown: its position in `rows`. -/
  position : ι → Nat
  /-- An application's spelling by position, in position order, each once;
  `names`, left out when empty. -/
  names : List (Nat × String) := []

namespace Projection

/-- How many row references below a mentioned label a projection expands. -/
def depth : Nat := 3

/-- A union as a diagnostic shows it. -/
def shown {ι : Type} (p : Projection ι) (A : List ι) : List Nat := A.map p.position

end Projection

/-- A store: labels with rows, and the ways the source path adds to it. `σ`
is the store's state, which extraction threads through a unit; `ι` its labels.

Rows are read through `row` and interpreted through `graph`, which must agree
with them; `valid` says which labels the store holds, `wellFormed` that its
rows name only those. `labels` lists them, and `bound` bounds any closure
over rows (the vocabulary a search is offered is such a closure). A store only
grows: every operation keeps the labels it had and their rows. -/
class Store (σ : Type) (ι : outParam Type) [Labels ι] extends ToJson σ, FromJson σ where
  /-- The graph the store denotes. Built once per state: its rows are read
  at every step of search and checking. -/
  graph : σ → NormalGraph ι
  /-- A label's row; an empty clause row for a label the store lacks. -/
  row : σ → ι → GraphRow ι
  /-- Whether the store holds a label. -/
  valid : σ → ι → Bool
  /-- Whether every row names only labels the store holds, and binds only
  parameters. -/
  wellFormed : σ → Bool
  /-- Every label the store holds. -/
  labels : σ → List ι
  /-- A bound on the rounds of a fixpoint over rows. -/
  bound : σ → Nat
  /-- The realm's array prototype, `ArrayProto`: the prototype every array
  type names. -/
  arrayProto : σ → ι
  /-- The label of a union of clauses, added when the store lacks it. -/
  intern : σ → List (Clause (List ι)) → σ × ι
  /-- The label of a union of clauses, when the store has one. -/
  lookup : σ → List (Clause (List ι)) → Option ι
  /-- A generic unit's binder: the store's one value parameter of that name
  that no scheme binds, or a new one. -/
  binder : σ → String → Except String (σ × ι)
  /-- Fresh value parameters, one per name, for a scheme's binders. -/
  binders : σ → List String → σ × List ι
  /-- A value parameter read within clauses and further parameters,
  `p ⊓ cs ⊓ also`: a bounded binder. The same label for the same meet. -/
  bounded : σ → ι → List (Clause (List ι)) → List ι → σ × ι
  /-- A scheme over binders: its signatures, its binders' bounds and its
  variadic signatures. -/
  scheme : σ → List ι → List (Arrow (List ι)) → List (ι × List ι) →
    List (RestArrow (List ι)) → σ × ι
  /-- What a diagnostic mentioning these labels shows of the store, rows
  expanded `depth` references deep (`Projection`). -/
  project : σ → List ι → Nat → Projection ι

/-- What a diagnostic mentioning `mentioned` shows of the store, to the
projection's depth. -/
def Store.projection {σ ι : Type} [Labels ι] [Store σ ι] (T : σ) (mentioned : List ι) : Projection ι :=
  Store.project T mentioned Projection.depth

/-- The meet of unions, lowered as a source intersection is. Apart from
`Store` because a store's intersections are lowered by the pass that lowers
its declarations, which is itself written over the store. -/
class Meets (σ : Type) (ι : outParam Type) where
  meet : List (List ι) → StateT σ (Except String) (List ι)

end Verification.Model.LabelStore
