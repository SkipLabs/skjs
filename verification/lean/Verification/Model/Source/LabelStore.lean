import Lean.Data.Json
import Verification.Model.Types.GraphRows
import Verification.Model.Types.PositiveCertificates
import Verification.Model.Programs.CertificateProducer

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
class Labels (ι : Type) extends Hashable ι, Ord ι, ToJson ι, FromJson ι, Repr ι,
    CertificateProducer.Instantiates ι where
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

/-- What checking reads of a store: labels with rows, their graph and the
image check its instances use. `σ` is the store's state, `ι` its labels.
Rows are read through `row` and interpreted through `graph`, which must
agree with them; `valid` says which labels the store holds, `wellFormed`
that its rows name only those. `labels` lists labels with rows of their own,
and `bound` bounds any closure over rows (the vocabulary a search is offered
is such a closure). A checked request reads its store through this view
only, so a store that no longer grows (`EquationStore.Checked`) is one. -/
class StoreView (σ : Type) (ι : outParam Type) [Labels ι] extends ToJson σ, FromJson σ where
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
  /-- The labels with rows of their own. -/
  labels : σ → List ι
  /-- A bound on the rounds of a fixpoint over rows. -/
  bound : σ → Nat
  /-- The realm's array prototype, `ArrayProto`: the prototype every array
  type names. -/
  arrayProto : σ → ι
  /-- The label of a union of clauses, when the store has one. -/
  lookup : σ → List (Clause (List ι)) → Option ι
  /-- What a diagnostic mentioning these labels shows of the store, rows
  expanded `depth` references deep (`Projection`). -/
  project : σ → List ι → Nat → Projection ι
  /-- How an instance's images are checked in this store's graph: proved
  sound, supplied by verified code, never by a certificate. -/
  images : (T : σ) → PositiveCertificates.InstanceImageCheck (graph T)

/-- A store the source path grows: the view, and the ways extraction adds to
it. A store only grows: every operation keeps the labels it had and their
rows. -/
class Store (σ : Type) (ι : outParam Type) [Labels ι] extends StoreView σ ι where
  /-- The label of a union of clauses, added when the store lacks it. -/
  intern : σ → List (Clause (List ι)) → σ × ι
  /-- A generic unit's binder: the store's one value parameter of that name
  that no scheme binds, or a new one. -/
  binder : σ → String → Except String (σ × ι)
  /-- Fresh value parameters, one per name, for a scheme's binders. They
  stand for the scheme's binders until `scheme` binds them: the scheme's own
  binders are its row's (`GraphRow.scheme`), which may be other labels. -/
  binders : σ → List String → σ × List ι
  /-- A value parameter read within clauses and further parameters,
  `p ⊓ cs ⊓ also`: a bounded binder. The same label for the same meet. -/
  bounded : σ → ι → List (Clause (List ι)) → List ι → σ × ι
  /-- A scheme over binders from `binders`: its signatures, its binders'
  bounds and its variadic signatures. -/
  scheme : σ → List ι → List (Arrow (List ι)) → List (ι × List ι) →
    List (RestArrow (List ι)) → σ × ι
  /-- A label with the binders named by `θ` read as their types: the source
  spells a binder by its name, and a unit or closure decides what the name
  stands for. The union a label becomes. -/
  rebind : σ → List (String × List ι) → ι → List ι
  /-- A label with labels `σ` names read as the labels it pairs them with:
  a scheme's fresh binders read as its own (`scheme`). The union a label
  becomes. -/
  substitute : σ → List (ι × ι) → ι → List ι


/-- What a diagnostic mentioning `mentioned` shows of the store, to the
projection's depth. -/
def Store.projection {σ ι : Type} [Labels ι] [StoreView σ ι] (T : σ) (mentioned : List ι) : Projection ι :=
  StoreView.project T mentioned Projection.depth

/-- The meet of unions, lowered as a source intersection is. Apart from
`Store` because a store's intersections are lowered by the pass that lowers
its declarations, which is itself written over the store. -/
class Meets (σ : Type) (ι : outParam Type) where
  meet : List (List ι) → StateT σ (Except String) (List ι)

end Verification.Model.LabelStore
