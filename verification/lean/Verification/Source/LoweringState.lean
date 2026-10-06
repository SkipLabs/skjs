import Verification.Source.SourceRequests
import Verification.Source.SourceClaims
import Verification.Source.Fragment

/-! Owns lexical slots and the mutable graph construction state. -/
namespace Verification.SourceExtraction
open CallEffects (Arrow RestArrow Contract Effect)
open Lean ProgramTyping PositiveRules ControlFlow CertificateProducer RequestJson
open Fragment LabelStore
open EquationGraphs (Tree)

section
variable {ι : Type} [Labels ι]

def distinct [BEq α] (xs : List α) : Bool := xs.eraseDups.length == xs.length

/-- What a scope slot holds. A value slot holds the value itself. A cell slot
holds the identity of a private cell this lowering allocated: `contract` is the
stable storage type every assignment is checked against, and `reference` is the
slot's own type, interned once when the binding was declared so that building
an environment stays a pure projection.

(Storage ι) comes from source declarations and assignments. A producer's
claim about `x` describes what the cell currently holds, which is exactly what
must not become the type of the slot holding its identity. -/
inductive Storage (ι : Type) where
  | value
  | cell (contract : Ty ι) (reference : Ty ι)
  deriving Repr, Inhabited

/-- A scope slot: how the source names it, and what it holds. `Descriptor` is
explanatory source-map data that cannot affect acceptance, so the storage that
decides lowering lives here and is projected away before anything is emitted. -/
structure ScopeBinding (ι : Type) where
  source : Descriptor
  storage : Storage ι := .value
  /-- A module function's slot: its type is its own source signature, never a
  producer claim, and it is a value slot, so no assignment can reach it. -/
  fixed : Option (Ty ι) := none
  /-- A `let`'s cell: the types of the slots below it when it was allocated,
  whose records' fields its fresh location differs from. -/
  apart : Option (List (Ty ι)) := none
  /-- A constant bound to an object or array it allocated: its fields are
  fresh, so they differ from every older cell's location. -/
  fresh : Bool := false
  /-- A parameter: bound before the body runs, so before any cell the body
  allocates, and at the same time as an assigned parameter's cell. -/
  param : Bool := false
  deriving Repr

@[nospecialize] def held (d : Descriptor) : ScopeBinding ι := { source := d }

/-- Explanatory projection: what a reader is shown, with the storage dropped. -/
@[nospecialize] def sources (scope : List (ScopeBinding ι)) : List Descriptor := scope.map (·.source)

/-- Name lookup is unchanged: descriptors carry the same names in the same
order, and an unnamed one can never match a source identifier. -/
@[nospecialize] def names (scope : List (ScopeBinding ι)) : List String := scope.map (·.source.name)

/-- The one place a source name becomes a slot, so no site can decide for
itself whether a name denotes a value or a location. -/
@[nospecialize] def resolve (scope : List (ScopeBinding ι)) (name : String) : Option (Nat × (Storage ι)) := do
  let i ← (names scope).idxOf? name
  let b ← scope[i]?
  return (i, b.storage)

/-- Only immutable value slots may be substituted by a guard's saved value. -/
@[nospecialize] def valueSlot (scope : List (ScopeBinding ι)) (name : String) : Option Nat := do
  let (i,.value) ← resolve scope name | none
  return i

/-- State local to one compiled graph. A closure begins with an empty frame
and restores its enclosing frame as a whole. -/
structure GraphFrame where
  program : Program := []
  /-- Computed types of saved execution-plan values, scoped to their bindings. -/
  executionTypes : List (String × Ty Tree) := []
  /-- Immutable aliases retained by evaluated operands for predicate refinement. -/
  executionOrigins : List (String × Fragment.Expr) := []
  /-- Prepared atoms consume saved operands; the plan owns source observations. -/
  atomicPrepared : Bool := false
  /-- Source metadata for a primitive whose executable operands are saved values. -/
  executionOriginal : Option Fragment.Expr := none
  /-- A saved method call passes this already evaluated receiver. -/
  executionReceiver : Option String := none
  /-- One source statement whose ownership gate permits a fresh local copy. -/
  executionOwned : Option Span := none
  claims : List (PointClaim Tree) := []
  sourceMap : SourceMap := []
  assertions : List (Nat × HeapKnowledge.Knowledge) := []
  /-- Full statement-entry interfaces; absent assertions mean empty knowledge. -/
  cuts : List Nat := []
  /-- While a `try` body or handler is compiled: where a throw out of a node
  goes, as a target over the handler's scope (the thrown value's slot, then
  the scope of the `try`), and the length of the `try`'s scope. Every node
  emitted meanwhile whose expression may throw names it. -/
  handler : Option (Target × Nat) := none

/-- Equation growth, obligations and nested code are shared across graph frames. -/
structure Built extends GraphFrame where
  /-- The graph under construction: the claims' table, grown by annotations. -/
  types : EquationStore.State
  flowTargets : List (Nat × Target) := []
  obligations : List (ExpressionClaims.Required Tree) := []
  /-- Labels the program mentions but no claim does, such as a pattern's
  literal index: search hints, never part of what is checked. -/
  hints : List Tree := []
  /-- The graph code the body creates, nested code first, each at each
  signature it offers, and what the source says of each code's graph. -/
  codes : List (CodeRequest Tree) := []
  codeSources : List CodeSource := []
  /-- Plans for nodes whose derivation the lowering already knows: search
  hints only, rendered where they can be and never obligations. -/
  nodePlans : List (DirectProof.Plan Tree) := []
  /-- The key-adding write sites of the body (`growSites`): the writes that
  may add a key, by copying their owned object. -/
  grows : List Span := []

/-- Source-validation failures that already know their source site use the same
structured channel as proof obligations. Keeping the diagnostic construction
here prevents an adapter check from degrading into an unlocated exception. -/
def locatedRefusal (T : EquationStore.State) (pos : Span)
    (role : DirectObligation.SourceRole) (reason : String) : String :=
  RequestJson.withDiagnostic s!"source refusal at [{pos.1},{pos.2}): {reason}"
    ([("kind",toJson "source-refusal"),("phase",toJson "request-validation"),
     ("outcome",toJson RequestJson.DiagnosticOutcome.notEstablished),("id",toJson s!"refusal:{pos.1}"),
     ("sourceMap",toJson (SourceMapEntry.mk pos role.wire none [])),
     ("reason",toJson reason),("fuel",toJson 0)] ++ (StoreView.projection T []).fields)

abbrev Compiler := StateT Built (Except String)

/-- Compile a graph in a fresh frame. Successful shared-state updates survive;
the enclosing graph frame is restored. A failure returns no state. -/
def withFreshGraph (action : Compiler α) : Compiler α := fun before => do
  let (value, after) ← action { before with toGraphFrame := {} }
  return (value, { after with toGraphFrame := before.toGraphFrame })

@[nospecialize] def table : Compiler EquationStore.State := do return (← get).types

@[nospecialize] def lower (m : SourceTypes.Lowering α) : Compiler α := do
  let s ← get
  let (a, T) ← m.run s.types
  set { s with types := T }
  return a

end
end Verification.SourceExtraction
