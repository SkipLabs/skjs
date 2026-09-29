# Viewer language and boundaries

The viewer displays producer claims and failed obligations, never trusted
assertions. Source identity, claim identity, and proof checking remain separate.
There are two explicitly typed representations: the structural claim text a
report prints, which can state TypeScript shapes outside the calculus, and the
native graph the source sidecar and the verifier use. Lifting a graph into the
text fails rather than erasing a requirement.

## Structural claim text

`tools/claim.mts` declares `ClaimType`, `Atom`, `Field`, `RecordAtom`, and
`FunctionAtom`; the source parser imports these same declarations.
`decodeClaimType` checks fields recursively. `tools/claim-text.mts` supplies
`printType`, and `lift`, which reads a normalized claim into this encoding.
Text determines the type without a previous claim.

| Form | Meaning |
| --- | --- |
| `unknown`, `never` | Top and empty union |
| `boolean`, `null`, `undefined`, `string`, `number` | Primitive types |
| `true`, `false`, `"text"`, `3` | Literal types |
| `A \| B` | Union |
| `{ name: A, optional?: B }` | Required and optional fields |
| `{ "a,b": A }` | Quoted field name |
| `{ value: A = (B) }` | Storage invariant A and current-content assertion B |
| `(A, B) => C` | Ordered parameters and result; zero parameters and nested functions are allowed |
| `((A) => B) & { value: C }` | Combined invocation and field contract |
| `T` | A type parameter of the enclosing function or closure, by its source name |
| `<T>(arg0: T) => T` | A quantified callable; binders carry `extends A` when bounded, and its parameters are shown positionally |
| `() => T` | A callable over an enclosing type parameter, with no binders of its own |
| `T @{...}` | Explicit nondefault object metadata |

Arrow alternatives in a union are parenthesized. Nondefault metadata on an
arrow follows parentheses around the whole arrow, so it cannot attach to the
result by accident. Bare records have absent indexes and unknown call,
constructor and array modes; bare functions have unknown constructor and array
modes. For example:

```text
((boolean) => null) @{"construct":"absent"}
{ value: boolean } @{"call":"absent","indexes":{"string":"synthetic","number":"absent","symbol":"synthetic"}}
```

Metadata accepts only the relevant mode fields and `and` (a list of structural
atoms for simultaneous requirements). It cannot replace fields, parameters, or
the atom kind. The printer writes every nondefault mode, including `and`.
Unknown producer shapes are shown as their exact JSON. `(unavailable)` is a
report marker, not a type.

The text grammar is a claim language, not all TypeScript syntax. Syntactic
expressibility is distinct from verification support: optional or multiple
fields can be printed, and the source adapter supports its documented fragment.

A bare graph-label list such as `[5]` is not the claim language: a normalized
claim is lifted into structural text, with `#5` only as auxiliary graph
identity. A recursive or not-yet-expressible type is shown through its graph
definitions; exact label JSON is not a readable standalone claim because its
meaning depends on the accompanying graph.

## Native graph and term language

`tools/type-graph.mts` declares the complete native `Clause`, `Arrow`, `Row`, and
`TypeGraph` types, shared by the source sidecar and its producers. It mirrors
`PositiveNormalization.Clause` as serialized by `RequestJson.lean`. Both rows and
label lists denote unions; clauses retain all simultaneous field contracts and
all ordered arrow domains/results. Labels have no implicit meaning in a general
request graph. The source sidecar separately requires its primitive prefix.

`decodeGraph` validates every constructor, field, and reference of the exact
JSON syntax. `graphDefinitions` prints each row once as `#n = ...`; references
remain references. Self-reference needs no exception and overloads are never
reduced to a single arrow. The readable definitions are a display.

`tools/calculus.mts` similarly declares `Term`, `CallCode`, and `Tag`
against `Calculus.lean`. `decodeTerm` / `printTerm` are exact, validated JSON.
Terms retain native slot numbers so the printed obligation matches the calculus;
source names are shown alongside in its context table.

`tools/control-flow.mts` declares the program graph over those terms —
`Target`, `Continuation`, and `ProgramNode` — against `ControlFlow.lean`. A node
names its successors and their slot maps explicitly, so the node in a failure
record is validated as program data rather than inferred from its expression.

## Obligations and consistency

`tools/diagnostic.mts` reads the native failure record, checking its
graph, sequent, mappings, source descriptors, and heap facts. Malformed or unknown
records remain human diagnostics. `tools/diagnostic-view.mts` prepares a typed
presentation at report generation and the complete graph legend. A direct
obligation is a subtyping judgment between two ground types at a call's span,
decoded structurally, its labels checked against the record's graph.
`formatJudgement` is the only `A ⊢ B` printer and takes the structured assumptions
and conclusion, so neither a producer nor a presentation call site can put prose
to the right of a turnstile. Its switches use `never` exhaustiveness checks, and
the decoder rejects unknown variants. The viewer renders `obligationView`; it does not infer an obligation
from a diagnostic sentence. [OBLIGATION-DIAGNOSTICS](OBLIGATION-DIAGNOSTICS.md)
owns the exact failure contract.

TypeScript compilation checks the shared declarations against source extraction,
sidecar producers, report generation and Svelte. The reader section of
`ocaml-producer/test.mts` collects pipeline reports and reads them back as the
page does: the annotated source, every function with its verdict and expression
claims, obligation presentations decoded from Lean-emitted records, and a
failure shown at the claim whose obligation stopped. Run `make verify` and the
viewer build after changing these boundaries.
