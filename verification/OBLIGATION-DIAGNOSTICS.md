# Obligation diagnostics

This is explanatory metadata about an unsuccessful verification attempt, not
proof evidence and not a judgement that a source claim is false. The independent
certificate consumer and successful evidence formats are unchanged.

## Transport and identity

On a structured failure, the verifier emits its existing human-readable error,
then one line on stderr:

```text
obligation-diagnostic: {"phase":"proof-search","outcome":"not-established",...}
```

`verification/tools/diagnostic.mts` reads the record without parsing the
human sentence. A record it cannot decode field by field, and a duplicate
record, are not interpreted: the reader requires the fields below and refuses
what it does not recognize, so a record it accepts is one of exactly this
shape. Every `not-established` result has a `location`. A failed direct
generic/scheme judgment carries the `direct-obligation` record described below;
source-conversion refusals use their typed source location. A verifier failure
that supplies neither is an internal protocol error and no report is written.
Absence of a structured record never changes a failure into success.

`annotate-source.mts` preserves recognized records as `results[i].obligation` and
keeps the machine payload out of the human `detail`. It adds `input`:

- `file`, `functionName`, `namePos`: the selected source function.
- `sourceSha256`: hash of the source text used for the attempt.
- `claimsSha256`: hash of `JSON.stringify` of the selected claim document passed
  to Lean. This is **not** the manifest's hash of the original claims file bytes.

IDs (`node:L`, `edge:L:I`, `expression:I`) are local to this function and attempt.
Do not preserve a selection across edits using only these IDs. Existing report
fingerprints and candidate revisions still determine freshness. A saved diagnostic
is untrusted display data; it cannot establish verification status.

## Common fields

| Field | Meaning |
|---|---|
| `kind` | `node-typing`, `edge-coverage`, `expression-claim`, `direct-obligation`, or `production-failure`. |
| `phase` | `proof-search`, `certificate-check`, or `request-validation`. |
| `outcome` | `not-established`. |
| `fuel` | Search depth used for this attempt, not a semantic bound or a diagnosis of exhaustion. |
| `types` | Exact finite graph table; type lists in the record index this table. |
| `requiredResult` | Whole-function result type on graph diagnostics; absent on standalone expression obligations. |
| `id` | Local obligation identity, where available. |

The exact calculus term and type graph use the encodings in
[REQUEST-PROTOCOL](REQUEST-PROTOCOL.md). Sequents have `context`, `term`, and `type`.
Context entries are de Bruijn slots, most recent first, and may include anonymous
saved results. They are not necessarily a source statement environment.

## Direct obligations

Rigid-generic validation and universal scheme introduction happen before a
ground graph request exists. Their failures are `direct-obligation` records,
with mandatory `sourceMap` and a `judgment` containing the checking `system` and
the exact rejected `statement`. They must not be disguised as graph sequents.
Lean diagnostics render ground types only through `SourceTypes.render`; numeric
labels remain references inside the graph document and never become type names
in user-facing judgments.

Source extraction constructs one explicit plan for every decoded function:
either a graph request or a successfully checked direct-generic plan. There is
no optional request and no filtering step, so adding a source function cannot
silently omit it from validation. A direct check that fails stops request
construction through the located diagnostic channel.

## Node and expression obligations

A `node-typing` record has:

- `source`: `{label, sourceMap, node, claim}`. `node` includes the expression and
  continuation; `claim` includes its entry context and required expression type.
- `sequent`: the exact judgement attempted at that node.

An `expression-claim` record has `sourceMap` and `sequent` directly. Its role may
be an expression claim, closure entry check, local annotation or closure result.
The kind identifies the obligation collection, not a claim of semantic blame.

`sourceMap` is this node's entry in the graph's **source map**: how to describe
the node, and each of its context bindings, in the words of the source it was
lowered from. It is nullable. When present, it contains:

- `pos`: source span, in the parser's UTF-16 offsets.
- `role`: assigned where extraction creates the obligation.
- `environmentStart`: optional source statement-entry offset, only where known.
- `context`: one descriptor per context binding, in context order.

A descriptor has `name`, the source binding this one is addressable by, and
`span`, the source expression whose value it holds; at least one is present.
Lowering is the only pass that knows both the source and the graph, so it is the
only pass that can record this, and it fails rather than emit a context it
cannot describe. **A reader therefore never has to show a position.** Render a
`name` as itself and a `span` as the source text it covers.

Source maps are explanatory in the strict sense: the structure has no decoder,
never reaches a request or a certificate, and cannot affect acceptance. A wrong
descriptor mislabels a message and nothing else. The rule that keeps this clean:
anything travelling back toward a reader carries source descriptors, anything
staying inside the calculus carries positions. `sequent.context`,
`transfer.available` and `target.mapping` are the calculus's own words and stay
positional; a reader joins them to the descriptors by index.

Current roles are `tag-dispatch`, `node-typing`, `return-contract`, `binding-annotation`,
`expression-claim`, `closure-entry`, `closure-result`, and `heap-observation`. The generic
`node-typing` role deliberately does not guess a more specific source purpose.
Unknown roles should display a generic obligation, not a guessed explanation.
The span for a closure result may be the lambda span, rather than its body span.

At a top-level return, expression typing and result-contract checking are
separate nodes that can have the same span. For example, a saved `boolean` result
cannot establish a declared `true` result even when the source expression's claim
is itself valid. The `return-contract` sequent shows the saved result in slot 0
and the required function result as its conclusion. `environmentStart` links to
the original return entry; it does not mean its environment equals the entire
node context (which includes the saved result).

## Edge obligations

An `edge-coverage` record includes `source` and `destination` node records,
`edgeIndex` (0 for the first edge, 1 for the second), and `transfer`:

- `available`: the context before applying the destination map, including any
  result pushed by bind or Boolean dispatch.
- `target`: exact destination label and slot mapping.
- `booleanObservation`: true/false for a result-binding Boolean branch; otherwise
  null. The observed slot is 0. This is the premise of that edge, **not** a claim
  that execution has actually taken the edge.

- `tagObservation`: `{test, answer, slot: 0}` for tag dispatch; otherwise null.
  Like Boolean observations, this describes the selected edge's premise, not an
  assertion that runtime took it. This additive field uses the existing tag encoding.

The destination requirement is `destination.claim.context`. Both branch edges
can have the same destination label and different maps; `edgeIndex` identifies
which obligation failed. Refinement must be interpreted together with the
observation, not as ordinary subtyping of `available` alone.

## Display contract

Readers of the diagnostic record should:

1. Prefer `obligation` to inferring a failure role from a span or source AST.
2. Present the available assumptions and required conclusion. For edges, expose
   both endpoints and the selected map/observation. Offer source selection only
   for validated spans that are present.
3. Distinguish “return contract”, “expression claim”, and the other known roles.
   Keep generic roles generic. Do not label a participant as the wrong claim.
4. Render internal types through the supplied graph table, or clearly show a
   technical fallback. Do not assume all IDs are the current primitive profile.
5. Preserve the existing first-failure and not-a-disproof wording and freshness
   rules. Treat a failed verifier result without a recognized location as a
   protocol error rather than inventing display metadata.

No recursive proof-search trace, minimal failing premise, or complete dependency
graph is promised. Extraction/type-decoding/missing-claim failures use typed
source locations. An independent certificate rejection is an internal error,
because the producer just emitted evidence that its consumer rejects. A source map entry
does not identify every contributing source claim or prove any premise separately.
There are no retained mutable-heap observations. Future overloads and generics
should extend explicit obligation data rather than force them into
an `in / claim / out` triple or infer their roles in the viewer.

`tests/obligation-diagnostics.mts` exercises the three partial repairs and full
repair of the return example, identical spans with different obligations,
selected maps on shared-destination branches, input fingerprints, and records
the reader must refuse. It runs under `make verify-test`.

## Source-extraction failures

Some attempts stop before a calculus obligation can be constructed. Their report
has `status: "not-established"`, `stage: "source-extraction"`, and a `location`:

| Location kind | Meaning | Outcome |
| --- | --- | --- |
| `unavailable-type-claim` | A required producer type is the exact `{ "unsupported": true }` sentinel. | **? — required type unavailable** |
| `source-limitation` | The claim is present, but the source consumer cannot handle it. | **? — could not check** |

Neither outcome is a failed proof search or a judgement that the claim is false.
Malformed types are not treated as unavailable sentinels. Unused unavailable
bindings do not prevent verification.

Environment locations use `start` and, when identified, `binding`; expression
locations use `pos`. A signature failure may have neither. Attach only to the
reported site. These failures carry no calculus `obligation`: do not synthesize
a sequent or infer a culpable expression from a known runtime counterexample.

### Reason vocabulary

Reasons explain source-extraction limits; they are not evidence and do not change
the classification above. Exporter reasons are optional metadata in
`functions[i].unavailableTypes`. The report copies a reason to `location.reason`
only for an unambiguous required entry binding or expression, and excludes that
metadata from verifier input. Missing, malformed, stale, ambiguous, or unfamiliar
reasons must not affect verification; readers use a generic explanation when
necessary.

Besides `parameter`, `result`, `entry`, and `expression`, `unavailableTypes[i].kind`
also carries `lvalue` (a spot in `functions[i].lvalues`, same shape as `exprs`)
and `declared` (a binding's declared type, in `envs[i].vars[j].declared`). A
function's claims object also carries, additively, a top-level `lvalues` array —
one `{pos, type}` entry per expression span SKJS typed as an assignment target or
a binding pattern rather than as a value (`exprTypes`'s `isLValue` key) — and each
`envs[i].vars[j]` binding object carries `mutable` (`true` for `let`/`var`/a
parameter/a catch variable, `false` for `const` and for `this`) and, only when it
differs from the narrowed `type`, `declared` (the binding's declared type).
`Fragment.decodeClaims` and `annotate-source.mts`'s `fromSkjs` read this
export by field name, so the additions reach both as soon as the field is
declared in the type they share.

For `unavailable-type-claim`, [SkjsTypeClaims.sk](../src/SkjsTypeClaims.sk) emits:

| Reason | Emitted when |
| --- | --- |
| `unsupported-primitive` | A `bigint` or `symbol`, outside the export format. |
| `unsupported-type` | A clause has no representable types. |
| `nested-object-type` | An object occurs as a field, parameter or result type; objects are exported at the top of a claim only. |
| `cell-is-array`, `cell-symbol-field`, `cell-index-signature`, `cell-callable`, `cell-constructible` | A branch read as a cell has an array brand, a symbol field, a real index signature, or positive callability or constructibility. |
| `cell-field-name`, `cell-field-access`, `cell-field-count` | A branch read as a cell has a field not named `value`, a non-public field, or a number of fields other than one. |
| `function-has-fields`, `function-index-signature`, `function-is-array`, `function-constructible` | A branch read as a function carries unsupported symbol fields, an index signature, an array brand, or a construct signature. A supported required `value` field uses a combined callable contract; unsupported property shapes use the cell refusal reasons. |
| `function-generic`, `function-this-parameter`, `function-optional-parameter`, `function-rest-parameter` | A signature has type parameters, a `this` parameter, optional or rest parameters. |
| `function-without-signature`, `not-callable` | A branch is provably callable with no signature, or has no call at all. |
| `no-object-branch` | The object has no branches. |
| `unexpanded-type` | A single unexpanded type of another kind, an array literal. |
| `unexpanded-named-type`, `unexpanded-intersection`, `several-unexpanded-types` | The type is an unexpanded alias or class instantiation, an unexpanded intersection, or more than one unexpanded type. |
| `type-parameter` | A clause carries a universally quantified type parameter. |
| `union-of-clauses` | The type has more than one clause, outside the bounded encoding. |
| `unbound-inference-variable` | An isolated unconstrained inference variable has no binding in the function's substitution snapshot. |
| `constrained-inference-variable` | An isolated inference variable carries constraints. |
| `fuel-exhausted` | Bounded type export exhausts its recursion fuel, independently of proof-search fuel. |

A branch that fits neither reading reports the reason of the reading its
shape asks for: a callable branch is a function that failed, anything else a
cell that failed. A field, parameter or result type that cannot be exported
gives the branch its own reason, so the innermost cause is the one reported.

Representable object branches are exported as separate union atoms. Multiple
branches alone are not a refusal reason. An unsupported branch causes refusal
of the whole type rather than a partial export. A class instance exports its
branches like any other object; the class name it carries is display
information.

Current-content assertions in the supported cell profile now reach checked
obligations. Graph failures use `edge-coverage`, with destination `sourceMap` role
`heap-observation`; `requiredKnowledge` at the destination identifies the actual
cell facts. Ordinary closure/compositional proofs use `expression-claim` with the
same role for uniform invariant justification. These are proof failures,
not exporter refusals. [Program typing](PROGRAM-TYPING.md#source-observation-checkpoints)
owns their interpretation.

`non-invariant-cell-contract` remains the one `source-limitation` reason the
report reader classifies. An unequal-contract error can still arise in an
ordinary type/signature or unsupported record union; standalone point
observations take the assertion path.

[Annotated-source tests](tests/annotated-source.mts) check reason transport and
classification; [viewer tests](tests/report-viewer.mts) cover known, unknown, and
absent reasons. [Source-claim export tests](tests/source-claim-export.mts) check
that observations survive conversion and become proof obligations rather than
being silently erased.

## Report presentation

The report writer attaches `obligationView` beside the exact raw `obligation`.
`tools/diagnostic-view.mts` prepares it once; Svelte only renders the typed
presentation. Its `judgement` has `assumptions`, `conclusion`, and their printed
`A ⊢ B` form. Node and expression failures use the recorded sequent. Edge
failures state the available slots, branch premise, target mapping, and heap
requirements explicitly; a transfer is not reduced to plain subtyping. A
production failure without a goal has no invented sequent.

Every graph row is shown once in `graph`, with labels in the judgement referring
to these definitions. Cycles and overloads are preserved without recursive
unfolding or a depth limit. The compact type summaries elsewhere in the report
are conveniences; this graph legend and the native term in the judgement give
the exact language. See [VIEWER-LANGUAGE](VIEWER-LANGUAGE.md) for the typed codecs
and their consistency tests. Search failure continues to mean not established,
not refuted.

The panel leads with a source-named comparison, for example `cell.value` with
available type `boolean` and required return type `true`. The report writer
resolves the goal term's actual variable slot through the source map; it does
not assume slot zero or invent an available type for a compound term. Full
context is a bordered table under a disclosure. Exact graph labels, native
terms and the proof-search budget remain under a separate technical disclosure.
This presentation describes the failed requirement, not a counterexample.
