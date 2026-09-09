# Obligation diagnostics (version 1)

This is explanatory metadata about an unsuccessful verification attempt, not
proof evidence and not a judgement that a source claim is false. The independent
certificate consumer and successful evidence formats are unchanged.

## Transport and identity

On a structured failure, the verifier emits its existing human-readable error,
then one line on stderr:

```text
obligation-diagnostic: {"version":1,...}
```

`verification/tools/obligation-diagnostic.js` reads the record without parsing the
human sentence. Unknown versions, malformed records, and duplicate records are
not interpreted. Failures that reach no calculus obligation carry human text and
an optional `location` instead of a record.
Absence of a structured record never changes a failure into success.

`annotate-source.js` preserves recognized records as `results[i].obligation` and
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
| `version` | `1`; independent of evidence/request versions. |
| `kind` | `node-typing`, `edge-coverage`, `expression-claim`, or `production-failure`. |
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

## Node and expression obligations

A `node-typing` record has:

- `source`: `{label, origin, node, claim}`. `node` includes the expression and
  continuation; `claim` includes its entry context and required expression type.
- `sequent`: the exact judgement attempted at that node.

An `expression-claim` record has `origin` and `sequent` directly. Its role may
be an expression claim, closure entry check, local annotation or closure result.
The kind identifies the obligation collection, not a claim of semantic blame.

`origin` is nullable. When present, it contains:

- `pos`: source span, in the parser's UTF-16 offsets.
- `role`: assigned where extraction creates the obligation.
- `environmentStart`: optional source statement-entry offset, only where known.

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
5. Preserve the existing first-failure and not-a-disproof wording, freshness
   rules, and fallback for failures without structured metadata.

No recursive proof-search trace, minimal failing premise, or complete dependency
graph is promised. Extraction/type-decoding/missing-claim failures and some
independent consumer failures still use the existing diagnostic path. An origin
does not identify every contributing source claim or prove any premise separately.
There are no retained mutable-heap observations. Future overloads and generics
should extend explicit obligation data rather than force them into
an `in / claim / out` triple or infer their roles in the viewer.

`tests/obligation-diagnostics.js` exercises the three partial repairs and full
repair of the return example, identical spans with different obligations,
selected maps on shared-destination branches, input fingerprints, and unsupported
record versions. It runs under `make verify-test`.

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

For `unavailable-type-claim`, [SkjsTypeClaims.sk](../src/SkjsTypeClaims.sk) emits:

| Reason | Emitted when |
| --- | --- |
| `unsupported-type` | A primitive or unit is outside the export format, an object occurs in a position that does not admit one, or a clause has no representable types. |
| `unsupported-object-branch` | An object branch fits neither the cell-record nor the function encoding, or the object has no branches. |
| `unexpanded-type` | An object still carries an unexpanded type. |
| `type-parameter` | A clause carries a universally quantified type parameter. |
| `union-of-clauses` | The type has more than one clause, outside the bounded encoding. |
| `unbound-inference-variable` | An isolated unconstrained inference variable has no binding in the function's substitution snapshot. |
| `constrained-inference-variable` | Inference variables cannot be followed as a single isolated unconstrained variable. |
| `fuel-exhausted` | Bounded type export exhausts its recursion fuel, independently of proof-search fuel. |

Representable object branches are exported as separate union atoms. Multiple
branches alone are not a refusal reason. An unsupported branch causes refusal
of the whole type rather than a partial export.

Current-content assertions in the supported cell profile now reach checked
obligations. Graph failures use `edge-coverage`, with destination origin role
`heap-observation`; `requiredKnowledge` at the destination identifies the actual
cell facts. Ordinary closure/compositional proofs use `expression-claim` with the
same origin role for uniform invariant justification. These are proof failures,
not exporter refusals. [Program typing](PROGRAM-TYPING.md#source-observation-checkpoints)
owns their interpretation.

`non-invariant-cell-contract` remains the one `source-limitation` reason the
report reader classifies. An unequal-contract error can still arise in an
ordinary type/signature or unsupported record union; standalone point
observations take the assertion path.

[Annotated-source tests](tests/annotated-source.js) check reason transport and
classification; [viewer tests](tests/report-viewer.js) cover known, unknown, and
absent reasons. [Source-claim export tests](tests/source-claim-export.js) check
that observations survive conversion and become proof obligations rather than
being silently erased.
