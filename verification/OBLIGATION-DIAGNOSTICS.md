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
not interpreted. Legacy failures still have human text and optional `location`.
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

Current roles are `node-typing`, `return-contract`, `binding-annotation`,
`expression-claim`, `closure-entry`, and `closure-result`. The generic
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

The destination requirement is `destination.claim.context`. Both branch edges
can have the same destination label and different maps; `edgeIndex` identifies
which obligation failed. Refinement must be interpreted together with the
observation, not as ordinary subtyping of `available` alone.

## Visualization handoff

The protocol and report adapter are implemented; the viewer is intentionally
unchanged. The visualization agent should:

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
There are no retained mutable-heap observations. Future tag dispatch, overloads,
and generics should extend explicit obligation data rather than force them into
an `in / claim / out` triple or infer their roles in the viewer.

`tests/obligation-diagnostics.js` exercises the three partial repairs and full
repair of the return example, identical spans with different obligations,
selected maps on shared-destination branches, input fingerprints, and unsupported
record versions. It runs under `make verify-test`.
