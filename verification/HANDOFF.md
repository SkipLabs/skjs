# Verification handoff — 2026-09-08

## Starting point

This handoff covers the consolidation prepared after `da29f5dd` (missing
point-claim repair): diagnostic locations, whole-function candidate repair,
and retirement of the separate primitive verifier. Inspect `git status` for
subsequent work; this document is a checkpoint, not a live working-tree status. No SKJS inference code was
changed. The user requested one current calculus and pipeline, with no F0
compatibility requirement.

Read [README](README.md) for commands and source coverage, [DESIGN](DESIGN.md)
for the trust boundary, and [tests/README](tests/README.md) for retained coverage.

## Implementation boundaries

- `lean/Verification/ExperimentState/` is the maintained calculus, consumer and
  source adapter. Its directory name is historical; it is production code for
  this experiment. The retired `Calculus/`, `Verify`, `Lowering`, `SourceAst`,
  `JsonDecode` and their exclusive tests are deleted.
- `SourceEncoding.lean` contains primitive wire data and JSON helpers that the
  current adapter still needs. `Wire.mem` supports exact-translation lemmas;
  it is not another program semantics. Decodable numeric/string wire data is
  still rejected by `SourceTypes`. Do not confuse decodability with support.
- The parser has one behavior. `--stateful` is no longer needed or documented;
  the old named-top-level-call lowering branch is gone. The CLI retains the
  explicit request/source production and checking modes, not the old three-arg
  invocation. `make verify` is the maintained test command.
- `report-viewer/examples.js` defines picker groups. Default examples are covered
  by current source suites; partial collection is a separate repair exercise.
  Four fixtures in `tests/unsupported/` have expected-reason rejection tests.
  Promote one only with a positive source-to-consumer integration test.

## Report and editor contracts

`annotate-source.js` produces the manifest; `model.js` validates and adapts it;
`viewer.js` renders it. `candidate.js` contains pure draft operations, while
`editor.js` manages browser state and `serve.js` runs collection or checking.

Failure locations are diagnostic metadata outside the certified request:

| Kind | Association |
|---|---|
| `expression-obligation` | Exact expression span where checking stopped. |
| `edge-obligation` | Destination expression whose incoming environment was not justified. |
| `environment-obligation` | Statement-entry start offset. |
| `source-limitation` | Unsupported expression; conversion stopped before proof checking. |

Lean currently emits recognized diagnostic prefixes, which the annotator maps
to these fields. Change the emitter, parser, tests and format documentation
together if changing this protocol. Never interpret an internal graph label as
an expression-list index or present search failure as proof of falsity. Unknown
locations retain a function-level diagnostic. See [ANNOTATED-SOURCE](ANNOTATED-SOURCE.md).

Every applied edit invalidates prior results. Preview checks attachment; only
fresh verification establishes a result. The server verifies the source hash
and uses temporary candidate files without rerunning SKJS or writing source.
Original claims remain an immutable baseline, exported with the candidate.

`missingFunctions` and `missingSites` are parser-derived repair hints, not claims.
A missing function needs an explicit `{params, result}` contract, followed by
its required point claims. Parameter names/order come from source. Both raw SKJS
and normalized candidates are supported. A failed preview retains the draft and
must not advance the repair UI. The candidate regression restores a removed
function, verifies it, and rejects a false source return contract.

## Validation and development

Run `make verify` for extraction/report changes; it builds Lean and exercises
real exports, claim/evidence corruption, boundaries, partial export and editing.
Use `cd verification/lean && lake build` for Lean iteration. Repository-wide
SKJS `make test` is for checker implementation changes, not verifier-only work.

Before this handoff, the retired modules were removed and a **clean** Lean build
passed (93 jobs). The current default viewer example was freshly verified in a
separate browser tab: all 15 functions in `basic.ts` passed. The handoff pass also
passed the full `make verify` suite, including the whole-function repair regression
(producer and consumer checks), plus JavaScript syntax and whitespace checks.

The local viewer was restarted on `http://localhost:8732`. Asset edits require a
browser reload; server code changes require a process restart. Export candidate
edits before reloading, then import and reverify. Do not assume a tab's URL still
names the currently selected file: the picker currently does not rewrite it.

## Deferred work, not implemented

- Source-text editing, position tracking during typing, incremental invalidation.
  The editor changes claims against a fixed source snapshot only.
- A viewer build/version indicator or update notification. There is no live reload.
- Rich type editing and editing an existing function contract in place. A whole
  missing function can be added; point claims can be edited normally.
- Extending the source fragment (equality, strings/numbers, `typeof`, general
  calls, mutable bindings, generics). These require explicit design and tests;
  removing the old pipeline does not implement them.
- Proved source-to-graph preservation remains an optional design item. The current
  extraction boundary is reviewed and tested, not claimed to be proved sound
  with respect to JavaScript.

Keep these limitations explicit. No new agent coordination or background task
has been created; this file is the handoff record.

## Follow-up: primitive callback domains

Consolidation was committed as `7fa0d808`. The next fragment increment adds all
primitive unary domains/codomains without changing the calculus term language.
The source profile is now `stateful-source-75-v1`; regenerate old normalized
sidecars. `FunctionClaims.translate_exact` checks both domain and codomain.
Source-mode search uses `SourceRequest.searchLabels`; this is a heuristic only,
and consumers continue to check the complete graph and exact obligations.

`primitive-callbacks.js` covers raw and normalized certificates, contravariant
contracts, wrong arguments, and the captured-refinement witness. The original
SKJS counterexample is gated by unequal reference read/write types; a separately
weakened candidate fails at the stale read obligation. Do not conflate those
results. The immutable-snapshot counterpart verifies. Callback and counterexample
files are linked from the main README and included in the viewer groups.

Concurrent viewer addressing/navigation edits are another agent's work; they
were not part of this fragment increment. Inspect the working tree before
staging. The full verification suite passed with the fragment extension; targeted
normalized callback round-trip tests passed as well.
