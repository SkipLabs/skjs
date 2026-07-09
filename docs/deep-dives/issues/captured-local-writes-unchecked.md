# Unsound: assignments to captured locals inside lambdas are never checked against the declared type

Proposed labels: `soundness`, `bug`. Priority: **high** — arbitrary cross-type
confusion, no refinement involved, silent.

## Summary

An assignment to an enclosing-function local from inside a lambda body is not
checked against the binding's declared type at all. Any value of any type can
be written into any captured `let`. This is distinct from the tracked
stale-narrowing family (#597/#598/#599): those bugs concern refinements not
being invalidated by writes that are *within* the declared type; here the
write itself is type-incorrect and undiagnosed.

## Minimal reproduction (self-contained)

Reproduction: [`repros/captured-local-write.ts`](repros/captured-local-write.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/captured-local-write.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS (`make check-file-in-docker`): **exit 0, zero
  diagnostics**. Annotating the lambda (`const g: () => void = ...`) changes
  nothing.
- node: prints `undefined` — `x` holds the number `5` in a `string`-typed
  position.
- tsc `--strict`: rejects, `TS2322: Type 'number' is not assignable to type
  'string'`.

## Root cause

`Scope::set` writes to the lambda's own frame; its subtype guard fires only
across loop frames (`src/TypeCheckScope.sk`), and `anonFunction` discards the
lambda frame without a merge or a check against the captured binding's
declared type (`src/TypeCheckExpr.sk`, lambda body checking ~2850).

## Relation to existing issues/PRs

Verified distinct from #597, #598, #599, #585 and PR #600 (all read in full):
those cover refinement invalidation by *type-correct* writes. The closest
local test is `tests/expect-error/unsound-refinement.ts` case 3 (#599), where
the closure writes `null` to a `string | null` local and the bug is the stale
post-call narrowing. This issue does not require any narrowing: the closure
write `x = 5` should be rejected against the declared `string` type at the
write site. Not previously tracked.

## Suggested fix

Check assignments to captured (out-of-frame) locals against the binding's
declared (widened) type at the write site — the same check that applies to
in-frame assignments.

## Provenance

Deep dive F (`docs/deep-dives/refinement-invalidation.tex`, finding L-CAPT);
adversarially verified with runtime execution 2026-07-05. Main-paper
assumption row: proposed L-CAPT (`VIOLATED`).
