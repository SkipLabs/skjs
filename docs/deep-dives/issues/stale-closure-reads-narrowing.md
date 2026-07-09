# Unsound: closure bodies read enclosing narrowings that are stale at invocation (read-in dual of #599)

Proposed labels: `soundness`, `bug`, `narrowing`. Related: #599 (its dual),
#597, #598.

## Summary

A closure body created inside a refined branch captures the *narrowed* type
of an enclosing local. If the local is reassigned before the closure runs,
the closure body's typing is stale. This is the **read-in** direction —
distinct from #599, which covers the **write-out** direction (closure
reassigns; enclosing code reads) and whose reproducer both SKJS and tsc
accept. For this direction tsc *rejects* (it re-widens captured-and-assigned
`let`s inside closure bodies, TS18047); SKJS accepts.

## Minimal reproduction (self-contained)

Reproduction: [`repros/stale-closure-read.ts`](repros/stale-closure-read.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/stale-closure-read.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS: **exit 0, zero diagnostics**.
- node: `TypeError: Cannot read properties of null (reading 'length')` —
  `x.length` is read from `null` in a position the checker typed via the
  stale `string` narrowing.
- tsc `--strict`: rejects, `TS18047: 'x' is possibly 'null'`.

## Field-level variant (covered by no invalidation-policy layer)

The same stale-read shape occurs for a narrowed *field* of a captured local:
a closure body reads `x.f` under the creation-time narrowing while `x.f` is
reassigned before the closure runs. Deep dive F's policy P3 re-widens
captured *locals* but not their narrowed *fields*, so no layer closes this.

Reproduction: [`repros/field-read-in-closure.ts`](repros/field-read-in-closure.ts)
— run `make check-file-in-docker
FILE=docs/deep-dives/issues/repros/field-read-in-closure.ts
BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

## Root cause

Closure bodies are checked against the enclosing scope chain's *current*
(narrowed) binding types (`Scope::maybeGetRef` walks the `up` chain,
`src/TypeCheckScope.sk`); no re-widening is applied for locals that are
assigned anywhere and captured.

## Relation to existing issues/PRs

#599 read in full: write-out direction only; its text notes both tools
accept its shape, and `tests/expect-error/unsound-refinement.ts` covers
cases #597/#598/#599 without any closure-body read. Not previously tracked.

## Suggested fix

tsc's discipline: inside closure bodies, captured `let`s that are assigned
anywhere use their declared (widened) type, not the flow-narrowed one.
(Fits as layer P3 of the policy in deep dive F.)

## Provenance

Deep dive F (`docs/deep-dives/refinement-invalidation.tex`, the
stale-closure-reads finding);
adversarially verified with runtime execution 2026-07-05. Main-paper
assumption rows: L-PURE / L-LOCAL boundary.
