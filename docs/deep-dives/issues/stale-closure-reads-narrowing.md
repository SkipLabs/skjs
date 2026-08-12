# Unsound: a closure reads an enclosing narrowing after reassignment has invalidated it

Proposed labels: `soundness`, `bug`, `narrowing`. Related: #599,
#597, #598.

## Summary

A closure body created inside a refined branch captures the *narrowed* type
of an enclosing local. If the local is reassigned before the closure runs,
the closure body's typing is stale. This differs from #599: there the
closure performs the reassignment and enclosing code later reads the
binding, while here enclosing code reassigns the binding and the closure
later reads it. Both SKJS and tsc accept #599's reproducer; tsc rejects
this case because it re-widens captured-and-assigned `let` bindings inside
closure bodies (TS18047).

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
(narrowed) binding types (`Scope::maybeGetRefHelper` walks the `up`
chain, `src/TypeCheckScope.sk:62-75`); no re-widening is applied for
locals that are assigned anywhere and captured. The capture machinery
guards the *write* direction only: `Scope::set` checks a captured write
against the binding's declared type (`isThroughFunction`,
`src/TypeCheckScope.sk:115-132, 184-194`), but reads inside the closure
still see the creation-time narrowing.

## Relation to existing issues/PRs

#599 covers only writes in a closure followed by reads in enclosing code;
its text notes both tools accept that shape, and
`tests/expect-error/unsound-refinement.ts` covers
cases #597/#598/#599 without any closure-body read. Not previously tracked.

## Suggested fix

tsc's discipline: inside closure bodies, captured `let`s that are assigned
anywhere use their declared (widened) type, not the flow-narrowed one.
(Fits as layer P3 of the policy in deep dive F.)

## Provenance

Deep dive F (`docs/deep-dives/refinement-invalidation.tex`, the
stale-closure-reads finding);
adversarially verified with runtime execution 2026-07-05. Registry row:
L-STALE-READ (with L-PURE and L-LOCAL adjacent).
