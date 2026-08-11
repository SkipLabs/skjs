# Unsound: a narrowing carried into a loop survives the back edge, so iteration 2 reads a stale type

Proposed labels: `soundness`, `bug`, `narrowing`.

## Summary

A narrowing established before a loop is not invalidated across the
loop's back edge. `Scope::set` applies exactly one check per write, in
order annotation → capture → loop: for an *annotated* binding, a write
reached through a loop frame is checked only against the declared type,
and the loop-entry (possibly narrowed) type is never consulted. The loop
body is checked once under the pre-loop narrowing, so a second iteration
reads the binding at the stale narrowed type while the store holds a
value the first iteration wrote — no call, closure, or alias involved.
For *un-annotated* bindings the through-loop check does fire and the
shape is rejected.

## Minimal reproduction (self-contained)

Reproduction: [`repros/loop-carried-narrowing-stale.ts`](repros/loop-carried-narrowing-stale.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/loop-carried-narrowing-stale.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS: **exit 0, zero diagnostics**.
- node: with `cond()` returning true twice, the second iteration prints
  `null` from `s: string` — a `string`-typed binding holds `null`.
- tsc `--strict`: rejects, `TS2322: Type 'string | null' is not
  assignable to type 'string'` at the `const s: string = x` read (tsc
  re-widens loop-assigned bindings at loop entry).

## Root cause

`Scope::set`'s three checks are mutually exclusive in order
annotation → capture → loop (`src/TypeCheckScope.sk:178-197`): the
annotation arm (`isAnnotated`, checks against `declaredType`) preempts
the through-loop arm (checks against the loop-entry type `upRef.type`),
so annotated bindings never receive the back-edge guard. Iteration-2
reads are justified only if back-edge writes preserve the loop-entry
type, which the declared-type check does not ensure.

## Relation to existing issues/PRs

Distinct from the L-PURE family (#597/#599: call- and closure-mediated
staleness) and from #598 (field write in a refined branch): this shape
is pure intra-function loop flow with a plain local. The pinned cases in
`tests/expect-error/unsound-refinement.ts` involve no loop. Not
previously tracked.

## Suggested fix

Deep dive F's policy layer P1: either extend the through-loop check to
annotated bindings — a back-edge write is checked against the loop-entry
type *in addition to* the declared type — or, matching tsc, re-widen at
loop entry the narrowings of every binding the loop body assigns.

## Provenance

Deep dive F (`docs/deep-dives/refinement-invalidation.tex`,
Finding "Loop-carried narrowings are not invalidated"); adversarially
verified with runtime execution 2026-08-06. Registry row:
L-LOOP-CARRIED.
