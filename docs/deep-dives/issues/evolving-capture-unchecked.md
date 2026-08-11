# Unsound: a captured write to an evolving binding is unchecked, and later reads keep the stale evolved type

Proposed labels: `soundness`, `bug`, `narrowing`, `tsc-parity`.

## Summary

Bindings declared as bare `let x = null` (or `undefined`) evolve: they
carry no annotation and no widening initializer, so the captured-write
check that protects every other binding (row L-CAPT) exempts them. A
closure can therefore write any value into the binding, while reads
after the closure runs still use the evolved type from the declaration
site: the program below binds `"s"` at type `null`. tsc accepts the
same program — its evolving `any` has the same blind spot — so this is
a parity hole, but a hole nonetheless: the acceptance is unsound on
Node.

## Minimal reproduction (self-contained)

Reproduction: [`repros/evolving-capture-unchecked.ts`](repros/evolving-capture-unchecked.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/evolving-capture-unchecked.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS: **exit 0, zero diagnostics**.
- node: prints `n = s` — a `null`-typed binding holds a string.
- tsc `--strict`: **accepts** (evolving `any`; closure assignments are
  not tracked by its control-flow analysis) — parity.

## Root cause

`Scope::set`'s escaping-write check applies the widened inferred type to
un-annotated bindings, except those recognized as evolving
(`getSingleVar` on a bare `null`/`undefined` initializer,
`src/TypeCheckScope.sk:178-197`): their writes are exempt, and reads do
not incorporate values written through captures.

## Relation to existing issues/PRs

The exemption is deliberate tsc parity (deep dive F's evolving-binding
exception under row L-CAPT). This draft splits the unsound facet into
its own row, L-CAPT-EVOLVE, so the proved L-CAPT row can be scoped
honestly to annotated and initializer-inferred bindings. Sibling of the
stale-read row L-STALE-READ (a different mechanism: there the write is
legal and the *read* is stale; here the write itself is unchecked).

## Suggested fix

Track captured writes into evolving bindings in the evolved union (so
later reads see `null | string`), or check them against the evolved
union at the write site. Either preserves tsc's ergonomics for the
common initialization pattern while closing the type confusion.

## Provenance

Deep dive F's carve-out paragraph, promoted to a row with an executed
witness by the adversarial referee pass
(`docs/adversarial-review-findings-2026-08-11.md`, finding 3).
