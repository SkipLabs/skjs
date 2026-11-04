# Unsound: a captured write to an evolving binding is unchecked, and later reads keep the stale evolved type

Proposed labels: `soundness`, `bug`, `narrowing`, `tsc-parity`.

## Summary

Bindings declared as bare `let x = null` (or `undefined`) evolve: they
carry no annotation and no widening initializer, so the captured-write
check that protects every other binding (row L-CAPT) exempts them. A
closure can therefore write any value into the binding, while reads
after the closure runs still use the evolved type from the declaration
site: the program below binds `"s"` at type `null`. tsc accepts the
same program because its evolving `any` has the same limitation. SKJS
therefore matches TypeScript here, but the acceptance remains unsound on
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

Tracked by #840. Its class-instance witness first evolves the local to a
concrete `MyNode` type and then performs an incompatible captured write.
The witness here covers the earlier phase: the captured write introduces
the binding's first non-null value while the outer scope continues to
read the initializer type. Together they show that the problem is both
an unchecked-write exception and a failure to incorporate escaping
writes into later reads.

The exemption is deliberate tsc parity (deep dive F's evolving-binding
exception under row L-CAPT). This report splits the unsound case into
its own row, L-CAPT-EVOLVE, so the proved L-CAPT row can be scoped
honestly to annotated and initializer-inferred bindings. It is also
distinct from L-STALE-READ: there a closure reads an enclosing narrowing
that has become stale; here the write itself is exempt and the bad read
occurs later in the enclosing scope.

## Suggested fix

Track captured writes into evolving bindings in the evolved union, then
use that union for later reads or call-site havoc. In this witness the
post-call type must include `null | string`, rejecting `const n: null =
x` without forbidding closures from initializing an evolving binding.

Sealing at first capture, as proposed in #840, handles the case where a
binding has already evolved to a concrete type. It is insufficient by
itself here: sealing to `null` rejects legitimate closure-based
initialization, while declining to seal leaves this witness unsound.

## Provenance

Deep dive F's exception for evolving bindings, promoted to a row with an executed
witness by the adversarial referee pass
(`docs/adversarial-review-findings-2026-08-11.md`, finding 3).
