# Callables

Source examples for callable contracts, checked through the existing parser,
SKJS claim exporter, certificate producer, independent consumer, and reports.
They have their own **Callables** group in the corpus and report viewer.

Add coverage for a distinct semantic obligation or an interaction that could
fail even when its components pass separately. Minor syntax variations alone
do not warrant another example. If a standalone Lean test takes too long to
develop or check, defer it until the case is expressible through the pipeline.

| Example in [unions.ts](unions.ts) | What it establishes |
| --- | --- |
| `guardedCallableUnion` | A null guard permits calling either remaining signature and preserves both possible results. |
| `andGuardedCallable` | `&&` calls only the non-null function; its true result does not erase the skipped false result. |
| `orGuardedCallable` | `||` skips the call for null, preserving true alongside the callable's false result. |
| `coalescedCallable` | Null and undefined select a fallback function before invocation; either callable can supply the result. |
| `capturedGuardedCallable` | A returned closure retains the immutable capture's non-null refinement and both callable alternatives after the branch ends. |
| `aliasedCallableSelection` | A selected local alias retains both callable alternatives through a nested closure; its callability does not transfer to the original nullable input. |
| `sharedCallableDomain` | A call must fit the shared argument domain of Boolean-accepting and true-only alternatives, while retaining both possible results. |
| `branchLocalCallableDomains` | Branch-refined Boolean arguments satisfy different callable domains; neither branch facts nor singleton results can be transferred to the other branch. |
| `callableArgumentWrite` | An assignment used as a call argument checks both storage and parameter contracts; its false RHS admits an explicitly refined false-only callable view. |
| `nestedCallableArgumentWrite` | A write inside a closure's call argument preserves the captured receiver and named RHS through temporary bindings; a same-typed capture cannot replace the parameter in the evidence. |

[callables.mts](../callables.mts) checks the original claims and rejects forged
claims and reused evidence. It also retains report round-trip and independent
report-verification coverage for these examples. The runner builds this fixture
alongside the other source fixtures in its shared container.

Run `make verify-test` for the suites or `make verify-examples` for the corpus.
`make verify` runs both. Core semantic regressions remain in
`lean/Verification/ExperimentState/`, including `SourceCallableUnionTests.lean`.

Pending pipeline coverage: call one factory twice, with each invocation allocating
a private Boolean cell and returning a closure that writes its argument and
returns the old contents. Starting from false, calls `first(true)`,
`second(false)`, `first(false)` should return false, false, true. A control with
the cell allocated outside the factory should return false, true, false despite
distinct returned closure identities. This combines fresh allocation, escaping
capture, and mutation; identity-only and single-capture tests do not establish
instance isolation. Add it when local closure factories with callable result
contracts are supported by the source pipeline. It is not current coverage.

That module also checks unions of overloaded functions using explicit normalized
source claims. Null and Boolean arguments select different signatures in each
alternative; narrowing the joined result or omitting an alternative's compatible
signature fails. These cases are not advertised as verified SKJS exports:
SKJS currently collapses incomparable arrow intersections to `never`, as recorded
in the [intersection finding](../skjs-incomplete/arrow-intersection.ts).

For `callableArgumentWrite`, the original SKJS assignment claim is Boolean.
The suite separately verifies an explicit false-result refinement with fresh
evidence; it does not count that refinement as an original producer claim.
