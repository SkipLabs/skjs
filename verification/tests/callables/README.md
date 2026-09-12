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
| `nullableFactoryResult` | A factory result can mix a callable with null; both alternatives survive the factory contract and invocation, and the caller must guard the returned value before calling it. |
| `returnedCallableDomain` | Factory branches with Boolean and true-only callable domains both implement a true-only result contract; neither the nested result claim nor a later call can widen that shared domain. |
| `branchReturnedCapture` | A factory returns different closures from a null-test branch; the escaping closure retains its own factory argument's refinement, which cannot transfer to the nullable caller capture. |
| `nestedCallableArgumentWrite` | A write inside a closure's call argument preserves the captured receiver and named RHS through temporary bindings; a same-typed capture cannot replace the parameter in the evidence. |

[callables.mts](../callables.mts) checks the original claims and rejects forged
claims and reused evidence. It also retains report round-trip and independent
report-verification coverage for these examples. The runner builds this fixture
alongside the other source fixtures in its shared container.

Run `make verify-test` for the suites or `make verify-examples` for the corpus.
`make verify` runs both. Core semantic regressions remain in
`lean/Verification/ExperimentState/`, including `SourceCallableUnionTests.lean`.

[factories.ts](factories.ts) exercises two calls to a factory that allocates a
private Boolean cell and returns a closure that writes its argument and returns
the old contents. A control hoists the cell outside the factory, so the returned
closures share state. Both original SKJS exports produce certificates checked
by the independent consumer in [callable-factories.mts](../callable-factories.mts).
The TypeScript producer also verifies both factories, with independent consumption
in [tsc-claims.mts](../tsc-claims.mts). They appear in the Callables corpus and
report viewer alongside the union examples.
Narrowing the returned closure's result to false fails both fresh production and
reuse of the original evidence.

These Boolean contracts establish type safety, not the exact instance-isolation
observations: calls `first(true)`, `second(false)`, `first(false)` should return
false, false, true for private cells and false, true, false for the shared cell.
The suite now checks those exact observations with a JavaScript runtime witness,
inserting a passive observer immediately before the outer return. It also runs
the unmodified function and checks its Boolean result. This does not prove that
the extracted Lean machine has the same execution: that semantic execution
check remains deferred. Callable arguments and
record-valued results remain outside this source fragment.

That module also checks unions of overloaded functions using explicit normalized
source claims. Null and Boolean arguments select different signatures in each
alternative; narrowing the joined result or omitting an alternative's compatible
signature fails. These cases are not advertised as verified SKJS exports:
SKJS currently collapses incomparable arrow intersections to `never`, as recorded
in the [intersection finding](../skjs-incomplete/arrow-intersection.ts).

For `callableArgumentWrite`, the original SKJS assignment claim is Boolean.
The suite separately verifies an explicit false-result refinement with fresh
evidence; it does not count that refinement as an original producer claim.

For `nullableFactoryResult`, SKJS's original claims verify. The tsc producer
currently gives the returned lambda its nullable contextual type, while source
extraction requires a lambda claim to name an arrow. The TypeScript claim suite
records this failure; tsc itself accepts the program. This is a producer/adapter
limitation, not evidence of unsoundness in the example.
