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
| `selectedCallableAfterMutation` | A selected callable remains fixed while a shared-cell write changes its live capture. A JavaScript witness distinguishes live from snapshot behavior, and a same-typed callee substitution needs fresh evidence. |
| `callbackProbeDoesNotNarrow` | A Boolean-returning probe has no type-predicate contract: its true result cannot narrow the captured callback in the caller, whose own null guard remains required. |
| `ambiguousCaptureGuard` | A successful disjunction may be justified by a separate Boolean flag; the returned closure must retain the nullable capture and guard it itself. The tsc suite checks both alternatives survive. |
| `compoundAbsenceCapture` | A returning null-or-undefined guard must exclude both tags before closure creation. Both producers verify it, and the tsc suite checks both exclusions. |
| `twoAbsenceCapture` | Eliminating undefined must retain null in a returned closure capture; its inner null guard is still needed. Both producers verify it; the tsc suite checks that undefined is removed while null remains. |
| `laterGuardedCallback` | A guard after closure creation cannot refine its earlier capture; the closure needs its own guard. The tsc suite checks the pre-guard nullable claim, and a reversed inner guard fails independently of the later outer guard. |
| `escapedLocalCallback` | A returned closure captures a guarded nullable const whose declaration is wider than its initializer. Both producers verify it; the tsc suite checks that its callee claim retains the creation-time guard. |
| `distinctNullableCallbacks` | Same-typed local callbacks require independent null guards; the tsc suite checks that guarding the first leaves the second nullable, then each own guard permits its call. |
| `nullableFactoryResult` | A factory result can mix a callable with null; both alternatives survive the factory contract and invocation, and the caller must guard the returned value before calling it. |
| `returnedCallableDomain` | Factory branches with Boolean and true-only callable domains both implement a true-only result contract; neither the nested result claim nor a later call can widen that shared domain. |
| `branchReturnedCapture` | A factory returns different closures from a null-test branch; the escaping closure retains its own factory argument's refinement, which cannot transfer to the nullable caller capture. |
| `nestedCallableArgumentWrite` | A write inside a closure's call argument preserves the captured receiver and named RHS through temporary bindings; a same-typed capture cannot replace the parameter in the evidence. |

[callables.mts](../callables.mts) checks original SKJS claims, forged claims,
reused evidence and report round trips. [tsc-claims.mts](../tsc-claims.mts) checks
the TypeScript producer, including the capture refinements identified above.
Both producers use the same extraction and independent consumer.

For `callableArgumentWrite`, SKJS exports Boolean for the assignment. A separate
false-result refinement verifies with fresh evidence; it is an explicit candidate,
not an original producer claim. Under `nullableFactoryResult`'s nullable context,
the tsc producer uses the lambda's own expression type, then checks that arrow
against the full return contract.

[factories.ts](factories.ts) contrasts factories allocating a private cell per
invocation with a control sharing a cell outside the factory.
[callable-factories.mts](../callable-factories.mts) rejects a narrowed returned
closure result with both fresh and reused evidence. Its JavaScript witness checks
that `first(true)`, `second(false)`, `first(false)` return false/false/true with
private cells and false/true/false with the shared cell. A passive observer records
the intermediate results; the unmodified function's result is checked too.

[arguments.ts](arguments.ts) covers a stateful callback passed to an invoker and
`escapedCallbackArgument`, where that callback enters a wrapper factory, escapes
as a captured parameter, and returns through another invoker. An intervening cell
write distinguishes execution-time reads from creation-time snapshots.
[callable-arguments.mts](../callable-arguments.mts) rejects incompatible callback
domains and results, and checks the escaping wrapper's JavaScript result for both
seeds. Both producers' certificates for factories and arguments are independently
checked.

JavaScript witnesses establish observations separate from the Boolean typing
certificates. They do not prove that extracted Lean programs execute equivalently;
those execution checks remain deferred unless a concrete discrepancy warrants
investigation. The [protocol](../../REQUEST-PROTOCOL.md#expression-closures-and-calls)
owns callable signature restrictions.

Core semantic regressions remain in `lean/Verification/ExperimentState/`.
`SourceCallableUnionTests.lean` isolates union decoding, operand-slot lowering
and overloaded union calls with explicit claims. Null and Boolean arguments
select different signatures in each alternative; narrowing the joined result or
omitting an alternative's compatible signature fails. These are not verified SKJS
exports: SKJS collapses incomparable arrow intersections to `never`, as recorded
in the [intersection finding](../skjs-incomplete/arrow-intersection.ts).
Guard polarity and guarded results are covered by the source suites; recursive
callable bags and recursive invocation remain distinct model obligations.

Run `make verify-test` for suites or `make verify-examples` for the corpus;
`make verify` runs both. The [test index](../README.md) describes suite ownership.

[cells.ts](cells.ts) and [callable-cells.mts](../callable-cells.mts) cover mutable
callback storage. `replacedCallback` distinguishes a saved function value from a
later cell read after replacement. `recursiveCallback` installs a callback that
reads and invokes itself through the cell, then reaches a base case. Both producers
verify the original claims with independent consumption. Forged read/write domains
and replacement result contracts fail; JavaScript witnesses check both seeds.
These examples require no new calculus constructor or typing rule.

[thunks.ts](thunks.ts) and [callable-thunks.mts](../callable-thunks.mts) cover
zero-argument creation and invocation: a returned thunk reads a cell after a
write, and a saved thunk remains distinct from its replacement. Both producers'
claims are independently checked. Forged domains/results fail, and the callable
argument suite checks that omission does not satisfy a required callback parameter.
JavaScript witnesses check delayed reads and replacement for both seeds.

[arity.ts](arity.ts) is a **source-boundary fixture**, not a supported corpus
example. It requires callee evaluation first, argument evaluation left to right,
and body execution afterward. [callable-arity.mts](../callable-arity.mts) checks
its JavaScript result and controls that reverse argument order or delay callee
evaluation; the tsc suite retains its expected source-gate rejection. The
[model preparation interface](../../SEMANTICS.md#argument-list-preparation)
establishes operand sequencing separately from the remaining invocation work.
