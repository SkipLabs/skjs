# Callables

Source examples for callable contracts, checked through the existing parser,
SKJS claim exporter, certificate producer, independent consumer, and reports.
They have their own **Callables** group in the corpus and report viewer.

| Example in [unions.ts](unions.ts) | What it establishes |
| --- | --- |
| `guardedCallableUnion` | A null guard permits calling either remaining signature and preserves both possible results. |
| `coalescedCallable` | Null and undefined select a fallback function before invocation; either callable can supply the result. |

[callables.mts](../callables.mts) checks the original claims and rejects forged
claims and reused evidence. It also retains report round-trip and independent
report-verification coverage for these examples. The runner builds this fixture
alongside the other source fixtures in its shared container.

Run `make verify-test` for the suites or `make verify-examples` for the corpus.
`make verify` runs both. Core semantic regressions remain in
`lean/Verification/ExperimentState/`, including `SourceCallableUnionTests.lean`.
