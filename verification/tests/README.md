# Verification regressions

`make verify` runs the maintained source pipeline. Lean tests build alongside
its implementation in `lean/Verification/ExperimentState/`.

| Tests | Coverage |
|---|---|
| `stateful-source.js` / `stateful-source/basic.ts` | Real certificates, branches and shared continuations, exact singletons, source annotations, parameter contracts, incoming-edge refinements, missing/duplicate claims, lexical scope and input identities. |
| `stateful-cells.js`, `stateful-closures.js` | Allocation, alias writes, reads, captures, returned closures, inner claims and corrupted certificates. |
| `stateful-loops.js`, `stateful-loop-transfers.js` | Supplied loop invariants, back edges, nested scope, early returns, break and continue. |
| `source-claims.js`, `source-claim-export.js` | Producer-independent claims, conversion fidelity and source association. |
| `partial-claims.js` | Partial collections without recovery, optional keep-going quality and diagnostics. |
| `annotated-source.js`, `report-viewer.js`, `candidate-editor.js` | Source-preserving display, failure locations and independent candidate repair. |
| `unsupported.js` / `unsupported/` | Explicit source boundaries, rejected for the expected reason. |

The reader's supported example group lists files exercised by these source
suites. `cell-contracts.ts` tests exported type contracts separately and is not
advertised as a source-verifiable example. `partial-claims.ts` is a repair
exercise, in its own group.

The retired primitive verifier and its duplicate test harness are no longer
maintained. Applicable coverage (joins, source annotations, false/missing claims,
signatures and binding identity) is exercised by the current suites. Features
outside today's adapter are not silently counted as covered: `typeof`, numeric
equality, general top-level calls and mutable bindings have boundary fixtures;
active-name shadowing and code after unconditional transfer have explicit gate
tests. General primitive set difference and the old sampled numeric runtime
checks have no counterpart in the current null/boolean source fragment.

To promote a boundary example, add a positive integration test using real claims
and the independent consumer, then move it into the supported group and remove
its expected rejection. Promotion depends on implemented semantics and checking,
not merely on the parser accepting the syntax.
