# Verification regressions

`make verify` runs the maintained source pipeline. Lean tests build alongside
its implementation in `lean/Verification/ExperimentState/`.

| Tests | Coverage |
|---|---|
| `stateful-source.js` / `stateful-source/basic.ts` | Real certificates, branches and shared continuations, exact singletons, source annotations, parameter contracts, incoming-edge refinements, missing/duplicate claims, lexical scope and input identities. |
| `stateful-cells.js`, `stateful-closures.js` | Allocation, alias writes, reads, captures, returned closures, inner claims and corrupted certificates. |
| `stateful-loops.js`, `stateful-loop-transfers.js` | Supplied loop invariants, back edges, nested scope, early returns, break and continue. |
| `primitive-callbacks.js` | Primitive domains, contravariant call contracts, returned writers, a stale captured-refinement witness and a verified immutable-snapshot counterpart. |
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

`negation.js` checks Boolean negation and reversed immutable refinements in branches, closures and loops, including forged claims and an effectful operand.

Producer examples are separated by the direction of the failure:

- [`skjs-unsound/`](skjs-unsound/README.md): SKJS accepts a program with a runtime type counterexample.
- [`skjs-incomplete/`](skjs-incomplete/README.md): SKJS rejects a safe program whose repaired claims the verifier establishes.

`partial-claims.ts` remains a separate collection/repair exercise; a producer
rejection alone does not establish incompleteness.

Each example function has a doc comment explaining the behavior or proof
obligation it illustrates. Keep these comments alongside new examples. For
producer failures, state the expected runtime behavior and the exact claim repair
or rejection being tested; for unsupported examples, distinguish the adapter's
limitation from a soundness result. Loop examples should say when termination is
not established. Comments are part of the displayed source, so the tests always
regenerate claims rather than reuse offsets from an older source version.

`null-tests.js` covers strict null comparisons, both operand orders, callbacks,
effectful operands and independent evidence. `unsupported/null-guard.ts` is a
separate graph-refinement limitation checked against real SKJS claims by that
suite; the other unsupported fixtures are checked at their syntax/type gates.
