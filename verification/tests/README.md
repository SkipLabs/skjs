# Verification regressions

`make verify-test` runs the maintained pipeline regressions. Lean tests build
alongside its implementation in `lean/Verification/ExperimentState/`.
`make verify-examples` separately reports per-function outcomes on original SKJS
and tsc claims for the viewer's corpus, without the repairs or corruptions used in tests.
`make verify` runs both, with separate summaries.

| Tests | Coverage |
|---|---|
| `stateful-source.mts` / `stateful-source/basic.ts` | Real certificates, branches and shared continuations, exact singletons, source annotations, parameter contracts, incoming-edge refinements, missing/duplicate claims, lexical scope and input identities. |
| `stateful-cells.mts`, `stateful-closures.mts` | Allocation, alias writes, reads, captures, returned closures, inner claims and corrupted certificates. |
| `callables.mts`, `callable-factories.mts`, `callable-arguments.mts`, `callable-cells.mts`, `callable-thunks.mts` / [`callables/`](callables/README.md) | Callable unions, factories, higher-order arguments and mutable callback cells and zero-argument thunks; exact contracts, forged claims, independent consumption, runtime witnesses and report round trips. |
| `callable-arity.mts` / `callables/arity.ts` | JavaScript evaluation-order witness for the next arity milestone; the tsc suite records the current source boundary. |
| `stateful-loops.mts`, `stateful-loop-transfers.mts` | Supplied loop invariants, back edges, nested scope, early returns, break and continue. |
| `null-tests.mts` | Null predicates, coalescing, logical expressions and compound guard edges; required claims, merge rejection, effect order, loop back edges and a direct-write stale-refinement counterexample. |
| `write-observations.mts` | Post-write precision and negated stale-refinement witnesses: SKJS/TypeScript results, execution, source shape for the Lean observation proof, and the current checker limitation. |
| `primitive-callbacks.mts` | Primitive domains, contravariant call contracts, returned writers, a stale captured-refinement witness and a verified immutable-snapshot counterpart. |
| `source-claims.mts`, `source-claim-export.mts` | Producer-independent claims, conversion fidelity and source association. |
| `skjs-operations.mts` | Closed subtype and expansion judgments from a real SKJS export; missing/extra fields and unsound inclusions are unproved, not accepted. |
| `inferred-replacement.mts` / `export-snapshots/inferred-replacement.ts` | Saved-substitution export of inferred replacement contracts, mutable object captures, and distinct nested local/field observations. Both producers verify; a forged local-content claim cannot borrow the field's snapshot. |
| `nullish-assignment.mts` / `stateful-source/nullish-assignment.ts` | Local `??=`: both producers and independent consumers; forged reads/results and out-of-contract writes are rejected. Nested assignments, skipped RHS effects and escaping captures complement a Lean graph-shape guard for read-once and correct branch selection. |
| `declaration-list.mts` / `stateful-source/declaration-list.ts` | Several bindings in one `const` or `let`: one statement entry, left-to-right initializers in the scope the earlier bindings extend, one cell per `let` binding, a later initializer's write to an earlier cell, and inferred contracts read at the following entry. Both producers verify; reversed declarators, a forged entry after the list, a stale or dropped initializer effect and cross-cell contents are refused; lists in closure bodies and uninitialized or destructured declarators stay gated; source executions agree, and `DeclarationListTests.lean` traces the lowered program itself: one cell per declarator in source order, the write to the first leaving the second as it was. |
| `object-patterns.mts` / `stateful-source/object-patterns.ts` | Object patterns on `const`: the initializer once, properties read in order, a default only on an undefined read, renamed bindings, and a binding that survives a later field write. Both producers verify; a singleton forged onto a defaulted or written binding, a dropped default and an unnamed field are refused; `let` patterns, lists beside a pattern, nesting, rest, empty patterns and closure-body patterns stay gated; source executions agree, and `ObjectPatternTests.lean` traces the lowered program's ordered defaults. |
| `casts.mts` / `stateful-source/casts.ts` | Type assertions (`as`, `satisfies`, `!`) as the operand's value retyped at the assertion's own claim. Both producers verify; removing the guard beneath an assertion, forging its claim, and an annotation the operand does not meet are refused; angle-bracket assertions stay gated; executions agree. |
| `distinct-cells.mts` / `stateful-source/distinct-cells.ts`, `distinct-cells-aliased.ts` | Distinct-location links: a private cell is fresh, so a write to it keeps a guard's fact about a parameter's field; two parameters may alias, so a write through one forgets the other's. A forged SKJS claim keeping it is refused, and so is TypeScript's claim on the second file, which TypeScript accepts, SKJS rejects, and which returns null as a number when called with one object twice. `HeapExpressionTests.lean` pins the link rules. |
| `singleton-operands.mts` / `stateful-source/singleton-operands.ts`, `singleton-operands-call.ts` | A strict comparison against an effect-free operand whose claimed type is a singleton, a name or a field read, refines the tested read on the right arm; the wrong arm's refinement and a broadened operand claim are refused, and so is TypeScript's claim on the second file, where the operand is a call that may write the tested cell. |
| `computed-keys.mts` / `stateful-source/computed-keys.ts` | Element access: the receiver, then the key, then the field the key's claimed string singleton names, for reads and writes; a broader or different key claim is refused, and a ternary's assignment in the key is a graph write the right side sees. |
| `arithmetic.mts` / `stateful-source/arithmetic.ts`, `arithmetic-strings.ts` | Arithmetic on numbers yields the number family; compound assignments and increments evaluate their target once and read at the storage contract, a postfix increment being the old value. An operand claimed as possibly null, a singleton result claim, and string concatenation are refused. |
| `logical-assignments.mts` / `stateful-source/logical-assignments.ts`, `logical-assignments-number.ts` | `??=`, `\|\|=` and `&&=` on fields and elements: the target's parts once, its value read, the right side written only on the writing arm. The kept arm is the value read; `\|\|= true` and `&&= false` establish their singletons; a number target, which TypeScript accepts and SKJS rejects, is refused. |
| `mutable-locals.mts` / `stateful-source/mutable-locals.ts` | Private-cell lowering of annotated `let`: captures, snapshots (including a TS singleton SKJS loses), assignment results, guards and nullish fallback. Forged or missing entry claims, stale contents, cell-identity guard confusion, invalid writes and shadowing are refused. Independent certificate consumption and source executions check the lowering boundary. |
| `stateful-source/mutable-locals-numeric.ts` | Numbers as the storage contract of a mutable local and in a closure's signature; the literal claimed at the family rather than its own singleton; and an inferred binding whose contract the producer supplies. Corpus-only: the corpus policy is its regression test. |
| `stateful-source/mutable-locals-guard.ts` | The recorded boundary: a guard does not refine a read of a mutable local. Expected not to verify, in its own file so it does not carry its siblings' verdicts down. |
| `numbers.mts` / `stateful-source/numbers.ts` | Numbers as opaque values: the family, its literal singletons and the one inclusion between them. Widening a singleton result, narrowing a family result, confusing two literals, and reading a number as a boolean are all rejected; `1.0` and `1` are one singleton. |
| `strings.mts` / `stateful-source/strings.ts` | Strings as opaque values: the family, its literal singletons, the one inclusion between them, and equality with a literal. Both producers verify; widening a singleton result, narrowing a family result, confusing two literals, reading a string as a number or Boolean, and deciding a broad string's negative arm are all rejected. `StringEqualityTests.lean` checks the equality tag on slices and observations. |
| `generic-source.mts` / `stateful-source/generic-identity.ts` | Source extraction of rigid `id<T>(x: T): T { return x }`; returning `true` is rejected; an unused distinct type parameter is admitted. |
| `generic-aliases.mts` / `stateful-source/generic-aliases.ts` | Source extraction of `type Id<T> = T` and `type Box<T> = { value: T }`; a non-identity body, an unknown alias, and extra type parameters are rejected. |
| `generic-extends.mts` / `stateful-source/generic-extends.ts` | `T extends boolean` as `T ≤ boolean`; returning `x` at boolean is accepted, returning `true` as `T` is not. |
| `generic-bodies.mts` / `stateful-source/generic-bodies.ts` | Generic variable-copy bodies with distinct parameters and dependent bound chains. Mutated sources/claims reject reverse or missing bounds, conflated parameters, cycles and missing annotations; successful requests also pass the certificate consumer. Dependent-parameter cases use unedited SKJS exports. Cross-producer rigid encodings and native-to-neutral evidence consumption are checked. Body-claim edits, missing/extra sites and reused certificates are checked; valid weakening succeeds and invalid edits carry viewer locations. |
| `partial-claims.mts` | Partial collections without recovery, optional keep-going quality and diagnostics. |
| `annotated-source.mts`, `report-viewer.mts`, `candidate-editor.mts` | Source-preserving display, failure locations and independent candidate repair. |
| `obligation-diagnostics.mts` | Distinct obligations sharing a return span, claim repair combinations, selected edge mappings, records the reader must refuse and report identity. |
| `unsupported.mts` / `unsupported/` | Explicit source boundaries, rejected for the expected reason. |

The reader's supported example group lists files exercised by these source
suites. `cell-contracts.ts` tests exported type contracts separately and is not
advertised as a source-verifiable example. `partial-claims.ts` is a repair
exercise, in its own group.

Features outside today's adapter have explicit rejection coverage: `typeof`,
numeric equality, general top-level calls and mutable bindings have boundary
fixtures; active-name shadowing and code after unconditional transfer have gate
tests. These tests establish the boundary, not support for the feature.

To promote a boundary example, add a positive integration test using real claims
and the independent consumer, then move it into the supported group and remove
its expected rejection. Promotion depends on implemented semantics and checking,
not merely on the parser accepting the syntax.

`negation.mts` checks Boolean negation and reversed immutable refinements in branches, closures and loops, including forged claims and an effectful operand.

Producer examples are separated by the direction of the failure:

- [`skjs-unsound/`](skjs-unsound/README.md): SKJS accepts a program with a runtime type counterexample.
- [`skjs-incomplete/`](skjs-incomplete/README.md): SKJS rejects a safe program; each entry distinguishes accepted repaired claims from model-only proofs or remaining verifier limits.

`partial-claims.ts` remains a separate collection/repair exercise; a producer
rejection alone does not establish incompleteness.

Each example function has a doc comment explaining the behavior or proof
obligation it illustrates. Keep these comments alongside new examples. For
producer failures, state the expected runtime behavior and the exact claim repair
or rejection being tested; for unsupported examples, distinguish the adapter's
limitation from a soundness result. Loop examples should say when termination is
not established. Comments are part of the displayed source, so the tests always
regenerate claims rather than reuse offsets from the source as it was before.

The [null-guard fixture](stateful-source/null-guards.ts) exercises the graph
refinement path against real SKJS claims, including guarded returns and loop
transfers. Unsupported fixtures are checked separately at their syntax/type gates.
