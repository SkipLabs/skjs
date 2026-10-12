# Verification work

This is the work ledger for the independent verifier: milestones, their
completion conditions and open investigations. [DESIGN](DESIGN.md) states the
architecture and decisions; [the source boundary](SOURCE-FRAGMENT.md) owns
supported-fragment restrictions. A completed engineering milestone establishes
its listed checks, within the scope of their evidence.

## Next steps

Open design work, each a known gap with the reason it is open. How many
units each gap stops is in
[SKJS-COVERAGE](pipeline/SKJS-COVERAGE.md#refusals-by-class).

### Status

Progress is recorded here and nowhere else. A commit that moves an item
updates its row. The prose below describes each item's design, not its
progress.

**One producer.** The OCaml producer is the pipeline's one producer, which the
cases, the corpus and the report viewer run. The shared control-flow IR
separates execution structure from type-directed expression elaboration.
The Fragment supplies source-oriented type inference; graph points and edges
supply the producer's data-flow equations. Mutable declaration contracts and
point-specific contents have separate claim identities.

| Item | State | Closed when |
| --- | --- | --- |
| 1. Delete the TypeScript producer (`tools/tsc-claims.mts`): the OCaml producer is the pipeline's one producer, the corpus and the report viewer run it | done | compared per function on the corpus's 303 (2026-10-05): the OCaml producer's claims verify for 301, the TypeScript producer's for 276, every one of those among the 301; the producer, `--producer`, the viewer's producer choice, the report writer's generic report input and per-function collection metadata deleted; TypeScript's own verdict per function (`typescriptVerdicts`) beside the verifier's in the corpus and the viewer |
| 2. The producer reads the shared control-flow IR: design and validation. Lean constructs claim-independent execution points and edges, final lowering consumes that IR, and the producer proposes environments and current contents per point. Type-directed expression elaboration consumes those proposals; mutable declaration contracts have separate identities | done: `FlowGraph`, `ExpressionPlan` and `BindingPlan` supply the shared execution schedule; entry and expression claims have owner-qualified point identities, expression sites also retain source spans, and mutable lifetime contracts have separate identities; forged point and contract associations are refused | the design states the graph wire, the claims keyed by node and the checks on that association; a prototype over a subset of the cases (control flow, `try`/`finally`, iterator close, closures) reaches the same outcomes as the source-level producer, with forged node keys refused |
| 3. The producer reads the shared control-flow IR: cutover | done: all 847 cases and independent forged-claim/report controls pass; the 53-file corpus has the same per-function outcomes as its baseline (303 accepted, 301 derived, 2 not derived); all six protected runtime traces pass; source-level control-flow, compound-expression and binding/default execution mirrors are retired | every `cases.mts` outcome and the corpus's per-function results unchanged or better; the producer's source-level control-flow mirror and association by source position alone deleted; expression claims identified by execution point and source span |

**Decomposition and state ownership.** This checklist covers the producer,
source lowering and their documentation. Completion counts milestones, not
equal amounts of effort.

| Milestone | State | Closed when |
| --- | --- | --- |
| M1. OCaml proposal decomposition | done | pass coordination, execution, expression families and publication have separate modules |
| M2. Lean typed source lowering decomposition | done | recursive lowering operations have responsibility-specific modules and explicit callbacks |
| M3. Lean claim decoding and acceptance decomposition | done | decoding, site validation, extraction and certification have separate owners |
| M4. Lean equation lowering decomposition | done | equation construction stages have separate modules |
| M5. Lean nested graph frame | done | closure compilation restores one enclosing graph frame |
| M6. OCaml execution analysis interface | done | the interpreter receives explicit lookups and operations without mutable pass-state access |
| M7. OCaml speculative frame | done | speculative inference restores one local record on every exit, retaining shared proposals and diagnostics |
| M8. OCaml claim collection interface | done | claim collection receives lookup, publication and speculation operations |
| M9. Node output and path scopes | done | named output records and scoped execution replace paired checkpoint callbacks and restore enclosing output and metadata on every exit |
| M10. Overload-row claim scope | done | each signature collects its claims through one scoped operation with restoration on every exit |
| M11. Typing-context scopes | done | block return context, observation roots, active point and rigid bounds have explicit scope operations |
| M12. Remaining OCaml access restrictions | done | the seven expression modules, binding analysis, statement analysis and closure offers use responsibility-specific interfaces; their unrestricted pass-state views are retired |
| M13. Lean lowering access restrictions | done | temporary contexts have scoped operations and consumers cannot access or replace the complete construction state |
| M14. Documentation organization | done | calculus rules, source elaboration, host contracts, protocol definitions, architecture decisions and the work ledger have clear owners; large mixed-subject documents are split, prerequisites are explicit, and links resolve |

**Upstream sum example.** `reactive-sum-prettier-ignore`, Skip's sum service
as published, against the pinned upstream runtime. The program is safe; the
items are the verifier limits it meets and the runtime's declared service
types, which do not state why it is safe.

| Item | State | Closed when |
| --- | --- | --- |
| 1. An intersection with no member inside a union is that union's bottom arm: `number & DepSafe`, distributed to `number \| (number & Managed)`, is `number` | done | `union-empty-intersection-arm` verifies, an annotation and a contextual callback parameter; `array-shadow-refused` stays refused; `reactive-sum-prettier-ignore` reaches item 2 |
| 2. A named function passed where a callback type binds more parameters: JavaScript calls it with the extra arguments, which it ignores | open | `process.on(sig, shutdown)` verifies, `shutdown` checked at its own annotated signature |
| 3. `runService(service, …)`: the upstream service types admit the service only by method bivariance, and do not relate what `createGraph` returns to what each resource reads | open | a design for runtime types stating that relation, against which the published service source is checked |

**Boundary-repair cleanup: done.** Restore the original positive sources that the
soundness boundary repairs refused ([steps](#restoring-completeness)). Closed
when every step is done and a full coverage run is back to at least the former
mechanism's 2,444 verified units and 121 gaps (current counts:
[SKJS-COVERAGE](pipeline/SKJS-COVERAGE.md): 2,484 verified, 93 gaps).
`sum-process-alias` stays a gap for a cause outside Promise (a global read
only through its members).

| Step | State | Closed when |
| --- | --- | --- |
| Source `unknown`, `void` and value parameters range over JavaScript values | done: the [source-value boundary](SOURCE-MODEL.md#source-value-boundary), exception preservation, source-view equality and intersection rules have Lean proofs; generic instances retain their bounds | full Lean build, 928 pipeline cases and all six verifier suites pass, including forged calculus-top instantiation and singleton-void claims. Verifier-only corpus: 2,483/2,674 verify; one gain and no regressions against the last full report plus the later void assessment. `void#validVoidUnionUsage` verifies; `void.ts` is 20/21, with `returningConstrainedVoid` refused by TypeScript. SKJS acceptance is reused from recorded results |
| Optional-field observations admitting `undefined` | done: field facts denote current property-read results, including absence, with [observation and read rules](PROGRAM-TYPING.md#current-content-rules-semantic-layer) proved in Lean. The producer exports optional-field observations; the reader checks them at graph entries. Shape guards save their read once; branch observations combine the saved predicate with the tested type. `field-refinement#testOptionalFieldEqualsUndefined` verifies | full Lean build and all six verifier suites pass, including 931 cases, a forged optional-read fact refused at its incoming edge, and alias-write/call runtime controls. Verifier-only corpus: 2,484/2,674 verify, one gain and no regressions; 93 gaps. SKJS acceptance reuses recorded results |
| Nullable field observations across source checkpoints | done: `destructuring#checkedNestedPattern` and `earlierPatternRead` verify; nullish exclusions have proved observation and sliced-read rules, and each pattern field read has an independently checked result claim | full Lean build, pipeline cases, forged claims, runtime counterexamples and supporting checks pass; alias writes, unrestricted calls, mutating defaults and the remaining undefined alternative are refused. Verifier-only corpus: 2,481/2,674 verified, two gains and no regressions |
| Precise generic arguments under readonly index bounds | done: `tvar-widening-in-constraint-check#testObjectFieldTvarWidening` verifies when inference prefers argument lower bounds and fresh literal arguments retain their inferred contracts and exact keys under readonly dictionary bounds | nested-field reads verify; function-valued members violate the bound; named members retain contextual contracts; full pipeline suite passes; verifier-only corpus gains one unit with no regressions |
| Producer retains structural dependent bounds | done: both `generic-dependent-constraints` units verify when named functions and generic closures retain their declared value bounds; Lean's bound interpretation is unchanged | reads and writes through `T extends Ref<U>`, chained bounds and outer closure parameters verify; incompatible writes are refused; pipeline suite and verifier-only coverage pass |
| Constructor argument spreads | done for fixed tuples: the original fixed-tuple target verifies; multiple, readonly, empty and generic spreads verify; incompatible elements and forged operand claims are refused. `repro311` also needs variadic constructor contracts | full Lean build and six suites pass; execution-plan and runtime controls preserve callee-first evaluation and snapshot-before-mutation order. Spread-field audit: parser and decoder retain positions; producer expands tuple contracts; execution planning snapshots operands; graph lowering reads every element; closed-expression lowering explicitly refuses spreads; recursive traversals retain operands and spread positions |
| Interface heritage through intersection aliases | done: every intersection part contributes its instantiated clauses through the existing source meet | `interface-extends-alias#viaInterMembers` and generic intersection-base reads and construction verify; missing inherited members are refused; full Lean build and all six suites pass |
| Generic class prototype contracts across module scope | done for [methods without their own type parameters and with independent class bounds](SOURCE-CONTRACTS.md#classes): `instanceof-generic-skolem-args#typedIdentity` and `generic-prototype-instanceof` verify; broader scope limits are stated in the contract | one fixed prototype contract across class instantiations; primitive, record and named bounds, repeated-bound normalization and multiple parameters, distinct constructed instances, generic consumers, deferred reads and inheritance verify; incompatible writes and forged prototype claims are refused; full Lean build and all six suites pass |
| Unreachable destructuring defaults use the saved read when `Answers` proves it defined | done: all five original coverage units verify; reachable defaults retain claims and effects, both Lean entry points refuse an omitted reachable-default claim, and the full Lean build and six verifier suites pass | all five original coverage units verify, reachable defaults retain claim and effect checks, and the full verifier suites pass |
| Generic union inference preserves named actuals until the arm is selected and uses native-head matching only for an arm containing binders | done: unchanged `stypes-diff#testPromiseInUnion` and all 25 units in its file verify; `generic-fixed-promise-union` verifies and its bounded negative is refused; the full pipeline suite passes | inference proposes an instance covering the actual argument, the original source verifies, and an incompatible fixed-arm call remains refused |
| Loose equality coverage | done | `loose-equality`, `object-identity-equality` and `equality-deciding-operand` verify: primitive pairs, nullish operands and object pairs compared by allocation identity, and an operand known to be a primitive, an object or nullish against a type parameter's value; `invalid-loose-equality-narrowing` is rejected; `==` converting an array or an open record to a primitive stays refused ([row](SOURCE-FRAGMENT.md#refused-on-principle), `loose-equality-array-conversion-refused`, `loose-equality-conversion-refused`); the upstream sum example reaches the shared refusal of the empty intersection `number & Managed` |
| 1. Explicit-comparator sorting | done | `native-sort-contracts` and the tuple-valued sorts verify; the optional-comparator negative is rejected |
| 2. Sparse results | done | `native-map-sparse`, `testTupleArrayMethod` and `isarray-record-array` verify; `invalid-map-hole-coalescing` is rejected |
| 3. Density-sensitive calls | done | `array-methods`, `array-library`, `array-generic-name`, `closure-contextual-parameters`, `testArrowOptional` and `testMapReturnsArray` verify; `mapArr`/`testMapCallback` stay refused, their written contract being false |
| 4. Standard array conversion | done | `sum-local-closure`, `sum-values-tuple` and `local-closure-result` verify; the coercion counterexamples are rejected |
| 5. Recursive quantified contracts (Promise) | done | the Promise table below is done |
| Coverage group "destructuring and rest/default parameters" (14 gaps) | done: 6 principled, 8 gaps | a rest typed by an intersection refused on principle ([row](SOURCE-FRAGMENT.md#refused-on-principle), `invalid-rest-intersection`): `arraysAreInvariant` and `variance`'s `interWithTop`/`interWithTopS` units; coverage run 2,444 verified (2,444), 135 gaps (141), 85 principled (79). The 8 left are a binder used both as a pack and as an array value , whose design is in [remaining source forms](#next-steps) |
| Coverage group "classes: modifiers, inheritance, fields, parameter properties, receivers" (13 gaps) | done: 8 verified, 4 principled, 1 gap | a method declaring `this: T` is a member whose host must meet `T` ([method members](SOURCE-MODEL.md#method-members-are-host-relative), `method-receiver`; `invalid-method-receiver` and `invalid-method-receiver-widened` rejected at their own obligations): the 8 `this-parameter*` units verify. A class extending `Array` is [refused on principle](SOURCE-FRAGMENT.md#refused-on-principle) under [ordinary array construction](SOURCE-MODEL.md#arrays) (`invalid-array-subclass`, with a Node run of `map` constructing through the subclass): the 4 `class-extends-generic-constructor` units. Coverage run: 2,452 verified (2,444), 123 gaps (135), 89 principled (85). The 1 left, `spread-callable#indexedOwnCopy`, is an index signature in a class, whose next blocker is method extraction (`read: source.read`) |
| Coverage group "a non-null assertion on a read at a for...in key" (8 gaps) | done: 8 verified | a `for...in` over a dictionary whose body reads the entry at its key where nothing that could change it ran since the step steps the dictionary's entries (`%Iterate:ForIn%`), each such read the step's value ([statement forms](SOURCE-CONTRACTS.md#statement-forms), `for-in-entry`); a read after a call, after a write of the enumerated chain and after rebinding the enumerated name are rejected at the cast (`invalid-for-in-entry-call`, `-field`, `-rebound`, each returning `undefined` under Node) |
| Coverage group "object literal members (methods, accessors, spreads)" (10 gaps) | done: 5 verified, 5 gaps | `Object.assign(arrow, literal)` at the two type arguments TypeScript infers (`function-fields-inferred`); the last merge of a literal at its claim, a written field allocated per arm of the expected union (`spread-field-per-arm`, `invalid-spread-field-per-arm`); a spread of a function copies its own fields, a created function's identity field being under `[[code]]`, which no source spells (`spread-function`, `invalid-spread-function-length`). Coverage run: 2,466 verified (2,452), 110 gaps (123), 88 principled (89: `callability#testSpreadTypeofFunction`, which TypeScript refuses, verifies). The 5 left are [model limits](SOURCE-FRAGMENT.md#model-limits): a spread of a value that may be a class, whose statics are bindings of the model (`spreadConstructor`, `copyStaticData`, and `spreadFieldsAfterSpread`'s `{}`, which also admits a string), of an array, whose own numeric keys other than its elements its type does not bound (`restArrayEntries`), and of a symbol-keyed property, which the copy does not take (`symbolBranch`) |

**Promise (step 5).** Closed when `promise-covariance` verifies and
`invalid-promise-covariance` is rejected at its own obligation; the
`library-promise*`, `async-await`, `promise-instance`, `class-async-method`
and `sum-*` framework cases verify with their negatives rejected at their own
obligations; and `sum-sound-binding` verifies unchanged. The Promise gaps are
the `cases.mts` entries refused as unsupported recursive generic contracts.

| Item | State | Closed when |
| --- | --- | --- |
| a. Recursive equations | done | the table below is done |
| b. A callback returning a promise instantiates `then`'s binder through `PromiseLike<TResult>` | done | `promise-then`, `named-promise-catch` and `promise-then-promise` verify; `invalid-promise-then`, `invalid-promise-then-promise` and `invalid-promise-catch-promise` are rejected at their return contracts |
| c. `await` on realm promises, forged promises refused | done | decided; `forged-promise-refused` stays refused on principle |
| d. A binder no actual, receiver or expected type constrains takes its declared default (`then`'s `TResult2 = never`), which the declaration document states for each scheme binder | done | `promise-then-chained` verifies; `invalid-promise-then-chained` is rejected at its return contract |

**Recursive equations (Promise a).** Closed when
`generic-growing-application` and `generic-growing-application-push` verify
unchanged ([design](#recursive-quantified-contracts)).

| Item | State | Closed when |
| --- | --- | --- |
| Shared rows (`GraphRow`, `NormalGraph.ofRowMap`) | done | proved |
| Equation graphs, one-step unfolding (`EquationGraphs`) | done | proved |
| Free support (`EquationSupport`) | done | proved |
| Application congruence (`EquationCongruence`) | done | proved |
| Checked substitution (`EquationSubstitution`, `substitutionTableOk`) | done | proved |
| One proved image checker for subtyping, expression typing and program certificates (`checkUsing`, `HasTyUsing`) | done | proved |
| Formal specification ([RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md)): motivation, meet labels, quantified-α, family subtyping, lowering, wire format, acceptance statement | done | reviewed; corrected to the pipeline |
| Thread the image checker through heap, context, control-flow and certificate-production proofs | done | proved; no finite-only premise left on the program path |
| Kernel: quantified-α, family entries, per-head variance declarations and `Var`, writable invariance kept ([§4](RECURSIVE-EQUATIONS.md#4-subtyping)) | done | proved, with the §7.7 controls as tests; `promise-covariance` and its negative move with S7 |
| S1. Source-claims wire with tree labels ([encoding](SOURCE-CLAIMS.md#encoding)); a temporary Lean adapter keeps the finite path | done | every `cases.mts` outcome unchanged; tamper and field-name tests pass |
| S2. Diagnostics show labels through a finite projection | done | identical diagnostics on every case |
| S3. Kernel: meet labels, equation validator, tree codec and hashing | done | proved; no pipeline change |
| S4. Source layer generic in its label type, still over the finite table | done | bit-identical evidence on the corpus |
| S5. Equation lowering module ([§5](RECURSIVE-EQUATIONS.md#5-from-source)), not yet wired | done | lowers `Promise`, `PromiseLike`, `Pair` and the upstream declarations with no budget |
| K2. Kernel: family hypotheses reach meet parts, so `meet(x,B) ≤ meet(y,B)` holds under `x ≤ y` (the framework's `T & DepSafe` heads, [§4.3](RECURSIVE-EQUATIONS.md#43-variance)) | done | proved; the `sum-collections` heads' variances check |
| S6. Cutover: lowering wired, `DeclarationGraph`, its budgets and the adapter deleted, `checkJson_safe` over `Equations.graph` | done | `generic-growing-application`, the Promise/async core, `sum-main` and `sum-run-service` verify; no negative verifies |
| R1. Fix: a bound framework method's claimed signature refused, the judgment holding. Equation lowering names a declaration's type literal by a head lifted over its binders, so the literal at an instance and the producer's own row for the same type are two labels with equal unfoldings. Two components required one label where the rule admits either. (a) Proof search's instance of a quantified member (`instanceCandidates`) offers the claimed operand as the image of a scheme operand spelled otherwise, which the image check accepts once proved equal, for fixed and variadic signatures: `map`'s constructor parameter `new (...p: P) => Mapper<…>` at its instance (`sum-map-array`, `sum-serializable-map`, `sum-add-index`, `class-value-generic-method`). (b) The checker's `bindMember` required a claimed variadic signature to be the member's by label (`merge`'s rest `EagerCollection<K, V>[]`); it covers it by subtyping proofs of the fixed parameters, the rest and the result, as a fixed one ([rule](PROGRAM-TYPING.md#judgments-and-constructor-views); `sum-collections`, `sum-resource`, `sum-sound-binding`) | done | the seven cases verify; `invalid-sum-map`, `invalid-sum-resource-mapper` and `invalid-class-value-generic-method` are rejected at their own obligations, and a rest claim wider than the member's at the bound member, by search and by the checker (`test.mts`); coverage run 2,441 verified (2,440 before), 142 gaps (142), 2 unexplained (3): `eagercollection-deep-value-no-oom#build` verifies; `json-generated-service#GraphResource` stops before any call, at its declarations, a record as `EagerCollection`'s `V extends Json` |
| R2. Fix: producer claims refused as outside their source annotation. Two causes, both in how the claims were written or read, the comparison being right. (a) The producer spelled a bounded binder `T` as `T & B`, while a binder label already denotes `T` within its bound as its unit reads it, the meet `T ⊓ B`: the claim read `T ⊓ B ⊓ B`, with `B` distributed when a union (`V extends Json`). Semantically within the annotation, but a second spelling the checker's meet rule does not relate (`generic-graph-bounds`; `class-ctor-tparam-unsound`, `generic-class-union-constraint`). The producer writes a binder by its name alone ([encoding](SOURCE-CLAIMS.md#encoding)). (b) A generic closure's scheme row for its annotations read the enclosing binders in claim-form parameters but not in graph labels (a class's generic method's receiver `C<T>`), so its annotations and its claim named two scheme rows' binders (`clauses-diff-subset`); `closureRows` reads them as its claims do | done | `generic-graph-bounds` verifies and `invalid-generic-graph-bound` is rejected; coverage run 2,438 verified (2,430 before), 144 gaps (155): the 8 `class-ctor-tparam-unsound` and `generic-class-union-constraint` units verify; of the 3 `clauses-diff-subset` units, 2 reach a later obligation, a class's generic method at the class's instance type (`class-generic-method`'s block, R3), and 1 is refused where TypeScript refuses it |
| R3. Fix: a class's generic method refused where the judgment holds. The prototype's closure and the instance type's member are two quantified signatures binding rows of their own (each scheme's binders are its head's), and the checker related a scheme received by the host to a target member only when both bind the same rows (`SchemeBinds`): incomplete for the quantified rule, which holds up to renaming ([RECURSIVE-EQUATIONS §4.1](RECURSIVE-EQUATIONS.md#41-quantified-signatures)). `SchemeBinds` renames the target's binders to the closure's, as `SchemeRenames` does for two declared schemes, proved in `covers_by_scheme_sound` ([rule](POSITIVE-TYPES.md#clause-coverage)) (`class-generic-method`, `clauses-diff-subset`) | done | `class-generic-method` verifies; `invalid-class-generic-method` is rejected at its own obligation, and a class declaration tampered so that the closure does not cover the member after renaming is refused at the construct code's return (`test.mts`); coverage run 2,444 verified (2,442 before), 141 gaps (141), 0 unexplained (2): `clauses-diff-subset#Helper` and `#testExplicit` verify |
| R4. Fix two stale `pipeline/test.mts` checks. The nested closure claim `() => boolean` over a body of type `T` is refused: proof search finds no derivation of its return-contract obligation, and the original evidence does not decode against the forged claims' equations; the check expected a message the equation labels no longer produce. `async-await` verifies, and the reader shows it verified; the check expected it refused as an unsupported Promise contract. The nested claim check asserts the search refusal at the body; the reader checks `invalid-default-invocation` as a whole-file unsupported source result before claims exist | done | both checks pass |
| S7. Variance by the checker ([§4.2–4.3](RECURSIVE-EQUATIONS.md#43-variance)): recursive instance discharge, variances computed per definition (traversal; guarded self-assumption on cycles), `Var` in request certificates, fallback coinduction up to renaming of bound variables; lowering's variance proposal and the front's variance gate removed | done | proved; tracing (`--trace-subtyping`) and the measurement script (`tools/subtyping-trace.mts`) in place; `promise-covariance`, `generic-growing-application-push`, `promise-like`, `framework-binding-sound`, `framework-binding-unsound` verify; `invalid-promise-covariance` and `invalid-framework-binding-sound` rejected at their own obligations |
| D. Decidability of subtyping in this model, studied in mathematics before any Lean | done | a note stating the problems precisely, what is proved, and what is open |
| S8. Coverage and performance, including the subtyping trace: work per question against type size ([§4](RECURSIVE-EQUATIONS.md#4-subtyping), linear-work conjecture) | done: 2,430 verified, 155 gaps, 1 unexplained; evidence median 44 kB, check median 32 ms; checker work at most 8.2 steps per unit of type size over 169 questions, consistent with the linear-work conjecture, not proving it ([measurements](pipeline/SKJS-COVERAGE.md#performance-on-the-pipeline-cases)) | coverage run remeasured; evidence size and decode time recorded; the conjecture confirmed or refuted on the examples, with the trace's counts |
| C. Delete the SKJS claim path, manual claim editing and the finite-table label store | done | no verifier mode, suite, tool, corpus column, report viewer feature or Lean module consumes SKJS's exported claims, edits claims, or uses the finite table as a label store; every `cases.mts` outcome unchanged |
| P. Fix: evidence production on `sum-sound-binding` and `reactive-sum-sound` costs 15 s at any search depth. Their one failing coercion (`Array<row 53>` to its meet with a readonly array) exhausts every search strategy, two of which prune a core table over the whole vocabulary (199 types, about 4600 candidate rows, 5–6 rounds), each table membership a scan of the row list. Search reads the table through a hash set of its rows (`CertificateProducer.RelIn`); the checker reads the list | done | both cases reach their expected refusal in under 5 s alone; every other `cases.mts` outcome unchanged |
| Q. The producer's subtyping search is §4's algorithm; the strategy cascade and pool-wide tables deleted. The search starts from the pair only: the premise judgment, an instance of a quantified signature (binder instances read through a meet among the matched row and the target's operands), or the fallback, which the checker decides itself: the pairs reachable from the pair, the uncovered ones deleted, the producer supplying only prototype-member instances. No certificate holds a table: `core`, `trans`, `table` and `gen` are deleted with `checkCore`, `Core`, `Valid` and `Sub`, and an instance's bounds are decided | done | `lake build` green, every `cases.mts` outcome unchanged but the two gap cases blocked on the meet `Array<row 53> & ReadonlyArray<…>`, which is now proved and moves their block to a later obligation; the case run 55 s (104–144 s before, loaded machine), `sum-sound-binding` 1.2–1.4 s alone (5.5–7.0 s before) |

**Follow-ups.** Engineering work not on the goal's path.

| Item | State | Closed when |
| --- | --- | --- |
| K3. Lowering: a unit bound naming another binder of the unit (`U extends T`). A function's or class's binder is its head's owned binder met with its lowered bound, which names the other owned binder (`EquationLowering.enterUnit`); a declared generic method's bound naming its own binders is refused ([request protocol](REQUEST-PROTOCOL.md)) | done | `generic-dependent-bounds` verifies (a function and a class); `invalid-generic-dependent-bound` and `invalid-generic-dependent-class-bound` are rejected at their own obligations |
| O5. The decoder convention ([AGENTS](AGENTS.md#conventions)) holds on the node side: each assertion that stood in for a check is replaced by it (a type predicate, a `typeof` or kind narrowing, `tools/syntax.mts` for the children a node of unasked kind carries, a restructured loop or destructuring), and `node verification/tools/unchecked.mts` fails on a written `any`, `as` or `!` without a `// asserted:` reason, a suite of `test-all.sh` | done | 81 `as` and 24 `!` in 20 files before; 7 `as` in 5 files, each a decoder's last line with its reason |
| O7. Divergence found by grouping the cases by requirement: requirements the cases guard that no document stated, source refusals in neither fragment-boundary table, and statements the pipeline contradicts | done: each requirement stated where it is owned, its group justified there: a type literal of call or construct signatures only, a rest over a union of tuples and the library's `Iterator` ([library types](SOURCE-CONTRACTS.md#library-types), [iterator protocol](SOURCE-CONTRACTS.md#the-iterator-protocol)); declaration merging ([one equation per declaration](SOURCE-CONTRACTS.md#one-equation-per-declaration)); object shorthand ([derived source forms](SOURCE-ELABORATION.md#derived-source-forms)); `unique symbol` constants ([library globals](SOURCE-CONTRACTS.md#library-globals)); logical assignment and a `.call` receiver ([judgments](PROGRAM-TYPING.md#judgments-and-constructor-views)); a `Promise` method's binder through `PromiseLike` ([async](SOURCE-CONTRACTS.md#async-functions-and-await)); a closure's offers wherever it flows ([source closures](SOURCE-ELABORATION.md#source-closures-and-their-annotations)); a `typeof` test of a type parameter's value ([refinement](PROGRAM-TYPING.md#refinement-under-an-observed-outcome)). Every source refusal is a row of its table (4 principled rows, 18 limit rows, 4 limit rows widened), its case in that table's group with the row's kind (4 gaps made negatives, 14 negatives made gaps; `pattern-method-refused` and `mutable-tuple-position-refused` stay gaps under O8). Contradictions resolved: the class list admits generic inheritance at the base's binders and constructor defaults; a spread before an effect is copied into a rest and refused into fixed parameters; generic members relate up to renaming, the producer's reason corrected; `invalid-isarray-record`'s row removed, a typing rule's search failure; the symbol-key copy stated as the model's, beside JavaScript's | each requirement stated in the section owning it, each refusal a row of its table, each case's kind agreeing with its row |
| O8. Fix: two principled refusals, a method read off its object by a pattern and a position past a mutable tuple's arity, were thrown by source extraction as bare messages, so the report viewer had no obligation to show and their cases could not be negative controls. Both go through `locatedRefusal` at the pattern element (`Pattern.span`) | done | both refusals located at their source span; `pattern-method-refused` and `mutable-tuple-position-refused` negatives, the reader showing each |
| C2. Write the source layer directly over its one store, `EquationStore.State`: `EquationLowering` and `EquationStore` precede the modules written over them in the import order, which call the store's operations and `equationFront` directly. `StoreView` and `Labels` stay classes, each with two instances: the growing store and the frozen equations | done | the three classes deleted; `lake build` green; every `cases.mts` outcome and diagnostic unchanged |
| E. Fix: the declaration reader erased a generic method whose signature it could not read to an `unknown` member, so a produced value met the declaration at any field (`return { run: 42 }` as a `Runner` whose `run` takes a type literal with a generic method). The reader refuses the declaration at such a method; a declaration's generic function type, the form behind most such erasures (`EagerCollection.mapReduce`'s result), is a scheme term whose signatures take any receiver ([request protocol](REQUEST-PROTOCOL.md)). The other `unknown` readings in the parser, the OCaml producer and Lean are stated meanings (a declaration's `any`, an ambient class's untyped readonly field, a receiver no signature states), none a fallback for a contract the reader cannot read | done | `invalid-generic-method-nested-scheme` refused at its declaration, and 42 in `run`'s place throws under Node; `generic-method-nested-method` and `generic-function-type-member` verify, `invalid-generic-function-type-member` is rejected at its return contract and returns the unpaired argument under Node; coverage run 2,466 verified (2,466), 110 gaps (110): no unit loses verification; `testUnionWithGenerics` and `testGenericTupleConstraint` stay gaps, blocked at their own generic function values |
| U1. [Unified subtype engine](#subtype-engine-cleanup-plan): one comparison operation and its soundness boundary | done: checked structural dependencies and completed results share one comparison state; cached successes carry proofs at every parameter assignment, with a fresh cache for each equation environment; full Lean build and eight pipeline suites pass; the source case suite passes | the operation handles the existing subtype rules over equations, with checked internal justification and explicit resource exhaustion |
| U2. Route subtype consumers through that operation | done: lowering, extraction, proposal search and certificate checking use the common operation for bounds, arguments, results, receivers and image equality; explicit instances share its checked state; declaration gates retain located outcomes; Promise, 205-field record and callable-bound positive/negative controls pass | bounds, arguments, results, receiver checks and instance-image equality use the same engine; producers supply inference choices |
| U3. Resource accounting and diagnostic integration | done: explicit frontier budgets retain typed exhaustion through required source comparisons, proposal search, expression/heap checks, graph/code validation and source bundles; acceptance equivalence is proved; both CLI modes and the shared report viewer presentation pass insufficient/sufficient-budget controls with located judgments and inconclusive exhaustion | the 200-comparison acceptance cap is absent; exhausted work is located and visibly inconclusive through the CLI, runner and viewer |
| U4. Retire superseded paths and validate the cleanup | done: public evidence supplies instance choices; separate subtype strategies, finite bound search, producer image prechecks and stateless instance helpers are retired; rule inventory and documentation checks pass; full Lean build and eight suites pass; the source case suite passes and per-function outcomes agree with the recorded coverage run; five alternating binary benchmarks have comparable search/check timings; a forged instance bound citing its unfinished comparison is refused during evidence search and checking | strategy-selection evidence and duplicate searches are deleted; the closure checks below pass; documentation and coverage measurements agree with the implementation |

The stages' order and dependencies: S1, S3 and the kernel rows may run in
parallel; S4 follows S1; S5 follows S3 and S4's interface; S6 needs all of
them and the image-checker row; S7 follows S6; S8 follows S7. K2 and K3
block the framework cases, not the cutover.

<a id="subtype-engine-cleanup-plan"></a>
### Subtype comparison

The [recursive-equation rules](RECURSIVE-EQUATIONS.md#4-subtyping) own the
comparison algorithm and its soundness statement. Milestones U1–U4 above record
its implementation and validation.

### Open work

**A connection to ECMA-262.** Proving the host's stated types as lemmas of a
mechanized specification would turn the ECMA rows of the trust surface into
theorems; the lemmas and their cost are in
[TRUST-REDUCTION](TRUST-REDUCTION.md#the-host).

**Constructor rests.** A constructor's rest parameter is refused. The code
could collect it as a closure's does, but no rule constructs at a variadic
construct signature: `ctorRestsT` has neither an introduction from code nor
an elimination by `new`, so that rule and its `construction` for code with a
rest (whose padded actuals would reach the store) come first.

<a id="generic-methods-left"></a>
**Generic methods left.** A class's generic method with a bounded binder:
the member's binder row is named by its bound, which the parser does not
spell for the closure (`class-generic-method-bounded-refused`). Members of
two declarations, or of two instances of one, binding as many binders relate
up to renaming ([generic methods](SOURCE-CONTRACTS.md#generic-methods)); two
binding different numbers of binders (`m<U, V>` at `m<W>`), which TypeScript
relates by instantiating the source at the target's binders, need an instance
table naming each source signature's image at the target's binders, inside
the family entry's table. A binder a member's result accumulates
(`catch`'s `Promise<T | TResult>`) grows its family by one binder per call:
each is an application of the one equation, unfolded only when read
([RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md)), never truncated. Members of
two declarations, or of two instances of one, bind different parameters; the comparison operation relates their signatures up to binder
renaming ([RECURSIVE-EQUATIONS §4.2](RECURSIVE-EQUATIONS.md#42-parametric-assumptions)).

<a id="restoring-completeness"></a>
**Contract completeness.** Array presence, callback effects and conversion
contracts impose separate obligations. Their current designs are stated under
[arrays](SOURCE-MODEL.md#arrays), [native contracts](SOURCE-MODEL.md#exact-contracts-and-native-effects) and
[effect certification](SOURCE-MODEL.md#inferred-call-effects-elaboration-and-certification).
A future inference improvement must preserve these distinctions: density is
stronger than readable elements; readonly aliases do not prevent callback
mutation; and a written callback annotation cannot silently acquire a stronger
effect. A program with an arbitrary callback promising readable `U[]` for every
`U` must justify that promise even when the callback shrinks the source.

Effect inference remains conservative for some rest wrappers, call forms and
nested heap operations. Expression scheduling alone does not supply the missing
effect derivation. Keep the source targets and their negative controls when
extending the body-effect checker; report coverage using the measured results
in [SKJS-COVERAGE](pipeline/SKJS-COVERAGE.md).

<a id="recursive-quantified-contracts"></a>
**Recursive quantified contracts.** Generic declarations are parameterized
equations. Their finite syntax can describe an unbounded family of instances;
comparison unfolds only what an obligation needs. Parameter identities must
remain local to their applications, substitution must preserve bounds and
effects, and writable positions must remain invariant. These requirements are
specified in [RECURSIVE-EQUATIONS](RECURSIVE-EQUATIONS.md).

A universally quantified native prototype is an audited host contract. It
cannot replace an arbitrary structural interface whose method may capture the
interface's type parameter. Any future simplification must preserve that
semantic difference.

**The array invariant at `unknown`, and a record's `length`.** `Array.isArray`
on `unknown` needs the invariant of every value, a thrown one included: the
throw outcome of `Safe` would carry it, which makes it relative to the graph's
realm. `length` read on a union of an array and a record naming `length`
needs a dispatch on `Array.isArray`, the store's length on one arm and the
field on the other, with the invariant excluding an own `length` key, which
the model's arrays never have. Until then both are located search failures.

**Keys known only at run time.** A key-adding write at one of several literal
keys needs a dispatch on the key, one copy per key; at a number or a symbol,
a one-key allocation at a computed key, and for a symbol a copy that takes
symbol keys. A write adding a key to an object another reference holds needs
the heap to map an object's identity to its keys, which it does not.

**Module composition** as a Lean theorem: the step-indexed argument that
units certified against each other's signatures compose.

**Iteration left open.** An array literal spread needs a literal lowering
that appends a spread's elements (the `%Spread:K%` array, or an array's
store) after the positions before it. An array pattern over a host
non-array iterable needs the pattern's reads as steps of `%Iterate:K%`, or of
the protocol. A spread of a program's iterable where the statement evaluates
code before it, and a default or nested pattern in an array pattern over one,
need the protocol's steps interleaved with that code, in the expression, not
before the statement. A generator needs a state-machine lowering, as
TypeScript's downlevel emit writes one: a closure over the suspension
point's number and the live locals, whose `next` resumes at a `switch` on
it. An element read past a readonly tuple arm's length needs a rule
reading `undefined` beyond an exact length.

**Remaining source forms.** Assignment patterns into fields: each
element's target reference (receiver, computed key) evaluated into slots
before the position is read and defaulted, then a field write, which the source parser restricts to local-variable targets. A method call on a union of primitives,
which needs one callee contract its receiver meets. A source binder used both
as a pack and as an array value (`...args: T`, `args: T`): a binder whose instances are
arrays or tuples of required positions, its pack meaning that tuple contract's lists, so an
entry collects the fresh store at it and a spread of its value gives a list in the pack. Explicit type arguments on an element call,
which reach an element only as a generic closure's quantified claim.
User guards and assertion functions: the promise is a contract a
conjunction of arrows states, `(x: A) => boolean` with
`(x: Exclude<A, T>) => false` (an assertion function's `=> never`), which the
body is checked at, as a closure at each of its signatures; a caller narrows
through a fact the call leaves tying its result slot to its argument slot,
"an argument in `Exclude<A, T>` gave `false`", which the branch on the
result turns into a slice of the argument. Such a fact is about a type's
meaning, world- and level-indexed, where current-content facts are not; it
needs its own place in the knowledge a statement entry states. A class's
statics read by its own methods, which needs them read late, from the class
value, rather than as bindings its closures capture; private names in
inheritance, which needs the derived construction's copy of its base part to
carry the base's private slots; a prototype member keyed by a symbol.

**Model limits of one form each.** Module storage (`declare let`, a
module-level `let`) needs cells every call may write, read at their declared
type. Sloppy code's `this` needs the receiver conversion (the global object,
a wrapper). A library class as a base needs a construction rule for what its
constructor allocates. An ambient enum needs an enum type that is not its
value set. `keyof T` and `T[K]` over a function's own binder need a row whose
meaning fixes a key set, which a value set does not. A relational comparison
converting `undefined` or a Boolean needs the conversion's rule, and the
refusal a reason apart from an object's. `o.m?.()` needs the receiver saved
across the test. `key in o` at a key the realm's prototypes hold needs those
prototypes' keys in the model.

**Precision.** Retaining heap facts across calls needs a proved
reachability or noninterference statement; set-valued clause covering (an
arrow against a union of arrows) needs a covering relation of another arity;
a vacuity escape for contradictory reference conjunctions
(`Ref null ∧ Ref bool ≤ Ref (null ∨ bool)`) is true and not derivable; the
producer's arrow search builds no nested `combine`. An element read keeps no
heap fact: it reads the heap only, but the value it finds is a value only
where the store's contract says so, which the frame rule would have to take
from the read's typing (a length is a number, and keeps them). A module function of fixed
arity meets a longer signature (it discards the actuals past its parameters,
`restsT_of_graph`), but its slot is its annotated signature: the slot would
carry the padded promise, a claim its own unit checks.

**A semantics of the Fragment.** The parser's rewrites and extraction rest
on review. The Fragment moves close to source JavaScript, the rewrites move
into extraction, and the Fragment gets a direct semantics in Lean: an
executable interpreter that reads it as JavaScript does, with types erased.
Extraction is proved a simulation of it. The interpreter's faithfulness to
JavaScript is tested against node, not proved: the target is fixed, so
testing converges without a mechanized specification. A rewrite chosen by a
type (`%Iterate:K%`, `%ElementAt%`) is correct under that typing premise.
The reading of declared types and the host remain trusted; the remaining
options are in [TRUST-REDUCTION](TRUST-REDUCTION.md).
