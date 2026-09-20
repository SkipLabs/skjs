# SKJS implementation improvement

Progress on making the checker more principled, using the independent semantic
contracts as a reference. This is **SKJS `src/` work**. It is not the
verification pipeline, and it is not a plan to make SKJS implement the Lean
fragment.

The bounded repair/lifetime audit is complete. The stronger architectural
refactoring is **in progress, not complete**: clarity, restricted capabilities and
separation of inference from validation are its additional completion criteria.
See [Architectural end state](#architectural-end-state).

Status of each row is stated only here. Corpus row status stays in
[ledger.yaml](ledger.yaml). Verification architecture stays in
[verification/DESIGN.md](../verification/DESIGN.md).

Update a row when a SKJS commit lands that addresses it: set the status, name
the tests, and keep the “done when” criterion true. `make test-in-docker` must
stay green.

Put a repair's regressions in [`tests/expect-error/`](../tests/expect-error).
The verification corpus is the functions that arc introduced in that directory,
so a test placed there is measured and one placed elsewhere is not. Appending a
case to an older file adds that case, not the file's existing contents.
`make verify-census` reports how many of its functions the pipeline can verify
and why the rest are refused; adding tests moves the recorded baseline, which
`make verify-census UPDATE=1` accepts. It counts against the functions SKJS
accepts, not against every function: a regression SKJS rejects is stating
nothing to check, and is reported separately rather than as a shortfall. The census is a measurement, not a gate:
a refusal names a boundary of the verified fragment and says nothing about
whether SKJS is right.

It extracts each top-level function with the file's non-function context,
including ambient declarations, aliases, classes and top-level variables. Other
named function implementations are omitted; it is not a dependency resolver.
Do not distort a regression to suit the census. For the pipeline continuation
checkpoint, inspected blockers and safe extension workflow, see
[Repair coverage](../verification/REPAIR-COVERAGE.md).

## Spec

Three similar-looking kinds stay distinct:

| Kind | Obligation |
| --- | --- |
| Generic parameter `T` | The body works for **every** admissible `T`. |
| Inference variable `?T` | The checker may **choose** a type that meets the constraints. |
| Hidden type argument of an object | There **exists a fixed type**; the checker cannot choose or identify hidden args of different runtime objects. |

Delayed literal selection is an existential **inference problem**: choose a
representation satisfying the element and use-site obligations, then preserve
that choice for later uses. It is not elimination of a hidden existential
package. The latter introduces a rigid unknown whose witness was already fixed
by the runtime object; the checker must work without choosing that witness.
Thus selectors belong with solver choices, while hidden arguments belong with
rigid parameters. Both need stable identity, but grant different authority.

`T extends boolean` is `T ≤ boolean`. It is not `boolean ≤ T` or `true ≤ T`.

SKJS separates rigid `TParam` from solver `TVar`. A parameter ID also carries
an explicit `ParamOrigin`: declared, ordinary synthetic, or hidden witness.
Equality includes that origin and renaming preserves it; a printable synthetic
name cannot forge a hidden witness. The owning substitution's witness allocator
is private, separate from rollback state, and exposes only a scope checkpoint.
Uses preserve rigidity, scope and witness identity through the retained escape
roots described below; origin tagging alone would not establish that lifetime.

Contracts (full text in [DESIGN](../verification/DESIGN.md#contracts)):

1. Substitution preserves meaning.
2. Expansion and normalization have explicit exact / approx / cache guarantees.
3. Successful subtyping is semantic inclusion under every assignment satisfying `Δ`.
4. Inference cannot invalidate previous checks.

Target architecture: inference **proposes**; validation is against an
**immutable, explicit** representation. The current implementation enforces parts
of this contract through shared mutable state and runtime protocols; it does not
yet provide the capability separation planned below. Heuristic inference may stay. Its
success does not authorize acceptance. Caches and clones then have local
obligations instead of becoming part of the meaning of subtyping.

The [mathematical audit](skjs-type-soundness.tex) already separates guidance
from validation and treats stale-state reads and caches as stability failures.
That is a starting specification, not a proof of the current checker.

A soundness argument against these contracts, with regression tests, can
justify a SKJS fix. An independently checked derivation is a **strong** route
to an incompleteness fix, not the only permitted one. A verification-pipeline
`reject:` is not a disproof, and a failed proof search is not incompleteness.

## Completed bounded repair audit

Statuses: `not started` · `in progress` · `done`.

R1 (hidden identity and escape), R3a (declaration identity), R3b (freeze-window),
M2 (stale captured reads), and M3 (loop-carried narrowing) meet their stated
bounded completion criteria.
The current validation-lifetime audit (R2/R3c) also meets its implementation
completion criteria, as recorded below. R1 records and revalidates signature
and persistent-binding escape roots. M1 now meets its bounded mutation/alias
criterion for the checked data-object language; its interoperability boundary
and evidence are recorded below. In this table, “done” means the stated bounded
implementation audit passed. In particular, R2/R3c do not mean that inference and
validation now have separate interfaces or that all invariants are enforced by
the host type system. The architectural milestones below track that work.

| ID | Work | Status | Done when |
| --- | --- | --- | --- |
| R1 | Uses of `TParam`, inference `TVar`, and hidden witnesses preserve rigidity, scope, and identity | done | Specific forbidden transitions and escapes fail (a parameter is not solved as `?T`; a hidden witness does not become another object's; a captured/loop-escaped witness keeps its identity). Legitimate repeated uses of the *same* hidden witness still check. Not a wholesale TVar rewrite. |
| R2 | Propose vs validate, **and** later uses respect the snapshot | done | A subtype/expansion result is valid against an explicit snapshot **and** subsequent uses of that result respect the same snapshot, or the judgment is revalidated when a recorded dependency changes. Exporting a closed record under the subst at validation time does **not** count: that stabilizes the *exported* record, not SKJS's earlier acceptance. |
| R3a | Expansion keys identify the resolved declaration, not spelling | done | [expansion-key-collision](deep-dives/issues/expansion-key-collision.md): same-named aliases from different modules no longer share a cache entry; the unsound call is rejected; renaming the local alias still rejects; valid uses of each definition still check |
| R3b | Substitution-dependent answers track what can invalidate them | done | [freeze-window](deep-dives/issues/freeze-window-stale-memo-caches.md): a memo written while a candidate is unsealed is not reused after that candidate grows; the order-dependent acceptance is gone; the program without the priming call still rejects |
| R3c | Speculative clone results authorize the parent only with a justified transfer | done | A clone that does not commit cannot make the parent accept; any transfer of a clone result is justified by an explicit obligation |
| M1 | Alias writes: a narrow alias must not promise contents another alias may legally overwrite (`L-MUT-ALIAS`) | done | Reduced [narrowed-alias-stale-write](deep-dives/issues/narrowed-alias-stale-write.md) programs are rejected; a positive counterpart with a shared invariant still checks |
| M2 | Stale captured reads: a creation-time narrowing is not a captured arrow guarantee (`L-STALE-READ`) | done | Reduced [stale-closure-reads](deep-dives/issues/stale-closure-reads-narrowing.md) programs are rejected; a snapshot-or-null-check counterpart still checks |
| M3 | Loop-carried narrowing (`L-LOOP-CARRIED`) | done | SKJS rejects the [loop-carried](deep-dives/issues/loop-carried-narrowing-stale.md) reduction using its existing language and tests. Independent pipeline coverage of `let` is **not** a prerequisite. A counterpart that remains correct under SKJS's own loop checking (not source-level supplied invariants) still checks |

## Architectural end state

The objective is a checker whose implementation explains the three variable
roles clearly and whose interfaces exclude misuse wherever practical. Completion
means fewer dangerous capabilities and caller obligations, not more mode flags,
wrappers or regression examples around the same unrestricted state.

### Current gap

`TParam` and `TVar` are separate, and parameter identity includes `ParamOrigin`.
A1 now restricts solver/witness allocation to owner-controlled serials and
protects identity payloads, binding storage and mutation counters from ordinary
callers. Declared parameters and hidden witnesses still share rigid algebra;
owner/scope checks remain partly dynamic. Array representation selectors now
have an opaque API distinct from value candidates, as described below.
`Subst` combines candidate storage, commitments, rollback, query dependencies,
caches and diagnostic/export state. A2 completed restricted committed shape
observation, including its algebra and declaration backend. Its raw transaction
kernel is private; consumers receive `TypeReadContext`. A3 now separates ordinary
inference from the validation and publication of subtype/call judgments.
`TType.isSub_` still proposes candidate growth, seals dependencies, establishes
literal representations and checks the relation in one mutable transaction.
Those mechanisms have been audited; their interfaces are not the target design.

### Responsibilities and permitted interaction

| Component | Capability | Must not be able to do |
| --- | --- | --- |
| Variable identities and scopes | Allocate declared parameters, solver candidates and scoped hidden witnesses through role-specific factories; preserve identities through renaming | Solve a rigid parameter, forge/reuse a hidden witness, or confuse a literal representation selector with an ordinary candidate |
| Inference engine | Propose candidates, constraints and representation choices; retry after validation feedback | Turn proposal success into acceptance, mutate established dependencies without preserving obligations, or construct validated results |
| Validation context | Read explicit assumptions and candidate interpretations through a restricted interface; compute judgments and their dependencies | Allocate/solve candidates, choose a literal representation, or reach the owner's mutable solver through a back door |
| Commitment/publication boundary | Check dependencies against their owner and transaction, establish required commitments, then release a retained result | Publish scratch-local evidence, a stale decision or a result whose provenance was discarded |
| Query machinery | Maintain recursion assumptions, dependency tracking and caches local to justified contexts | Treat a conditional recursive answer as unconditional or transfer caches independently of their justification |
| Diagnostics and export | Inspect an appropriate view and report outcomes | Manufacture acceptance authority or feed display approximations back into validation |

Inference and validation communicate; they are not independent algorithms.
The driver may propose, validate, commit or retry. Validation may return an
unsatisfied constraint or an inability to establish a shape. It must not silently
solve that problem itself. Changing an inference heuristic may change which
valid programs are found, but cannot change what counts as valid evidence.
Recursive bookkeeping and caches may remain mutable inside validation; semantic
candidate state is what the restricted interface must prevent it from mutating.

Do not require all candidates to be globally closed. A judgment can retain
symbolic dependencies under explicit assumptions. Publication must preserve
those assumptions: commit inspected payloads, retain justified symbolic operands,
or retain an obligation that is revalidated before further reliance. Inference
choices never change an allocated runtime location's fixed world type.

Use separate variants/identifier types and restricted constructors where they
exclude real misuse. Rigid universal parameters and existential witnesses may
share algebraic operations when their identity and scope rules are preserved;
three semantic roles do not require three copies of the type algebra. Distinguish
ordinary inference, field construction and literal selectors within solver state
where their legal transitions differ. Computation purpose (checking, probe,
diagnostic) is independent of variable role.

### Planned milestones

These are architectural milestones A1–A4, separate from completed repair rows
R1–R3/M1–M3. A1–A2 are **done**; A3 is **in progress**; A4 is **not started**.
Names below describe responsibilities, not prescribed new class names.

| ID | Deliverable | Closure evidence |
| --- | --- | --- |
| A1 | Restrict variable creation and state transitions | Role-specific factories and private storage prevent ordinary callers from minting witnesses or writing candidate bindings directly. Solver operations cannot accept rigid IDs. Candidate/field/selector transitions are explicit. Existing identity, escape, rollback and literal controls pass; any necessary dynamic scope/owner checks are centralized and documented. |
| A2 | Introduce validation read capabilities | Migrate committed shape observation end to end so callbacks receive a restricted context, with no solver mutation or mutable-owner accessor. Reads still collect transitive dependencies; blocked, unavailable and negative decisions remain distinct. Existing owner/clone/rollback controls pass without relying on callbacks voluntarily avoiding mutators. |
| A3 | Separate proposals, checking and publication | Split ordinary subtype/call processing into explicit proposal, validation and commitment responsibilities using A1/A2. Validation cannot call growth or representation-selection APIs. Retained positive/negative judgments and materialized shapes pass through justified publication; symbolic results remain symbolic where appropriate. A call fixed point or a generic success wrapper is not sufficient. |
| A4 | Migrate consumers and retire unrestricted paths | Complete the existing consumer/cache/clone inventory against the new interfaces; remove superseded mutable entry points, modes and duplicate mechanisms where their purpose has been replaced. Qualify all source outcomes, native protocols, independent suites, census changes and performance. Report remaining trusted/dynamic checks explicitly. |

Start with the allocation/mutation entry points in `TType.sk` and
`TTypeSubst.sk`, then the observation boundary in `TTypeObservation.sk` and
`TTypeSubst.sk`. Use one existing shape consumer as the first complete A2
migration, including its commitment path. A facade that internally hands the
same unrestricted owner to the callback does not complete A2. For A3, use
`TTypeSubtyping.sk` and the call driver to separate proposal effects from the
relation checked; include literal selectors, negative decisions and retained
constructor results, not just the final Boolean. Reuse the consumer inventory
and regression responsibilities in this guide for A4.

### A1 checkpoint: owner-state and identity access

Implemented in the first slice:

- Binding/origin maps and the inference-version/owner-epoch counters are
  protected within the substitution-state implementation. Ordinary consumers
  use read-only counters; exporters receive an immutable map value through
  `bindingsForExport`. Neither a direct write nor a `with` update of a saved
  state's protected fields is available to ordinary callers.
- Solver-ID factories and the hidden-witness factory consume serials from the
  supplied owner; they no longer accept caller-chosen integers. The serial
  allocators perform the existing observation/mutation or clone checks. Witness
  enumeration is limited to the owner's allocated range. An allocation request
  may consume a serial, but a returned integer cannot construct an identity.
- Identity payloads are private/protected, so a `with` update cannot change an
  ordinary parameter's origin to hidden or replace a solver serial. Rigid
  parameters remain inadmissible to the solver's `TVar` argument.
- Native fixtures use production growth/sealing operations, with no test-only
  writable-store API. The old uninstrumented-store-mutation fixture instead
  tests mismatched payload rejection at the read frame itself. Snapshot testing
  uses legal growth and retains the immutable-snapshot assertion.

Negative compilation probes confirmed rejection of all eight attempted bypasses:
live binding write, epoch write, caller-chosen candidate/witness serials,
witness-origin rewrite, solver-serial rewrite, solving a rigid parameter, and
saved-binding replacement. The temporary probe was removed after checking;
there are no intentionally uncompilable files in the source tree.

Validation: all 211 checker tests and 65 independent verifier suites pass;
the curated corpus retains 278 proofs with zero unexpected outcomes. Three
isolated paired rounds retain exact diagnostics. Median seconds before/after:
array 0.734/0.721, generic membership 1.074/1.068, deep collection 5.369/5.267.
No TypeScript source regression was added or regrouped, so the repair-census
selection and baseline remain unchanged; native tests are not corpus rows.

The second slice separates representation selection from contextual element
inference. `TArrayLit` and `TType.arrayLit` require `ArrayLiteralSelector`, whose
private backing variable is allocated through its owner. Its interface allows
tracked reads, snapshot inspection, and one-shot commitment; it exposes no
candidate, ID, growth, or occurrence-constraint operation. A selector cannot be
passed to `Subst.grow` or `TType.var`, and a general candidate cannot construct a
delayed literal. The owner still supplies storage, mutation tracking, freezing
and rollback through the existing implementation. This is API separation, not a
new proof of representation validity: the literal checker must still validate
the chosen type against the elements.

`TVIDForLiteralCommitment`/`genForLiteralCommitment` and their helper are renamed
to contextual-element names, with unchanged growth/sealing policy. These value
variables may widen before sealing; a selector only chooses once. Type
transformers preserve selector identity and no longer map fictitious selector
constraints. Escape traversal and export use snapshot inspection without
obtaining its backing candidate. Existing literal-intersection and hidden-escape
tests now construct actual selectors. The transition test covers choice while
candidates are frozen, resistance to replacement, and enclosing rollback.

Validation of this slice: 212 checker tests, 65 independent verifier suites,
and the unchanged 278 curated proofs pass. Five negative compilation probes
reject candidate-as-selector construction, selector growth, selector-as-value
construction, backing-candidate access, and backing-candidate replacement. The
probe source was removed. Three paired performance rounds have identical
outputs; median seconds before/after are array 0.793/0.790, generic membership
1.129/1.161, and deep collection 5.556/5.598. No source corpus fixtures changed.

The identity audit also closes an ordinary-variable construction route:
`TVar` factories now require an owner and allocate the requested role directly.
They no longer accept an existing `TVarID`. The variable's identity field is
protected, with read-only `identity()` inspection, so a record update cannot
replace its identity or role. Occurrence-constraint transformations preserve the
same identity. Export snapshots remain data, not a source of constructible live
variables.

The current owner implements these transitions centrally in `grow`, `get`,
and `commitObservedBindings`:

| Role/state | Permitted transition |
| --- | --- |
| Unbound ordinary, field or contextual element | Lower-bound growth opens a binding; expected-type growth seals it. |
| Open ordinary candidate | Lower-bound growth may union before freezing; expected-type growth cannot replace it; covariant read seals unless frozen. |
| Open field or contextual element | Context may union and seal the value, including while ordinary candidates are frozen. |
| Closed binding | Further growth cannot replace it. |
| Literal selector | Its opaque API exposes only unbound-to-sealed choice, tracked read, and snapshot inspection. |
| Rigid parameter or hidden witness | No solver binding transition exists. |

Save/restore preserves this state machine but rewinds candidate identities and
bindings together. Abandoned speculative values must not escape rollback.
Cross-owner use is still a caller lifetime obligation, not a statically checked
owner brand. This applies to independent checking roots and to abandoning values
when rolling back; the construction milestone does not prove those lifetimes.

Hidden-witness allocation is disabled by default on every substitution. Only
`createCheckingOwner`, taking a light environment with no candidate owner,
enables a fresh namespace. Source checking roots use that constructor; ordinary
`mcreate`, saved-diagnostic reconstruction, clones, probes and observation state
cannot mint witnesses. The runtime check is centralized in the serial allocator,
and the counter never rewinds with solver state. This replaces repeated clone
sentinels with one safe default. The sole production minting path remains
`TEnv.makeSkolemTArgsOf`, reached from instance narrowing. A native regression
covers detached normalization with and without saved state, saved diagnostics,
ordinary and diagnostic clones, plus successful fresh allocation by the owner.
The first three routes previously restarted the namespace; no production source
acceptance bug was demonstrated through them.

Final A1 validation: 213 checker tests, 65 independent verifier suites, and
278 curated proofs pass with no unexpected producer or proof outcomes. The
identity factory/update bypasses are compiler-rejected. The additional test is
native; no source corpus selection or census baseline changed. Earlier paired
performance qualification remains recorded above; no new timing claim is made
for the final identity/allocator access changes.

A1's construction/transition milestone is complete within these explicit trust
boundaries. Candidate state and identity replacement are unavailable to ordinary
callers; role-specific creation, selector commitment and value growth are
separate; rigid IDs cannot enter the solver. Occurrence constraints preserve
identity. Clone/rollback/escape and literal controls remain required tests.
The A2 closure below records the subsequent migration of committed shape
observations. A3–A4 still cover ordinary inference and its wider consumer migration.

Remaining dynamic enforcement includes checking-owner authority for witness
allocation, checkpoint validity, observation read/commit checks, and save/restore
lifetimes. The mutable state hierarchy is trusted implementation, not a security
boundary against adding privileged subclasses/extensions. No source acceptance
or wire-format change is intended by these access-control milestones.

### A2 closure: restricted shape observation

Committed shape observation uses `TypeReadContext` end to end. The context has
no allocation, growth, sealing, literal-selection, solver-cloning or mutable-owner
accessor. Its fixed-read subtype and intersection orchestration shares structural
rules with inference; it does not call inference's proposal or growth machinery.
Symbolic members remain symbolic until an operation actually inspects them.
Unknown payloads block instead of receiving inference defaults.

| Boundary | Implementation and evidence |
| --- | --- |
| Publication | `Subst.withCommittedReadContext` / `withCommittedReadDecision` create the capability. The private transaction kernel collects transitive reads and checks every binding before sealing any. Owner epoch/freeze checks refuse stale transfers. |
| Variadic shapes | All four `TVariadicTyping` consumers use the context: optional tuple, retained tuple absence, rest element, and combined call-rest shape. Optional absence commits nothing; retained negative decisions commit their reads; Blocked cannot authorize a fallback. |
| Refinement | `TypeCheckRefine` establishes head expansion before transforming it without re-entering inference expansion. `TypeCheckScope` branch elimination receives only the read context; uncertainty retains an alternative. Ordinary source checking and refinement construction remain distinct from the committed head observation. |
| Type algebra | Fixed-payload expansion, selector reads, subtype/intersection orchestration, occurrence constraints, disjointness and iterator/member projection are in `TTypeObservation`. Union, clause distribution, field assembly and callback rules share solver-free structural helpers with inference. Recursive premises and query qualification retain their lifetime rules. |
| Declaration normalization | `TypeReadDeclaration` carries declaration lookup, diagnostics and the active context, not a candidate owner. Class/alias construction, signature normalization, heritage aliases, enum types, rest constraints, symbol carriers and primitive boxing borrow the same snapshot/read frame across lexical environment changes. |
| Materialization | `TEnv.materializeReadContext` separates the checking callback from detached probe/diagnostic callbacks before dispatch. Index merges, constrained parameters, templates, mapped/computed keys, `keyof`, numeric indexing, `Closed<T>`, receiver classification and `typeof` projections use this boundary. |
| Retirement | The raw materialization helpers and raw decision helper are removed. `withCommittedTypeReads` is private and has one production caller, the context factory. Fault injection uses extensions compiled only into the native test binary. |

Compatibility probes may solve detached state only to report diagnostics: no
solved type, environment or success receipt returns to declaration construction.
Diagnostic rendering returns text only. Explicit source type arguments retain
live constraint checking; separating those ordinary inference proposals belongs
to A3. Computation purpose remains independent of variable role.

The capability's record copies and borrowed declaration scopes share a private
lifetime cell. Normal return and exceptions expire it, so a retained handle
cannot add reads after publication. `Subst::mcreate` refuses a declaration-only
context rather than inventing an empty candidate store. These are dynamic
backstops; Skip does not provide a static ownership/lifetime proof. The private
scratch still owns query bookkeeping and caches, whose isolated descendants
share the same read frame. Restoring caches cannot import untracked owner facts.

Seven compiler-negative probes reject raw transaction access, the removed raw
decision and materialization helpers, extraction of the context's scratch or the
declaration's reader, passing a read context as a solver, and use of test-only
fault-injection wrappers from production code. Temporary probe source is removed
before building and testing the restored tree. Privileged class extensions are
trusted implementation, not a security boundary against malicious repository edits.

`tests/TypeReadObservation.sk` covers commitment, Blocked versus Unavailable,
retained negatives, atomic frozen transfer, owner rollback, nested clones, cache
provenance, symbolic rest members, literal selection, callback comparison and
normal/exceptional lifetime expiry. The declaration regression normalizes two
`keyof` projections under borrowed lexical bindings: a late unknown commits
neither read; resolving it commits both; the escaped declaration handle then
refuses normalization and solver creation. `tests/TypeConstruction.sk` checks
structural algebra against its inference adapters without solving symbolic operands.

Final qualification: 222 checker tests and all 65 independent verifier suites
pass. Curated outcomes remain 278 verified, 9 search failures and 18 unavailable,
with zero mismatches or runner errors. Formatting and shell checks pass. Three
alternating paired runs under a 4 GiB limit preserve exact diagnostics and finish
within the 20-second per-file bound. Median seconds before/after the closure are
0.769/0.776 for array literals, 1.152/1.156 for generic membership and 5.429/5.661
for deep collections. The last control is about 4% slower in this sample; these
bounded checks show comparable performance, not identical timing or a general
performance guarantee. No TypeScript source fixtures or corpus-selection inputs
changed in this closure; native protocol tests are outside the repair census.

A2 closes the committed shape-observation boundary, not the full architectural
refactoring. A3 still separates ordinary subtype/call proposals, validation and
publication. A4 completes that wider consumer migration and retires the remaining
inference interfaces. Existing lifetime, owner and rollback controls remain
necessary; an arbitrary callback result is not a proof certificate.

### A3 execution plan

A3 must replace the mixed acceptance path, not merely run another check beside
it or rename `isSub`. The following work remains one milestone:

1. **Positive subtype validation.** Distinguish exact source/shape dependencies
   from monotone target lower bounds. Run the restricted relation without growth,
   publish only a proved positive judgment, and preserve symbolic operands.
   A failed proof is not a retained negative fact. Existing fixed shape/negative
   observations retain their stronger commitment policy.
2. **Subtype proposal driver.** Separate candidate growth, literal representation
   proposals and speculative constraint discovery from acceptance. Proposal success
   is not proof. Recursive proposal paths must not publish accepted judgments,
   export claims or call-graph edges before validation. Preserve constraint
   obligations and rollback; do not close every candidate to force a proof.
3. **Call publication.** Collect receiver, positional, optional and rest obligations
   after generic instantiation. Inference may iterate, but returning a call or
   constructor result requires validation of the whole applicable obligation set
   in one consistent state. Include literal choices and explicit/dependent bounds.
4. **Representative integration and qualification.** Exercise failed/reordered
   proposals, callback variance, symbolic results, constructor results and owner
   rollback through the real drivers. Retained negative decisions still require
   justified dependencies. Compare source outcomes, verifier results and named
   performance controls before declaring A3 complete. A4 then handles the wider
   remaining consumer inventory and retirement of superseded interfaces.

The first implementation provides `Subst.proveSubtype`, which runs an actual
restricted positive relation rather than an arbitrary callback. Source reads and
shape operations still require exact payloads. Reads of the positive relation's
target carry lower-bound dependencies; publication checks those against the same
snapshot but leaves them open. Legal `Subst.grow` preserves a bound by union;
contravariant callback/field positions swap sides and therefore acquire fixed
source dependencies where needed. Any dependency also read exactly is still
sealed. Missing interpretations block; false comparisons publish no commitments.
Probes and diagnostics cannot use this checking publication entry point.

This is a validation primitive, **not completion of A3**: the ordinary `TType.isSub`
and call drivers still mix proposal and checking. Their migration, representation
proposals, constraint obligations and deferred publication remain required.

### Acceptance criteria and migration discipline

- For each migrated boundary, state which misuse has become unrepresentable,
  which runtime check remains, and who owns it. Prefer compiler-enforced access
  restrictions. Where Skip cannot express a lifetime/ownership restriction,
  keep the check at one narrow boundary rather than claiming static enforcement.
- Private validated-result construction, if introduced, must correspond to an
  actual judgment and its dependency lifetime. Wrapping an arbitrary callback
  result, an already materialized type or an immutable snapshot is not evidence.
  No success object may outlive rollback or cross owners without justification.
- Preserve the recursive-premise publication rules, transitive read tracking,
  monotone target-growth justification, and symbolic intersection fallback.
  Read-only access by itself proves neither subtyping nor future stability.
- Use small, green implementation slices, but judge completion end to end.
  Temporary adapters must have named remaining callers and be retired in A4;
  do not leave two competing sources of truth. Avoid parallel type algebras and
  unnecessary wire-format changes. Keep independently demonstrated behavior
  repairs separate from behavior-preserving interface changes.
- Reuse the meaningful existing tests. Add tests for new capability boundaries
  or genuinely different failures, not copies of previous examples. Verify that
  changing/reordering proposals cannot bypass validation, that rejected proposals
  cannot publish, and that positive inference controls retain their behavior.
- Run the full checker suite for code changes, independent pipeline regression
  gates at coherent checkpoints, and the repair census when source tests change.
  Keep the three named performance controls and broaden qualification at A4.
  Do not reintroduce whole-store snapshot memo keys or blanket invalidation that
  caused the earlier OOM/slowdown. Inspect diagnostic and acceptance differences;
  do not silently update expectations to accommodate regressions.

The end state is reached when the old mutable validation route is retired,
variable-role misuse is excluded as far as Skip permits, and the remaining
correctness argument is concentrated in the validator and publication boundary.
A proof of the entire checker and broader language support remain separate work;
passing the old bounded audit does not close A1–A4.

## Validation lifetime closure audit (2026-09-19)

Through `f2b59831`, this closes the current implementation audit for R2/R3c.
It is a source-level argument over the boundaries below, supported by regression tests; it is not a
Lean proof of the full checker or completion of the alias/effect work in M1.
The current architecture below consolidates the earlier checkpoint notes; Git
history retains the individual counterexamples and intermediate measurements.

The lifetime rule has three cases. A materialized decision commits every
inspected candidate payload in its actual owner before publication. A symbolic
construction retains its original operands instead of fixing a provisional
answer. A normal successful subtype check retains its live commitments: source
reads are covariant, parameter/setter checks reverse the relation, and remaining
positive target growth only widens the admitted set. Closing one outer candidate
is not enough; these rules apply again whenever a nested dependency is inspected.
The callback-variance regression checks that the negative dependencies close
while a positive result candidate can still grow without invalidating success.

| Boundary | Why a retained result survives |
| --- | --- |
| Named expansion and source normalization | `materializeRead` observes a fixed snapshot with fresh scratch caches and no inherited caller proof assumptions. Descendants share the read frame; the actual owner commits matching payloads before return. Uninspected children remain symbolic. `expandNamed` is the single memoizing publication path. |
| Explicit type arguments and call checking | Written constraints validate live, including phantom aliases and constructor arguments. Inference proposes bounds; the argument pass checks them. Its fixed point provides call-local consistency; later lifetime follows from the same commitments and variance rule as every successful subtype check. |
| Defaults and definite assignment | Both positive and negative `materializeSubtypeDecision` results have owner-committed dependencies. Observed subtyping skips `growTVars`: deciding whether an existing type admits `undefined` must not propose a new solution. Default-result projections establish literal forms before retaining their shape. |
| Refinement and alternative elimination | Equality, subtraction, truthiness and head-shape projections use committed observations. An unjustified optional refinement keeps the original type. Branch elimination observes all descendant reads and commits them before discarding an alternative. |
| Variadic/callback shape extraction | The tuple/rest/callback shape observations include the raw-binding fallback. Failure to establish a read cannot select a more permissive fallback. The extracted element types may remain symbolic. |
| Delayed array literals and `await` | A selector is a representation choice, not monotone lower-bound growth. Subtype validation establishes its array/tuple form, including through aliases, unions and intersections. Awaited flattening establishes inspected literal forms while preserving unresolved ordinary candidates. Provisional defaults cannot justify retained intersections or query caches. |
| Successful subtype alternatives | Successful branches retain their commitments. Failed alternatives restore values and caches together. `growTVars.isCovered` probes only guide proposals; live checking validates the final relation. A redundant-constraint shortcut additionally requires no shared mutation and reusable query dependencies. |
| Remaining speculative clones | `instanceof` preservation returns the original branch, not the clone's solved type; the other branch uses fresh rigid witnesses. Literal-precision probes choose element guidance followed by live element validation. Detached declaration probes return no type result; rigid declaration checking and retained argument constraints justify use. Diagnostic overlap, display and advice do not authorize acceptance. |
| Hidden escape raw reads | Raw traversal installs no rebuilt type. Persistent symbolic roots are retained and rechecked after later inference growth, under the existing R1 boundary. |
| Runtime value projections | Destructuring/property reads and object/array spread extract current values or allocate copies. Nested types retain their identities; covariant candidate reads establish inspected payloads. Retained alias-shape projections, notably mixed `await`, additionally establish literal selectors. Mutation of runtime objects is the separate M1 obligation. |

The cache argument is compositional, not an entire-substitution cache key:

- `seenUnion` combines symbolic inputs. `seenExpansion` uses resolved declaration
  identity and the observation publication boundary.
- `seenSub` retains committed source/negative dependencies and permits monotone
  positive target growth. Equality of the same symbolic type and admission to
  top need no payload read. Recursive premises have scoped publication rules;
  a child depending on an ancestor's unfinished premise cannot publish it.
- `seenInter` may publish only reusable computations. Frozen candidate reads
  and uncommitted literal defaults mark the shared query frame provisional,
  even across scratch clones and freeze-mode exit. Retained constructors use
  `interForTypeConstruction` to preserve operands when simplification is not
  justified for later reuse.
- Rollback restores candidate values and caches together. Observation frames,
  provisional-read counters and mutation stamps cannot rewind with a failed
  alternative. Scratch caches never transfer to the owner.

The source counterexamples in `literal-representation-lifetime.ts` distinguish a
structural length view, a conditional alias, and a mixed awaited projection.
Previously SKJS accepted a return contract of `1` although growing the same
array made the returned length `2`. The repaired checker rejects those promises;
the corresponding numeric-length views remain usable. Existing contextual
single/union tuple tests and generic async inference remain positive controls.
Native tests cover stale literal intersections, observed validation without
inference, callback variance, recursive publication, rollback and clone reads.

Final gates: 211 checker tests passed; 65 independent verifier suites passed;
the 64-file example run retained 278 proofs with zero expected-outcome
mismatches or runner errors. That verifier run checks the existing corpus; it
does not independently certify these new checker repairs. No extracted Lean
programs or verification-language changes were needed.

Three isolated before/after rounds under a 4 GB container limit retained
identical diagnostics. Median times before/after the final projection repair
were 0.709/0.715 seconds for `array_literal_examples.ts`, 1.058/1.056 seconds for
`instanceof-generic-skolem-args.ts`, and 5.209/5.174 seconds for
`eagercollection-deep-value-no-oom.ts`. These are bounded performance gates,
not a whole-corpus complexity guarantee. The withdrawn whole-snapshot memo
policy was not reintroduced.

### Extension rule

For a new typing consumer, identify what escapes: a value type, an eliminated
alternative, a negative decision, or a cached success. Use committed observation
for materialized facts, preserve symbolic operands when simplifying is
provisional, or validate live and explain the variance/commitment lifetime.
A detached clone's success, a call-local fixed point, an exported closed record,
and a green suite are not substitutes for that argument. Representation
selectors must be fixed before their default shapes escape; ordinary monotone
candidate growth must not be confused with changing that representation.

New counterexamples reopen the affected boundary. These completion criteria
do not assert that SKJS is globally sound or complete.

## Mutation and alias boundary audit (2026-09-20)

Through `ef5416fb`, milestone 2 closes M1 for the checked data-object subset.
This is an implementation audit, not a whole-language soundness theorem. The
obligation is that a lasting alias cannot promise a temporary contents fact,
and that a runtime write or call cannot leave such a fact available for later
reads or condition replay. This section states the current scope.

| Boundary | Rule and evidence |
| --- | --- |
| Alias publication | Declarations, assignments, returns, arguments, receivers, selections and copied object-valued fields use stable contents contracts. Scalar reads are values and may retain their point type. Existing alias, object-literal, pattern, spread/rest and receiver regressions cover these paths. |
| Visible writes | Property/index writes, compound assignments and updates invalidate transient contents on contracted aliases; destination write contracts remain fixed. Primitive snapshots and known non-null references are retained. |
| Explicit execution | Calls, construction and suspension use `invalidateCallEffects`. Captured locals that may be reassigned widen to their contract. Condition replay uses observation epochs so a pre-effect guard cannot become a post-effect fact. |
| Iteration | Acquisition, advancement and closing invalidate at the relevant array/argument spread, destructuring and `for…of` boundaries. Existing iterator regressions cover body entry, exhaustion/closing and later call arguments. |
| Membership hooks | `instanceof` is an implicit call effect, including in keys and condition summaries. Visible `Symbol.hasInstance` hooks use the same argument, receiver, generic and fixed-point call validation as explicit calls. Arguments are already evaluated, so validation cannot replay their effects. Runtime truthiness converts the result; no Boolean-return assumption is imposed. |
| Growing objects and constructors | A local object's first read/escape establishes its shared contents contract. Captured writes establish that contract too. Prior initialization is not mistaken for an established-object refinement. Batched probes rejected callback invalidation of a newly built object, escape of an incomplete constructor object to a stronger parameter, and admission of a broader writable alias to a narrower initialized slot. These overlap existing contract/growth tests and were not duplicated. |
| Other implicit operations | Arithmetic, relational and template conversion accept primitive domains, so they cannot invoke a user object's coercion hooks. Data-property reads, `in`, object copying and key enumeration have no user execution under the data-object interpretation below. Getter/proxy semantics are not silently treated as this case. |

The new witnesses in `implicit-instanceof-effects.ts` cover a later field read,
replay of an earlier conjunct, a computed-key read retaining its evaluated
receiver, and an incompatible hook argument. The first three previously
promised `number` after the hook wrote null; the last could invoke a numeric
method on a missing field. All now reject. Scalar snapshots, fresh checks and
compatible hook arguments pass. Existing ordinary-class membership and custom
membership-narrowing tests remain green.

Final qualification found one additional protocol boundary: a structural
constructor or `Function` view could omit a restrictive `Symbol.hasInstance`,
then admit an incompatible operand. `f29516c2` makes function-like subtyping
preserve that hook. Compatible explicit protocols and opaque object views remain
accepted. Both unsafe conversions are accepted by strict tsc; the regressions
are in `membership-protocol-erasure.ts`. This also makes the limit of the previous
visible-hook audit explicit: checking a use is insufficient if an earlier
conversion can discard the contract that must be checked.

### Scope of the object contract

The current checked language creates data properties and rejects accessor
declarations. Its stubs do not supply proxy/reflection construction operations.
As in the semantic model's caller interpretation, an object input satisfies a
data-field contract; a structural TypeScript annotation alone does not prove
that an arbitrary unchecked JavaScript object has data properties. This audit
therefore does **not** cover externally supplied getters, setters, proxies or
monkey-patched built-ins. This is an explicit language/interoperability boundary,
not evidence that such operations are pure. Supporting them requires modeling
execution at reads/writes and repeated-read stability, rather than merely
invalidating after a getter has already consumed an unjustified refinement.

For a new operation that can execute user code, add its execution boundary and
its syntactic effect summary together. Use stable operand/receiver contracts
when operands were evaluated before the effect. Preserve the distinction
between scalar snapshots and aliases, and between initialization and observation.
Do not use tests passing under a plain-data assumption as evidence about
accessor/proxy behavior.

Validation: 211 checker tests, 65 verifier suites and the existing 278 example
proofs pass with zero unexpected outcomes. Three bounded timing rounds retained
identical diagnostics; median before/after seconds were 0.743/0.750 (arrays),
1.070/1.065 (generic membership), and 5.202/5.264 (deep collection). These are
regression controls, not a whole-corpus complexity guarantee. The repair census is reported in
[Repair coverage](../verification/REPAIR-COVERAGE.md). Unsupported language
features and general type-rule completeness are not implied complete by these
lifecycle audits.

## Native ownership boundaries

The implementation uses three different notions of change. Keep them distinct:

| State | Purpose |
| --- | --- |
| `Subst.version` | Progress of the live call-inference fixed point. |
| Owner `semanticEpoch` and matching payloads | Transfer of an observed result back to the owner that supplied its dependencies. |
| Shared `typeMutationStamp()` | Whether a query or scratch descendant changed candidate state, including changes later rolled back. Cache-only restore is not candidate mutation. |

### Contract implemented by observation

`TEnv.materializeRead` and `Subst.withCommittedTypeDecision` run a shape
operation in isolated state. All scratch descendants share one read frame.
Before a result escapes, every inspected candidate payload must still match
and be committed in the actual owner. Uninspected symbolic members stay open;
observing `Array<E>` must not determine `E` without inspecting it.

- Normalize source operands in the checking environment before observation.
  Explicit type-argument constraints and live `typeof` checks remain mandatory.
- A negative shape decision is still a result with dependencies. Blocked reads
  must not silently choose a permissive fallback. Optional absence and inability
  to establish a read are distinct outcomes.
- Recursive normalization preserves the observation's own guards. Caller proof
  assumptions are cleared only at entry, never on every nested expansion.
- Named expansion has one publication path, `TEnv.expandNamed`; direct
  instantiation is gated too. An expansion cache entry is justified by its
  publication and transactional lifetime, not by its immutable result alone.
- Speculative type-argument checks and diagnostics have explicit detached
  purposes, preserved through cloning and restore. Their answers and caches
  cannot authorize the checking owner. Probe callbacks return no type result.
- Observed restore clears imported caches and retains the read frame. Ordinary
  rollback must abandon derived answers together with their commitments.
- Keep the void-typed exception boundary with `SubstReadCell`: a generic result
  crossing try/catch in a mutable generic method crashed the Skip compiler.

Implemented consumers include call/function-rest layouts and element projections,
named expansion, direct instantiation, `keyof`, numeric indexed access, `Closed`,
template and mapped-key classification, index/computed-key classification,
union/intersection construction, declaration `typeof`, and function normalization.
Tests: `TypeReadObservation.sk`, `observed-rest-shape.ts`,
`observed-array-rest.ts`, `observed-rest-subtyping.ts`,
`observed-indexed-normalization.ts`, `observed-normalization-boundaries.ts`,
and `normalization-owner.ts`.

### Recursive and provisional query dependencies

Subtype and intersection query scopes record which recursive premises they
introduce and consume. A child depending on an unfinished ancestor cannot
publish independently. A successful enclosing computation can discharge its own
premises; failure and exceptions cannot. Dependencies from outside the active
query tree remain unresolved. This relies on the existing coinductive algorithm;
it is not a proof of that algorithm.

`TypeQueryReads.provisional` records frozen unsealed reads and uncommitted literal
defaults. It is shared with scratch descendants and survives rollback and leaving
frozen mode. A closed outer candidate does not hide an inspected open child.
A later independent fixed query remains eligible for reuse. This qualification
tracks actual dependencies rather than invalidating every answer after every
substitution change.

`interForTypeConstruction` preserves symbolic operands when an eager intersection
is provisional. For example, `(T & number)[T := a]` must retain `a & number`:
current numeric contents of `a` cannot erase the numeric constraint, and current
string contents cannot permanently collapse it to `never`. Field reads/writes,
callback inputs and generic bounds use this boundary when constructing retained
types. Temporary solver queries still use ordinary intersection.

`ArrayLitTyping.establishLiteralForms` commits representation selectors before
subtype validation, defaults or awaited projections retain their shapes. Tuple
contexts select tuples; other contexts select arrays. Ordinary generic candidates
can remain symbolic. An observational read never proposes new inference growth.
Rollback abandons representation choices with the failed judgment.

### Performance constraints

The whole-snapshot memo policy introduced in `065d419b` was withdrawn: the array
fixture exceeded 4 GB and failed to complete. A separate freeze-window slowdown
introduced in `68c3b742` took that fixture from about 0.5 to 5 seconds. Tracking
actual unsealed reads repaired that blanket exclusion. Recursive premise scopes
subsequently raised the array cost to roughly 0.7 seconds and the generic
membership fixture to roughly 1 second; those are explicit correctness costs.
Do not recover speed by publishing conditional answers without justification.

Keep `array_literal_examples.ts`, `instanceof-generic-skolem-args.ts` and
`eagercollection-deep-value-no-oom.ts` as cost controls. Before a broad scan,
exercise its harness on a completing control, an expected diagnostic and a
timeout/error. Separate rejection, timeout, kill and harness failure. Skip reserves
16 GiB of virtual address space: use a container memory limit, not `ulimit -v`.
Use the same source and compare diagnostics as well as timings. A failed or empty
scan is not evidence of no regressions.

## Hidden identity and escape boundaries

R1 is a bounded source audit backed by escape regressions, not a theorem about
all generic programs. Only solver candidates may be solved; rigid parameters
and fixed hidden witnesses retain their identities and bounds.

| Boundary | Established rule and evidence |
| --- | --- |
| Hidden identity creation | `evalInstanceof` is the sole consumer of hidden argument creation. `genSkolemTParam` never rewinds on rollback and refuses creation in a speculative clone. Different discoveries therefore do not reuse an identity within a substitution. |
| Parameter bounds | Declaration parameters stay rigid; inferred arguments remain candidates; hidden arguments are rigid identities. Later bounds refer to the corresponding earlier arguments. `hidden-dependent-bounds.ts` exercises same-witness inclusion, forbidden reversal, cross-witness writes and constructor inference. |
| Callback publication | The complete signature and enclosing bindings are retained as escape roots. This includes contextual parameters supplied by a temporary generic receiver and explicit `typeof` results. `contextual-hidden-escape.ts` and the closure cases in `instanceof-generic-skolem-args.ts` distinguish escaping identities from opaque results and invocation-local inference. |
| Repeated execution | While/for checks include conditions and increments; for initializers persist, while for-in/of iteration bindings are fresh. Persistent binding roots reject pooling; per-iteration containers remain accepted in `instanceof-generic-skolem-args.ts`. |
| Later inference | The traversal follows symbolic arguments, fields, call/construct signatures, constraints, raw candidate bindings and array commitments. Each live expression/statement and the final publication sites revisit retained roots. `tests/HiddenEscape.sk` changes a dependency after registration and checks rollback without replacing the obligation. |
| Checking environments | Callbacks and loops share their environment. Named functions/methods publish declared signatures, class fields have declared types, and top-level constants cannot publish objects. These paths do not publish an inferred hidden object signature from a discarded body environment. Detached conformance probes and diagnostic environments cannot authorize acceptance. |

## Retained binding contracts (2026-09-17)

The uncaptured assignment path previously replaced `LocalRef.type` without
checking `LocalRef.declaredType`. For `let value = 1; value = "s"`, it retained
`number` as the latter and installed `string` as the former; it did not compute
a common invariant. Captures constrained writes, so inserting a closure changed
whether the same replacement was accepted. This was an unchecked write, not
missing exporter support for an internally established union.

The repair makes runtime writes check the retained contract regardless of
capture. Concrete primitive and callable contracts reject incompatible
replacements; open inference variables collect writes in the same variable,
and the existing loop restriction remains. Flow observations and object-shape construction are still distinct
from runtime writes: only `TCEnv.writeVar` marks a runtime assignment. The AVL
example now states `node | null` for a temporary read before replacement;
its equality read had already resolved its otherwise null-only inference bound.
Inference stability and object aliasing require the separate lifetime and
mutation rules above.

`inferred-binding-contract.ts` records the two previously accepted replacements,
compatible callable replacement, and explicit-union assignment with a precise
string result. `evolvedInferredSnapshotStillString` is now an expected rejection
at the string assignment. That is a checker repair, not an increase in the count
of verified repair functions. The verifier's fixed-world invariant is unchanged.

## Regression responsibilities

Tests are retained by the invariant they distinguish, rather than by the date of
the repair. These families are complementary; similar syntax does not make two
different ownership or variance cases duplicates.

| Family | Distinct obligation |
| --- | --- |
| `TypeReadObservation.sk` | Owner commitment, negative/blocked results, clone and rollback transfer, detached purposes, recursive-premise publication, frozen-mode exit and mutation stamps. |
| `TypeConstruction.sk` | Parameter substitution, field read/write variance, callback input/result variance, generic bounds and literal selectors retain their dependencies. |
| `HiddenEscape.sk`, `hidden-dependent-bounds.ts`, `contextual-hidden-escape.ts`, `instanceof-generic-skolem-args.ts` | Distinct witness identity, dependent bounds, callback publication, persistent versus per-iteration roots, later candidate growth. |
| `observed-*.ts`, `normalization-owner.ts`, `alias-inference-stability.ts` | Actual source consumers of observed layouts and normalization, with symbolic-member and later-growth controls. |
| `literal-representation-lifetime.ts`, `type-query-memo-stability.ts` | Source-level stale representations and query reuse, including conditional and awaited projections. |
| `inferred-binding-contract.ts`, alias/refinement/closure/loop tests | Fixed storage contracts versus point-specific contents, stable aliases, snapshots and repeated execution. |
| `iterator-effects.ts`, `implicit-instanceof-effects.ts`, `membership-protocol-erasure.ts` | Implicit execution boundaries, condition/receiver summaries, and preserving an implicit call contract across structural conversion. |
| Independent verifier suites and curated examples | Regression qualification of the existing pipeline, not certification of all checker internals or these new repairs. |

Native protocol counterexamples test actual checker operations, but are not
necessarily executable TypeScript exploits. Source counterexamples are stronger
evidence of an acceptance bug. Neither kind is a proof of global soundness.
Concrete instantiations of a generic do not certify its universal body.

## Final qualification (20 September 2026)

The three bounded repair delivery milestones are complete: validation lifetime,
checked-data mutation/effect boundaries, and consolidation with broader
qualification. This checkpoint does not complete architectural milestones A1–A4.
The final checker repair is `f29516c2`; its baseline tests are `3231d580`.

- All **211 checker tests** pass, including the multi-file project and incremental
  suites; **65 independent verifier suites** pass.
- The **64-file curated corpus** remains at **278 proofs**, nine unsuccessful
  searches and 18 unavailable checks, with zero outcome mismatches or runner
  errors. This checks pipeline regressions, not global checker soundness.
- The repair census selects **390 functions**: **240 rejected** by SKJS and
  **150 accepted**, comprising **40 verified**, **87 gated** and **23 unproved or
  unavailable**. The four new membership functions add two producer rejections
  and two gates; they do not increase independent proof coverage.
- A paired scan checks all **418** TypeScript files under `tests/expect-error`
  and `examples/src` against the saved milestone-1 and final binaries. All **836
  processes** finish under a 20-second per-file timeout and a 4-GB container
  limit. Exact diagnostics differ only in `implicit-instanceof-effects.ts` and
  `membership-protocol-erasure.ts`, matching the intended repairs. The scanner
  first checks a clean control, an expected rejection, forced timeout and error
  classification; a crash cannot silently become a clean result.
- Strict tsc accepts both erasure counterexamples. Running their erased
  JavaScript with an incompatible operand produces `TypeError`; the explicit
  compatible protocol succeeds. This is direct source evidence, separate from
  the native ownership tests and independent proof counts.

The broad scan is one pass and initially overlaps suite execution. Its two
apparent timing regressions disappear in three isolated paired rounds, with
binary order reversed in the middle round. Exact diagnostics remain identical
on all five repeated fixtures. Median seconds, milestone 1 / final:

| Fixture | Before | Final |
| --- | --- | --- |
| `array_literal_examples.ts` | 0.726 | 0.723 |
| `instanceof-generic-skolem-args.ts` | 1.064 | 1.073 |
| `eagercollection-deep-value-no-oom.ts` | 5.229 | 5.222 |
| `builtins_documentation.ts` (scan outlier) | 0.402 | 0.404 |
| `person.ts` (scan outlier) | 0.229 | 0.232 |

These are bounded regression measurements, not a complexity guarantee.
No regression tests or native tests were removed to meet the
criteria. Chronological handoff notes were consolidated into the architecture,
consumer inventory and extension rules above.

## Closure and future work

The finite closure criteria are: each audited acceptance consumer has a lifetime
argument; the three variable roles preserve their distinct identities; explicit
and supported implicit effects invalidate transient facts; distinct regressions
and legitimate controls pass; and broader qualification reports actual outcomes
and cost. A new counterexample reopens its boundary even if every suite is green.

The active next objective is [Architectural end state](#architectural-end-state),
A1–A4. It strengthens implementation clarity and enforcement without requiring
new language features. Beyond that refactoring, separate work remains:

- A soundness proof of the full subtype/normalization algorithm, recursive types,
  and the whole source checker. The current source audit is not such a proof.
- Symbolic abstract indexed/key/template projections. Approximating a universal
  parameter by its upper bound is not an implementation of these operations;
  removing the current guards must preserve dependence through caller instantiation.
- Broader generic forms, forward/recursive bounds, higher-rank polymorphism and
  first-class existential packaging. Capture contracts can conservatively lose
  safe hidden-type precision; universal, inferred and existential roles must
  remain distinct when support grows.
- Accessor/proxy interoperability and precise custom iteration protocols, beyond
  the checked data-object/effect interpretation above. Ordinary call invalidation
  is conservative and can also reject safe pure-helper programs.
- Independent repair-corpus coverage. See [Repair coverage](../verification/REPAIR-COVERAGE.md)
  for measurements, inspected fragment blockers and the safe extension workflow.
  This is a separate deliverable from repairing checker acceptance.

Do not rewrite SKJS into the independent calculus, weaken a location contract,
follow an unsound tsc acceptance, or change checker behavior incidentally while
extending extraction. An exported closed operation records only selected paths
and does not establish the lifetime of earlier acceptance. Before relying on
operation exports, measure attempted, recorded and omitted paths. Generic source
extraction also covers only specific supported shapes, not arbitrary bodies.

The removed chronological implementation notes remain in Git history through
`73572889`; current status belongs here, source-language restrictions in
[skjs-rules.md](../skjs-rules.md), case status in [ledger.yaml](ledger.yaml), and
verification architecture in [DESIGN.md](../verification/DESIGN.md).
