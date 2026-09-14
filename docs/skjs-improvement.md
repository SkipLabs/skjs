# SKJS implementation improvement

Progress on making the checker more principled, using the independent semantic
contracts as a reference. This is **SKJS `src/` work**. It is not the
verification pipeline, and it is not a plan to make SKJS implement the Lean
fragment.

Status of each row is stated only here. Corpus row status stays in
[ledger.yaml](ledger.yaml). Verification architecture stays in
[verification/DESIGN.md](../verification/DESIGN.md).

Update a row when a SKJS commit lands that addresses it: set the status, name
the tests, and keep the “done when” criterion true. `make test-in-docker` must
stay green.

## Spec

Three similar-looking kinds stay distinct:

| Kind | Obligation |
| --- | --- |
| Generic parameter `T` | The body works for **every** admissible `T`. |
| Inference variable `?T` | The checker may **choose** a type that meets the constraints. |
| Hidden type argument of an object | There **exists a fixed type**; the checker cannot choose or identify hidden args of different runtime objects. |

`T extends boolean` is `T ≤ boolean`. It is not `boolean ≤ T` or `true ≤ T`.

SKJS already separates `TParam` from inference `TVar`. The remaining question
is whether *uses* preserve rigidity, scope, and witness identity, especially
when closures or loops let values escape.

Contracts (full text in [DESIGN](../verification/DESIGN.md#contracts)):

1. Substitution preserves meaning.
2. Expansion and normalization have explicit exact / approx / cache guarantees.
3. Successful subtyping is semantic inclusion under every assignment satisfying `Δ`.
4. Inference cannot invalidate previous checks.

Repair architecture: inference **proposes**; validation is against an
**immutable, explicit** representation. Heuristic inference may stay. Its
success does not authorize acceptance. Caches and clones then have local
obligations instead of becoming part of the meaning of subtyping.

The [mathematical audit](skjs-type-soundness.tex) already separates guidance
from validation and treats stale-state reads and caches as stability failures.
That is a starting specification, not a proof of the current checker.

A soundness argument against these contracts, with regression tests, can
justify a SKJS fix. An independently checked derivation is a **strong** route
to an incompleteness fix, not the only permitted one. A verification-pipeline
`reject:` is not a disproof, and a failed proof search is not incompleteness.

## Active work

Statuses: `not started` · `in progress` · `done`.

R1 (hidden identity and escape), R3a (declaration identity), R3b (freeze-window),
M2 (stale captured reads), and M3 (loop-carried narrowing) meet their stated
bounded completion criteria.
The next architectural milestone is durable validation under substitution
changes (R2), including justified use of speculative clone results (R3c).
R1 records and revalidates signature and persistent-binding escape roots.
General substitution stability remains R2; general alias mutation remains M1.

| ID | Work | Status | Done when |
| --- | --- | --- | --- |
| R1 | Uses of `TParam`, inference `TVar`, and hidden witnesses preserve rigidity, scope, and identity | done | Specific forbidden transitions and escapes fail (a parameter is not solved as `?T`; a hidden witness does not become another object's; a captured/loop-escaped witness keeps its identity). Legitimate repeated uses of the *same* hidden witness still check. Not a wholesale TVar rewrite. |
| R2 | Propose vs validate, **and** later uses respect the snapshot | in progress | A subtype/expansion result is valid against an explicit snapshot **and** subsequent uses of that result respect the same snapshot, or the judgment is revalidated when a recorded dependency changes. Exporting a closed record under the subst at validation time does **not** count: that stabilizes the *exported* record, not SKJS's earlier acceptance. |
| R3a | Expansion keys identify the resolved declaration, not spelling | done | [expansion-key-collision](deep-dives/issues/expansion-key-collision.md): same-named aliases from different modules no longer share a cache entry; the unsound call is rejected; renaming the local alias still rejects; valid uses of each definition still check |
| R3b | Substitution-dependent answers track what can invalidate them | done | [freeze-window](deep-dives/issues/freeze-window-stale-memo-caches.md): a memo written while a candidate is unsealed is not reused after that candidate grows; the order-dependent acceptance is gone; the program without the priming call still rejects |
| R3c | Speculative clone results authorize the parent only with a justified transfer | in progress | A clone that does not commit cannot make the parent accept; any transfer of a clone result is justified by an explicit obligation |
| M1 | Alias writes: a narrow alias must not promise contents another alias may legally overwrite (`L-MUT-ALIAS`) | in progress | Reduced [narrowed-alias-stale-write](deep-dives/issues/narrowed-alias-stale-write.md) programs are rejected; a positive counterpart with a shared invariant still checks |
| M2 | Stale captured reads: a creation-time narrowing is not a captured arrow guarantee (`L-STALE-READ`) | done | Reduced [stale-closure-reads](deep-dives/issues/stale-closure-reads-narrowing.md) programs are rejected; a snapshot-or-null-check counterpart still checks |
| M3 | Loop-carried narrowing (`L-LOOP-CARRIED`) | done | SKJS rejects the [loop-carried](deep-dives/issues/loop-carried-narrowing-stale.md) reduction using its existing language and tests. Independent pipeline coverage of `let` is **not** a prerequisite. A counterpart that remains correct under SKJS's own loop checking (not source-level supplied invariants) still checks |

## Convergence audit (2026-09-14)

The remaining work is architectural. Recent assignment, initialization, and
iterator repairs are useful, but more syntax-level completeness examples do not
by themselves close R2, R3c, or general M1. R1's bounded closure is recorded
below. Treat those examples as a separate backlog unless they expose an
acceptance bug or block one of the contracts below.

The broad read-only audit inspected substitution mutation/cache boundaries,
clone/raw-read consumers, hidden-type escape boundaries, and call/refinement
handling. A batched source probe confirmed:

- A direct call that writes null still leaves a numeric field refinement usable;
  its erased JavaScript returns null. An unknown callback has the same gap.
  A post-call null check also gets a stale "always false" warning.
- Scalar snapshots and explicit rechecks remain accepted. Direct alias writes,
  returning a concrete number as arbitrary `T extends number`, and exchanging
  values between two independently discovered hidden types reject.
- The call-effect family already has #597/#599 witnesses in
  `tests/expect-error/unsound-refinement.ts`; do not duplicate them just to grow
  coverage. M2/M3's completed bounded criteria do not cover arbitrary callee
  effects. M1's original direct-alias examples are repaired, but its broader
  mutation objective is still open.

The effect-boundary repair now invalidates contracted object contents after
explicit calls, construction and suspension. Captured mutable bindings widen to
their lasting contracts when the capture/write summary permits reassignment.
Condition replay tracks when field and captured-binding reads were observed, so
a later call cannot resurrect an earlier guard. Scalar snapshots, private scalar
locals and fresh post-call guards retain their precision. The #597/#599 witnesses
now reject. The checker display intrinsics do not execute user callbacks and are
exempt; ordinary calls have no inferred purity exemption.

This is conservative: pure formatting and recursive ADT helpers can lose their
discriminant refinement, recorded in the ADT tests. Remaining M1 boundaries are
implicit execution (accessors, iterator hooks and similar operations), growing or
uncontracted inferred objects, and general alias/substitution lifetime. These are
explicit residual risks, not covered by the explicit-call criterion.

These probes are evidence for the listed outcomes, not an exhaustive audit or
a proof of generic soundness. R1's late-growth gap remains a structural concern;
this pass did not produce a new accepted hidden-escape witness.

Use three broad sweeps to converge:

| Sweep | Scope and completion evidence |
| --- | --- |
| **1. Effect boundaries (M1)** | Audit direct, method, constructor and callback calls, captured-local writes, and suspension together. Establish one conservative invalidation policy, with explicit exceptions only for justified effects. Existing stale-read witnesses must reject; scalar snapshots, rechecks, and shared invariant contracts must remain usable. Record any unsupported effect classes. |
| **2. Validation lifetime (R2/R3c)** | Inventory every acceptance-relevant clone, save/restore, raw candidate read, cache shortcut and successful subtype consumer. Each needs a documented reason it remains valid in the parent and after growth: committed constraints, sealed dependencies, or explicit revalidation. Cover calls, source type references, defaults/definite assignment, narrowing and variadic inference as one pass. Diagnostics, printing and literal guidance are distinct roles, not candidates for indiscriminate live checking. A call-local fixed point and exported evidence alone do not finish this sweep. |
| **3. Escape lifetime (R1) and closure audit** | Reuse the validation-lifetime mechanism to guard hidden identities reachable through later inference growth, not just the types visible at closure/loop exit. Audit every candidate-growth path and persistent container boundary. Preserve same-witness use and opaque packaging; reject cross-witness identification and invocation/iteration escape. Finish with the combined regression/verification run and an explicit residual-risk list. |

The finite validation audit surface includes `TEnv`'s argument-check roles;
`TypeCheckExpr`'s default and initialization decisions; `TypeCheckRefine` and
`TypeCheckScope`'s installed filtering/projections; `TTypeSubtyping`'s speculative
admissibility and rollback; `TVariadicTyping`'s raw tuple fallback; and the
substitution caches. `TArrayLitTyping`'s literal guidance and diagnostic/printing
clones should be classified separately. Listing a site here does not assert that
it contains a bug.

For each sweep, collect independent witnesses in one batch, repair the shared
boundary, then run focused probes and the full suites once the batch stabilizes.
Commit coherent fixes separately without turning every fixture into a user
iteration. Do not add extracted Lean programs absent a credible verifier issue.
The existing semantic contracts remain the reference; passing concrete generic
instantiations does not prove a generic body.

## Validation-lifetime inventory (2026-09-14)

This pass traces the clone, save/restore and raw-binding consumers in the checker,
including the surrounding successful-check and cache paths. It is a source audit,
not a soundness proof. “Local justification” below identifies why that operation
can transfer its result; it does not establish stability of every reachable
inference dependency. No R2/R3c completion status changes follow from this table.

| Consumer | Local justification / remaining obligation |
| --- | --- |
| `TEnv.instantiateTParams`, `TypeChecker.call`: written arguments | `ValidateTypeArguments` checks the live substitution. Explicit source aliases/classes validate before expansion; explicit construction validates before constructor forwarding. Phantom bodies cannot erase the check. Existing `alias-inference-stability.ts` covers later incompatible growth. |
| Alias expansion, class setup and declaration normalization | `ProbeTypeArguments` discards speculation. The independent obligation is the checked rigid declaration plus constraints carried by fresh inferred arguments. This depends on every entry path maintaining that invariant; it is not evidence produced by the successful probe itself. |
| `TypeChecker.call`: inferred positional/rest arguments | The complete argument pass repeats until the substitution version stops changing. This checks consistency within that call. It supplies no revalidation when a dependency changes after the call returns. |
| `TType`, `STypes`, `Clauses`, `TFun`, `TObject` subtyping | Successful alternatives retain their substitution changes. Failed alternatives restore state; an entirely failed check restores its entry state. These are transactional acceptance paths, not successful checks on discarded clones. Stability of previously successful checks still depends on sealing and symbolic types. |
| `growTVars.isCovered` | Its subtype probes always restore, but only choose which lower bounds to propose. The outer `TType.isSub_` subsequently expands and validates the complete relation in the live substitution. A probe success is not the final acceptance result. |
| `growTVars`: constraint admissibility | `freezeCandidates` suppresses growth/sealing of already determined candidates while permitting fresh determinations. Success commits fresh determinations before growth; failure restores. The outer subtype check validates afterward. Frozen-query results are not published to subtype/intersection caches. |
| `TType.mapTParams`: redundant-constraint shortcut | Success skips an intersection only when the substitution version is unchanged. Otherwise it restores and computes the intersection. The shortcut establishes non-mutation now; its dependence on earlier cached answers belongs to the cache obligation below. |
| `VariadicTyping.resolveSpreadToTuple` | Success consumes a tuple shape from contravariant expansion, with a raw-binding fallback when constraint intersection hides the tuple. Failure restores. The stored-callback witness below showed that element checks did not protect the outer shape. Tuple resolution now establishes that shape through a covariant read before flattening; unsuccessful resolution restores the read. General transitive dependency tracking remains open. |
| `VariadicTyping.inferRestTypeVar`, array literal commitment | Successful constraint/element checks commit; failure restores in the transactional paths. Literal-precision probing chooses guidance, followed by live element checking. Error-recovery state is outside this soundness objective. |
| `bindType`: uninitialized annotations | The annotation expands covariantly in the live substitution before the clone tests whether it admits `undefined`. The clone cannot alone choose an uninitialized variable's accepted type. Existing definite-assignment stability coverage exercises this boundary. |
| Tuple/object defaults | Clone queries decide whether the default contributes and produce warnings. The selected value passes through live source expansion/default-result typing and subsequent binding. The negative reachability decision still relies on those reads establishing the relevant candidate. Probes below exercise both tuple and field paths. |
| Equality/truthiness refinements | Local equality establishes both operands live; contracted field refinement establishes the field live before clone intersection/subtraction. **Open:** nested symbolic dependencies and uncontracted inferred fields need a transitive stability argument. The new effect epoch addresses runtime effects, not substitution growth. |
| `evalInstanceof` preservation probe | A successful branch probe retains the original branch; it does not import the clone's solved type arguments. A failed probe intersects with fresh rigid witnesses live. Preserving a branch therefore does not itself identify two hidden witnesses. Their later escape remains R1. |
| `Scope.mayMatchAlternative` | Alternative elimination now requires both the current-type expansion and the disjointness probe to leave their clone versions unchanged. Otherwise the alternative is retained. This prevents clone-only solving/sealing from authorizing elimination. It still relies on the ordinary cache and symbolic-dependency invariants for non-mutating results. |
| Diagnostic overlap, `showTypes`, `originSuggestions` | Clone/raw results supply warnings, display assertions or advice, not a program typing premise. Keep these separate from mandatory validation; making them live would change inference merely by requesting diagnostics. |
| `EscapingTypeParams` | `peekRaw` traverses current bindings without installing its rebuilt type. This detects identities reachable now. Retained escape obligations now revisit the symbolic roots after later live checks. The completed bounded R1 audit below covers root publication and checking-environment boundaries; general subtype/cache stability remains R2. |

The cache/storage part of the inventory is separate from those consumers:

- `SubstState.restore` restores candidate values, origins and all four caches
  together. A failed branch does not leave its successful subtype memo in the
  restored state. The recursion guards in `TEnv` are value-scoped to the active
  call chain, distinct from substitution-owned success caches.
- Union and named expansion caches retain symbolic arguments. Their obligation
  is that no cached construction materializes a changing argument's current
  value. The existing resolved-declaration identity checks remain necessary.
- Subtype and compound-intersection caches rely on covariant reads sealing the
  candidates whose current values they inspect. Suppressing publication during
  candidate freezing closes that specific exception. **R2 remains open:** neither
  cache records transitive dependencies or schedules later revalidation.
- `SVClosed` closes one candidate binding; its payload can still contain symbolic
  types. Treating “closed” as an immutable, fully resolved graph would skip the
  very dependency argument this audit requires.

Focused source probes tested a rest factory with a numeric seed, assignment of
its result to a numeric function alias, and a subsequent incompatible argument;
SKJS rejects the incompatible call and accepts a compatible numeric call. The
seed was a `number` parameter so literal inference did not reject the alias
before the intended check. Tuple and object defaults from an inferred undefined
field reject later numeric writes. An `instanceof`-preserved generic instance
rejects a string write after establishing a numeric alias. Strict tsc reports the
same four negative sites. These probes found no new acceptance bug and overlap
existing regression families, so they were not added as repetitive permanent
tests. They do not discharge the structural open obligations above.

## Normalization-transfer audit (2026-09-14)

The next R2/R3c target is transfer of normalization results between substitutions,
not another syntax family. Changing cache keys would not by itself repair a
result already materialized from the wrong state.

| Path | What the source audit establishes |
| --- | --- |
| `seenUnion` | `TType.union` combines symbolic instances and clauses; `TObject.union` retains branches. The shape-inspecting `TField.union` and `TFun.union` helpers belong to subsequent branch projection, not this cache's construction path. No freeze-window cache fix follows merely from those helpers having the same operation name. |
| `seenSub` / `seenInter` | Frozen candidate queries do not publish entries. Ordinary reads seal directly inspected candidates; untouched nested types can remain symbolic. This is a local justification, not a transitive proof for every subtype shortcut and materialized projection. |
| `seenExpansion` | Both `TType.expandToVectors` and `collectTVars` cache `instantiate` results by resolved declaration and symbolic arguments. Cache-key identity does not establish that the result remains symbolic. The previous source comment claimed only `keyof` could inspect arguments; that inventory was incomplete. |
| `instantiate` | Creates a separate `Subst` initialized from the caller's state. Its values/caches can diverge, and `Subst.mcreate` does not copy `freezeCandidates`. A seal in that substitution is not a seal in the caller. Returning symbolic arguments is sufficient only for branches that actually preserve them. |
| `keyof`, numeric indexed access and `Closed<T>` | Their normalizers create fresh substitution state and inspect expanded operands. Bounds/shape restrictions can make an outcome conservative or reject it, but the successful cases need an explicit transfer argument. Neither the fresh state nor an unchanged parent version supplies that argument. |
| Template holes and mapped keys | Use `expandToVectors(..., None())`, preserving unresolved TVars and refusing/deferring abstract shapes under their existing rules. Their named expansions and any concrete shape they materialize still belong in the normalization contract. Index-key classification also performs a covariant read in fresh state. |

Batched source probes rejected a string write through a nested inferred array
following a readonly numeric view, while accepting its compatible-write control.
Concrete and inferred `T[number]` value annotations also passed; a delayed
callback-result form rejected conservatively. Strict tsc agrees with the nested
write rejection. These outcomes do not demonstrate a new runtime counterexample,
and overlap existing lifetime and indexed-access families, so no repetitive
regressions were added. No behavior or R2/R3c completion status changed.

The next experiment should isolate a shape-inspecting normalization with a
reachable candidate, compare its returned result with recomputation after legal
candidate growth, and identify which state justifies that result. Only then
choose between retaining a symbolic operation, validating in the owning state,
or recording a dependency. Preserve declaration-only normalization and inference
probes as separate roles; globally sealing their inputs would change inference.

## Bounded R1 closure audit (2026-09-14)

R1 meets its stated use-level criterion. This is a source audit backed by the
existing escape regressions and the dependent-bound repair, not a proof of all
subtyping or all generic programs.

| Boundary | Established rule and evidence |
| --- | --- |
| Hidden identity creation | `evalInstanceof` is the sole consumer of hidden argument creation. `genSkolemTParam` never rewinds on rollback and refuses creation in a speculative clone. Different discoveries therefore do not reuse an identity within a substitution. |
| Parameter bounds | Declaration parameters stay rigid; inferred arguments remain candidates; hidden arguments are rigid identities. Later bounds refer to the corresponding earlier arguments. `hidden-dependent-bounds.ts` exercises same-witness inclusion, forbidden reversal, cross-witness writes and constructor inference. |
| Callback publication | The complete signature and enclosing bindings are retained as escape roots. This includes contextual parameters supplied by a temporary generic receiver and explicit `typeof` results. `contextual-hidden-escape.ts` and the closure cases in `instanceof-generic-skolem-args.ts` distinguish escaping identities from opaque results and invocation-local inference. |
| Repeated execution | While/for checks include conditions and increments; for initializers persist, while for-in/of iteration bindings are fresh. Persistent binding roots reject pooling; per-iteration containers remain accepted in `instanceof-generic-skolem-args.ts`. |
| Later inference | The traversal follows symbolic arguments, fields, call/construct signatures, constraints, raw candidate bindings and array commitments. Each live expression/statement and the final publication sites revisit retained roots. `tests/HiddenEscape.sk` changes a dependency after registration and checks rollback without replacing the obligation. |
| Checking environments | Callbacks and loops share their environment. Named functions/methods publish declared signatures, class fields have declared types, and top-level constants cannot publish objects. These paths do not publish an inferred hidden object signature from a discarded body environment. The detailed environment inventory below separates conformance and diagnostic-only environments. |

The combined run after these repairs passed all 148 checker tests and 41 verifier
suites, with zero corpus mismatches. Extra probes confirmed that a captured object
cannot acquire a new hidden-typed field after use, and that an outer alias named
`T` cannot supply a dependent class argument's bound. These overlap the existing
boundary families and were not added as repetitive permanent tests.

Residual limits remain explicit: forward/recursive bounds and first-class
existential packaging are not established here. Capture contracts can erase safe
hidden-type precision; supporting every such program is not R1's criterion.
General transitive cache/subtyping stability is still R2/R3c, and implicit runtime
effects and growing-object aliasing remain M1. The escape traversal does not make
an independently unsound subtype judgment sound.

## Implementation record

R2/R3c abstract-projection repair: the normalization-transfer experiment exposed
an acceptance bug before any later candidate growth was needed. For
`type ElementOf<T extends readonly unknown[]> = T[number]`, a generic function
returning `ElementOf<T>` could return `"wrong"`: the body normalized the abstract
array's upper bound to `unknown`. An explicit `number[]` instantiation later
normalized the same alias to `number`. The accepted erased program returned a
string at that numeric result. `type Keys<T> = keyof T` had the same mismatch:
a fabricated key became a different literal type after concrete instantiation.

`keyOfType` and `numberIndexedType` now share a guard against projecting an
abstract parameter outside type-alias validation. Alias declarations may defer
until concrete instantiation; known object/array shapes with symbolic members
remain supported. `abstract-type-projection.ts` covers both witnesses, the
explicit-instantiation consumers, and concrete/symbolic-element controls. A real
read through an abstract whole-array parameter is also conservatively rejected;
use an explicit element parameter (`readonly E[]`) instead. Full support needs a
symbolic projection type, not approximation by the upper bound.

Strict tsc accepts the indexed-access counterexample but rejects the fabricated
`keyof` return. The other shape normalizers already reject/defer abstract inputs
under their existing policies. This fixes the demonstrated representation
mismatch without changing caches or claiming the remaining candidate-growth
transfer obligations are complete.

R1 dependent-bound repair: class declaration checking, inferred constructor
arguments and hidden `instanceof` arguments now resolve each later bound with
the preceding parameters already bound. In `C<T, U extends T>`, the bound of
`U` therefore refers to this declaration's rigid `T`, this constructor's
inference candidate, or this object's hidden identity, respectively. Class
checking reuses `addTParams` instead of independently rebuilding its arguments
before establishing their scope.

`hidden-dependent-bounds.ts` covers the accepted same-object direction and
constructor inference, with rejected reverse, cross-object and incompatible
constructor cases. Previously every case stopped at an unresolved `T`. A probe
with an outer `type T = number` also confirms that this unrelated name cannot
justify a numeric result from an unknown object's hidden field. This repairs
incompleteness and binder identity; it is not a newly demonstrated runtime
unsoundness. Forward and recursive bounds are not established by this change.

R1 contextual-signature repair: a non-generic method can still contain inference
candidates from its generic receiver. For a temporary `new ContextRunner(null)`,
those candidates are not enclosing bindings. A contextual default
`y = x instanceof ContextBox ? x : null` grew such a candidate to include the
fresh hidden identity; the explicit result annotation `typeof y` then published
it without the inferred-result check. The callback ran twice on independently
typed boxes, and the returned pair made their fields exchangeable.
`contextual-hidden-escape.ts` demonstrates a string returned at a declared numeric
result; strict tsc rejects the default. An explicit `unknown` receiver argument
and opaque callback result form the accepted counterpart.

Every anonymous function now registers its complete published signature as a
retained escape root when it minted local hidden identities. This covers required,
optional and rest parameters, result types and generic constraints through the
existing type traversal. This subsumes the earlier inferred-result-only check,
which is removed to avoid duplicate obligations and diagnostics; signature escape
uses SKJS2080. Both the initial signature and later candidate growth are checked,
independently of whether the receiver or
candidate appears in the enclosing scope. A hidden identity discovered outside
the callback is not forbidden by this callback's local identity set.


R1 root/publication audit: the traversal follows fields (read and write types),
call/construct signatures, receiver/parameter/result types, generic arguments,
intersections, candidate constraints and current candidate bindings. It missed
one representation edge: `TArrayLit` stores its committed array/tuple type in a
separate candidate. That binding is now traversed just like an ordinary `TVar`.
`tests/HiddenEscape.sk` exercises an initially empty literal, a commitment to an
array of another candidate, later introduction of a forbidden identity, and
rollback. The same retained obligation must observe each state. Source probes
returning direct and nested arrays were already rejected, so this is a direct
representation regression rather than a new accepted runtime counterexample.

The checking-environment inventory distinguishes these boundaries:

| Environment | Publication / final check |
| --- | --- |
| Named functions and methods | `funDefSetup` creates one environment for parameters and body. Anonymous functions and loops reuse it. Revalidation now also runs after fallthrough/result checks, before CFG or successful claim publication. |
| Constructors | The same setup checks the body, followed by a final initialized-fields subtype check. Revalidation now follows that check. The body-specific `this` view is checked against declared fields, not published as a new class signature. |
| Instance field initializers | A fresh environment checks the expression and then its declared field type. Revalidation now follows that final subtype check. |
| Top-level expressions/constants and computed enum members | Final void, annotation or numeric checks can run after expression checking; each expression-bearing environment now revalidates afterward. Constants are additionally restricted to primitive published types. |
| Class/interface conformance | The four remaining class environments perform declared-type compatibility checks only; they do not evaluate closure/loop bodies or register local escape obligations. |
| Top-level CFG reconstruction | Uses one separate environment over the full statement list; statement revalidation applies. Its diagnostics are discarded and only CFG output is retained. It does not authorize source acceptance. |
| `saveAll` / `mcreateFromSaved` | The saved substitution is used for diagnostic rendering in `TypingError`, not another acceptance environment. Obligations need not be transferred into a diagnostic clone. |

This closes the identified post-expression final-check gaps. The contextual
signature repair above adds the missing publication root for receiver-owned
parameter candidates. The combined closure audit above closes the bounded R1
criterion; no generic signature publication is justified merely by the absence
of a diagnostic-clone transfer.


R1 escape-lifetime hardening: successful closure-result and enclosing-binding
checks now retain their symbolic roots, forbidden hidden identities, and original
diagnostic location in the current `TCEnv`. After subsequent expression and
statement checks, the same obligations traverse the current substitution again.
A root that reaches a candidate which later reaches another candidate is followed
transitively by `EscapingTypeParams`; the retained roots are not frozen expansions.
The initial check and late check share one implementation and the existing error
codes. An invalid obligation is not retained for repeated recovery diagnostics.

This supplies live-state revalidation within a checking environment without
adding side effects to `Subst.grow` or rejecting a tentative subtype alternative
before its normal rollback. Existing closure/loop pooling regressions and opaque
or invocation-local controls cover the boundary behavior. No newly accepted
source-level late-growth counterexample was established in this pass; an attempted
parameter-default/`typeof` result escape was already blocked by required parameter
annotations. This is a structural strengthening, not a new runtime witness.

The retained checks cover growth reachable from the boundary's recorded roots.
They do not prove that every persistent root was enumerated, establish scope
transfer between separately created checking environments, or replace the wider
R2 dependency argument. R1 therefore remains in progress. The next audit should
follow root publication and checking-environment boundaries, rather than add more
variants of already rejected pooling.


R3c alternative-elimination hardening: `mayMatchAlternative` is an acceptance
consumer, unlike the overlap check used only for warnings. It used clone
expansion and intersection to discard declared object alternatives without
checking whether the clone had solved or sealed any inference candidate.
The transfer now requires an unchanged substitution version at both boundaries:
the expansion that supplies current branches and each intersection that proves
required fields disjoint. If either computation changes its clone, the alternative
is retained. The parent is not constrained merely to make a speculative branch
selection succeed. This uses the same non-mutation criterion as the existing
redundant-constraint shortcut in `TType.mapTParams`.

This is a structural strengthening, not a newly demonstrated source-level
unsoundness fix. Existing `assignedUnionAlternative` and
`checkedConditionalAlias` cases in `unsound-refinement.ts` guard concrete
alternative precision; the file's stale alias cases guard rejection. No redundant
source fixture was added without a distinct observed behavior. Unchanged clone
versions do not constitute a general dependency proof: success-cache validity
and later hidden-witness growth remain R2/R1 obligations.


R2/R3c rest-shape repair: `resolveSpreadToTuple` consumed a bound candidate with
a contravariant read, then flattened away the candidate's identity. Parameter
checks could establish the tuple's elements without establishing its length or
preventing replacement of the outer tuple. `rest-inference-stability.ts` stores
`(x: number) => number` beside an inferred one-element argument tuple in a
generic runner. SKJS accepted replacing that tuple by `[]` or `["changed"]`;
the runner then returned undefined or a string at its declared numeric result.
Strict tsc rejects both replacements. The compatible numeric replacement remains
the positive control. These are runtime counterexamples, not merely inconsistent
diagnostics across two checks.

Resolution now uses covariant expansion in both its ordinary and raw-binding
fallback paths. Consuming an exact shape establishes the outer candidate before
flattening it into parameters. Returning no tuple restores the entry substitution,
so an unsuccessful shape probe does not seal an unrelated array candidate.
Both call checking and function subtyping share this boundary. This is a local
sealing repair; it does not provide general immutable validation evidence or
finish R2/R3c. Clone-based alternative elimination and late hidden-witness growth
remain separate obligations.


R3a implementation note: the initial cache-key patch alone still accepted the
witness. Named-instance hashes and a subtype shortcut also identified types by
spelling. The repair covers those equality paths as well as expansion keys and
instantiation guards. Recursive subtype comparisons also use resolved identity,
so equivalent imported mentions do not lose their cycle guard. Regression coverage is in
[`tests/projects/expansion-key-collision`](../tests/projects/expansion-key-collision):
the rejected flow, reverse expansion order, a renamed declaration, and a renamed
re-export of the same declaration. `make test-in-docker`, `make verify`, and
strict tsc on the regression project pass. The declaration-identity repair is complete.

R1 initial scope repair: an inferred closure result cannot expose a hidden type
minted while checking that closure. The same syntactic `instanceof` runs on
different objects across calls; exporting its one checker identity would let
those objects exchange incompatible values. A read-only traversal inspects the
result's symbolic structure, constraints, and current inference bindings.
Concrete observations and explicit opaque results remain usable. Existing
`instanceof-generic-skolem-args.ts` witnesses cover direct and higher-order
result escapes. At the same boundary, the enclosing bindings' current and
declared types are inspected under the updated substitution. This catches
locally minted hidden identities inferred into captured containers, including
closures with explicit void results. Opaque outer containers and invocation-local
inference remain usable. The same enclosing-binding check runs at while, for,
and for-in/of boundaries, including hidden identities introduced by conditions
and increments. For-in/of excludes its fresh iteration binding; a for
initializer remains persistent across iterations. Existing loop-pooling
witnesses are rejected while per-iteration inferred containers remain valid.
The escape-lifetime hardening above now revalidates these symbolic roots after
later live checks. The combined closure audit above records the completed
bounded R1 criterion; this does not provide general existential packaging.

R2 initial stability repair: retire the `TSInst` subtype shortcut that equated
an open inference candidate with a concrete argument using `peekRaw`. That
instantaneous equality does not justify an enduring alias contract. The normal
subtype path applies the existing covariant sealing discipline, rejecting later
incompatible growth while allowing compatible writes. Coverage is in
`alias-inference-stability.ts`; the existing recursive-generic performance
regression remains the guard for structural expansion. This removes one
acceptance bypass; it does not introduce immutable validation snapshots or
complete R2. The primed freeze-window regression now rejects the incompatible
push itself: the first call has already established a number[] result. Without
priming, the later incompatible call still rejects.
The resolved-declaration identity protections from R3a remain in
normal expansion and recursive comparisons.

R3b implementation note: subtype and intersection results computed while
`freezeCandidates` is set are not inserted into the substitution caches.
Those queries can read open candidates without sealing them, so their results
have no stability guarantee after growth. Ordinary cache reuse is unchanged.
[`freeze-window-stale-cache.ts`](../tests/expect-error/freeze-window-stale-cache.ts)
checks rejection with and without priming, plus repeated valid queries when
later growth remains within the constraint. `make test-in-docker` and
`make verify` pass. The freeze-window repair is complete.

R2/R3c first repair: explicit generic-call constraints are mandatory checks on
the live substitution in `TypeChecker.call` (`src/TypeCheckExpr.sk`). `typeof`
of a local uses the ordinary expression checker, so an explicit argument can
contain open inferred field candidates. A discarded clone could validate and
seal those candidates only in the clone, leaving later writes free to invalidate
the earlier judgment. `explicitConstraintMustRemainValid` in
`alias-inference-stability.ts` isolates this: a no-value-argument, void-result
call accepts the numeric field bound; a string write used to succeed; repeating
the same constraint check then failed. The write now rejects, and
`compatibleWritePreservesExplicitConstraint` still accepts numeric writes.
This witnesses loss of validation stability, not a demonstrated runtime failure.

The check instantiates dependent constraints with the explicit type-argument
map and uses ordinary live subtyping to establish them. This reuses existing
candidate sealing rather than introducing a second constraint store. The shared
call routine distinguishes written arguments from arguments forwarded by class
setup; merely having a populated argument array does not make them explicit.
Class arguments are now validated at the new-expression source site, before any
constructor call. Inferred constructors keep compatibility probing on a clone so
arguments can determine their full shape. Existing `class-ctor-tparam-unsound.ts`
tests preserve fields beyond the constraint and explicit constructor arguments.
Inferred generic arguments retain their constraint-carrying growth path. Receiver and
positional/rest arguments still undergo their normal live checks. The explicit
constraint is no longer justified solely by successful discarded speculation.

R2/R3c source-instantiation repair: `validateExplicitTypeArgs` establishes
alias/class bounds in the active substitution. Type references normalized in a
lexical `TCEnv` validate before returning the named type, independently of body
expansion or cache reuse. Previously that reference-site check used an empty
substitution; a phantom alias could erase its type argument, and a cached body
could hide an invalidated bound even at a second reference. Explicit `new`
arguments use the same validator before constructor lookup, covering classes
with no constructor. Constructor calls then retain compatibility probing for
already-validated or synthesized arguments, preserving inference of extra fields.

`aliasConstraintMustRemainValid` and `classConstraintWithoutConstructor` in
`alias-inference-stability.ts` now reject the writes that invalidate their first
instantiation. The alias previously accepted both references; the class only
rejected the second instantiation. `compatibleAliasAndClassConstraints` keeps
numeric writes and repeated instantiations usable. These are validation-stability
regressions, not runtime counterexamples.

R3c remains in progress: expansion and declaration contexts still use clone
checks, whose justification for constrained unbound inference variables needs
to stay explicit. Diagnostic and literal-guidance probes do not establish the
same acceptance obligation and should not be changed indiscriminately. R2 also
remains open: these repairs establish selected source-level constraints through
existing sealing, not general immutable validation evidence or dependency-aware
revalidation.

Generic constraint routing uses the required `TypeArgumentCheck` sum type,
shared by function calls and alias/class parameter instantiation. There is no
default role: every caller selects live validation or a discarded probe.

| Caller | Role | Why |
| --- | --- | --- |
| Source function calls and callable construction signatures | `ValidateTypeArguments` | Written arguments establish their bounds in the active substitution. Fresh omitted arguments follow their separate constrained inference path. |
| Explicit alias/class source references and `new` arguments | `ValidateTypeArguments` | Bounds must hold independently of body expansion or constructor availability. |
| Class constructor forwarding | `ProbeTypeArguments` | Written class arguments were validated at `new`; synthesized arguments must remain open for constructor inference. |
| Alias expansion, class shape setup, and declaration normalization | `ProbeTypeArguments` | Compatibility does not itself establish a new source-level fact; declaration bounds and inference constraints supply the independent obligation. |

This replaces defaulted booleans with a compiler-checked choice and centralizes
substitution selection. It preserves behavior; the explicit-bound stability
regressions and constructor shape-inference tests exercise the two roles. It
does not prove the probe transfer conditions or complete R2/R3c.

Equality narrowing now establishes both operands' current inferred types in the
live substitution before intersection or singleton subtraction on a clone.
Previously the live read was special-cased to the spelling `null`: an inferred
nullable read narrowed against literal null but failed against a named null
value. An inferred singleton on the other side was also invisible to subtraction.
`local-vs-local-refinement.ts` covers both accepted cases and rejection when the
other operand is not a singleton; strict tsc confirms those outcomes.

Field equality establishes the other operand through the same live expansion
before detecting a singleton. `field-refinement.ts` covers an inferred field
used to narrow another field; existing nonsingleton and mutation regressions
retain their rejections. Field narrowing still uses the established-contract
policy for the receiver and keeps its branch filtering on a clone.

Object identity comparisons also use the other expression's stable alias
contract before intersection. Comparing `x.child === y` after narrowing
`y.value` used to import that temporary field fact into `x.child`; reading a
new alias from the member lost its provenance and survived a null write through
`y`. `identityMemberAlias` in `unsound-refinement.ts` now rejects the stale read.
Its positive counterpart checks the child itself and copies the scalar before
the write. Both local and field equality use this boundary; scalar singleton
narrowing retains its current value type. This closes a concrete M1 channel
without requiring general nested-field refinement or new member-lookup rules.

This separates the lasting observation from the branch-local filtering without
committing the intersection's speculative constraints. The change fixes an
incompleteness in scalar comparison narrowing, not a newly demonstrated runtime
failure or general proof that all narrowing probes transfer correctly.

The call-validation fixed point now includes receiver, required/optional
arguments, and rest arguments in the same pass. A successful call exits only
after a complete pass leaves `subst.version` unchanged. Previously receiver
checking preceded the positional fixed point and rest checking followed it.
Argument expressions and initial rest-shape inference still run once before
validation; repeating subtype obligations does not re-evaluate expressions.
The exploratory callback/rest and dependent-constraint probes already rejected
before this change, so this is a structural strengthening of the validation
boundary, not a newly demonstrated unsound acceptance. Existing generic-rest,
receiver, constructor, and call tests guard behavior and termination.

This is a local fixed-point condition, not the full R2 guarantee: cache validity
and later substitution changes still require their own justification. The
checker does not yet retain immutable evidence or track all dependencies of a
successful call after it returns.

R2/R3c initialization repair: an annotation's admission of `undefined` is a
mandatory fact when it exempts a binding from definite assignment. A written
`typeof box.value` annotation can contain an open field candidate. Previously,
`bindType` checked `undefined` against that candidate in a clone, which could
grow it to include `undefined`; the parent retained the numeric type and
accepted returning an uninitialized local as `number`. This is a runtime
counterexample, unlike the earlier phantom-constraint stability witnesses.

`bindType` now expands the annotation covariantly in the live substitution
before the membership probe. This establishes the candidate type on which the
exemption depends; the clone cannot choose a different type just to admit the
initial value. `definite-assignment-tvar-soundness.ts` covers the rejected read,
assignment before reading, and a field type that already includes `undefined`.
The existing rigid-generic cases still reject. An uninferred generic result
establishes `unknown`, which admits the initial value but now correctly fails
the existing test's `void` return contract. This is not a ban on all
uninitialized declarations or a change to error recovery.

Local destructuring defaults have a separate control-flow obligation: their
effects occur only when the source value is `undefined`. Declaration defaults
previously ran in the enclosing scope, so a skipped assignment could justify a
numeric return or establish definite assignment. Assignment defaults used the
same unconditional evaluation through another entry point. Both now check the
default in a child scope and merge it with an untouched path. This preserves
both the pre-default value and any invalidating write the default can perform;
discarding the child scope alone would be unsound for local bindings.
`destructuring.ts` covers these distinct obligations and a fresh check after
the merge. Parameter defaults retain their existing isolated contract scope.
The local merge conservatively includes both paths even when the source type
could establish that the default always or never runs.

Object binding patterns preserve source order, including in the parser. Each
field's default and binding is checked once across the source's type branches.
After a default (including one in a nested pattern), later object fields and
rest copies use the source's stable contents contract. The actual read must
establish an object reference first; projecting its contents contract then
discards primitive alternatives, preserving a checked non-null child through
nested defaults. Unchecked nullable children still reject. Earlier scalar reads
remain snapshots. `destructuring.ts` distinguishes a default overwriting a later
field from the safe reversed order. This conservatively forgets field refinements
after any default; it does not analyze whether that particular default mutates
the source. General hidden call effects and evolving source contracts remain open.

Object patterns also carry each source field's stable contract through nested
patterns. Binding an object value uses that contract; extracting a scalar keeps
the observed value. `identityPatternAlias` in `destructuring.ts` rejects a saved
child narrowed by reference equality whose contents are subsequently overwritten;
`identityPatternScalar` preserves the scalar copied by a nested pattern before
the write. This closes the object-pattern binding boundary.

Property reads now record a separate stable result contract from the receiver's
contract, before that result can be stored or passed elsewhere. Dot and indexed
reads share the projection, including literal string/number/symbol keys and
general index keys. Resolution uses the existing field/index lookup operations;
an absent contract supplies no object-content guarantee and produces no second
access diagnostic. The current expression type and its primitive alternatives
remain available, so immediate scalar reads and non-null reference checks keep
their precision. `unsound-refinement.ts` covers an inferred property alias,
an annotated indexed alias, and a scalar snapshot. This is contract propagation,
not general nested-field refinement or callee-effect tracking.

Spread and object rest share a property-copy step that projects object-valued
fields through the source's stable contract, using the same lookup as direct
property reads. Named fields, symbol fields, and index slots retain their
existing copy-presence and callability treatment. Scalar values stay snapshots;
copying the carrier does not copy the contents of objects its fields reference.
`unsound-refinement.ts` covers spread/rest child aliases invalidated by a later
write and scalar copies that survive it. General mutation through uncontracted
or growing source objects remains open.

The projection is one type operation, `TType.withStableContents`: combine the
current type's primitive alternatives with the contract's object alternatives.
Alias creation may preserve selected contract alternatives; invalidation can
restore all of them. Local bindings decide whether their refinement provenance
requires projection, while property reads, copies, object patterns, and composed
receivers call the operation directly. They no longer manufacture local-binding
records with initialization and mutability flags to request a type projection.
This consolidates the existing algorithm without changing acceptance or making
its symbolic contracts immutable substitution snapshots.

Computed property reads capture the receiver before evaluating the key, then
drop transient contents if the key's existing `CaptureWrites` summary includes
a property write or unknown target. The same operation runs before computed
method lookup. Rebinding a local alone preserves the captured receiver rather
than looking up that name again. `computedRead` and `computedCall` in
`unsound-refinement.ts` reject reads/calls after the key clears their field;
`capturedReceiver` retains the original object's checked value after rebinding.
The summary is conservative about nested syntax and unrelated property writes;
hidden callee effects and uncontracted source contents remain separate limits.

The optimized local-object assignment path evaluates a computed key before its
right-hand side, matching ordinary assignment evaluation. Previously the reverse
order accepted a numeric field write whose key first cleared the RHS variable,
and rejected a safe write whose key initialized it. `keyClearsRhs` and
`keyInitializesRhs` in `obj-literal-var-field-growth.ts` cover both directions.
This retains the existing field validation and growth rules.

Local-object growth also requires the receiver name not to be visibly rebound
by the key or RHS. Such assignments use ordinary target checking before RHS
evaluation, so a write through the captured object cannot add fields to the
replacement object's type. The write-name scan includes array-destructuring
targets and conservatively includes nested closure bodies; hidden callee effects
remain open. `replacedReceiver` rejects growth attributed to the replacement,
while `retainedReceiver` keeps an existing-field write through the original
object valid in `obj-literal-var-field-growth.ts`.

Arithmetic compound assignments now capture the target read and setter before
checking the RHS, then validate the result against that setter. They share the
ordinary arithmetic typing operation instead of duplicating the target through
an assignment rewrite. `compound-computed-key.ts`, promoted from unsupported
conformance coverage, exercises a side-effecting computed key that previously
triggered the duplicate-expression invariant. An explicitly typed numeric field
accepts; the unannotated literal-field case retains the widening restriction
also seen in ordinary read/write assignments, now as a diagnostic rather than
a crash. Logical and nullish compound assignments share the captured setter
and write validation, with the RHS and write inside a conditional scope. Their
expression result combines the skipped value and RHS, preserving stable alias
contracts; local bindings retain that selected value after the effect merge.
`logical-compound-computed-key.ts` covers computed `??=` and `&&=` targets;
`logical-compound-flow.ts` checks that `||=` does not make RHS effects definite
and that `??=` leaves a local non-null. Hidden callee effects and general R2
validation remain separate obligations.

Postfix updates use the same captured setter and write validation. Previously
member/index `++` and `--` checked only the old numeric value, accepting writes
to readonly and numeric-literal fields. `increment-narrowing.ts` covers both
rejections and a valid computed-key update. Local updates now use `TCEnv.writeVar`
so exception and loop write tracking observe them as ordinary assignments.
The existing numeric operand restriction and widened expression result remain.

Local runtime writes check binding immutability in `TCEnv.writeVar`, before
recording effects or changing flow types. This enforces the const assumption
already used when retaining binding facts across captures and loops. `const-writes.ts` covers assignments,
updates, destructuring, and captured compound writes; a const-bound object's
writable fields remain mutable. Initialization and control-flow refinement use
separate scope operations and do not count as reassignment. Object-field growth
uses `updateObjectType`: it updates the view of the same reference, retaining
effect tracking without requiring a mutable binding, including constructor `this`.

Assignment-target validation treats receivers as values rather than nested
assignment targets. `assignment-receivers.ts` accepts ordinary, compound, and
postfix writes through returned objects and logical writes through a selected
object. The access-chain check still rejects optional links, including through
computed access and calls; the parser's existing loss of parenthesis boundaries
means this remains conservative for explicitly grouped optional chains.

Array-destructuring assignment defaults capture a property/index target before
checking the fallback, retaining the receiver and setter through fallback
effects. Nested patterns still process their targets after defaulting the
nested source. `keyBeforeDefault` and `keyClearsDefault` in
`destructuring-assignment.ts` cover keys that initialize or clear a fallback
variable: the former now accepts and the latter rejects the null write.
Destructuring targets, with or without defaults, and update expressions share
`writeCapturedTarget` for contract validation, local write tracking, and property
refinement invalidation; target evaluation remains with each syntax form.

Fixed-size destructuring patterns also project differing-length tuple unions
positionally. Every alternative must be tuple-shaped; a missing position adds
`undefined`, while a position present in every alternative keeps its element
union. Declarations and assignments share the projection through
`destructuringElements`. `destructuring-tuple-union.ts` accepts the guaranteed first element in an
assignment, keeps distinct positional types in a heterogeneous declaration,
and rejects reading a possibly missing second element as `number`. This value projection is not a new tuple
type and is not used to infer rest-array lengths. Rest patterns separately union
the unconsumed elements of every tuple alternative into a fresh array type.
An exhausted alternative contributes no elements, whereas an absent prefix
position contributes `undefined`. `destructuring-tuple-rest-union.ts` covers
excluding a consumed head, preserving a generic tail element, and rejecting an
incompatible tail target. All-empty remainders retain fresh-array inference.
Uniform-length tuple rest representations remain unchanged; differing lengths
are not exposed as a precise union of tuple lengths.

Local declaration statements reserve all their names before checking any
source or default, using the same pending-binding mechanism as parameters.
This includes plain names, nested patterns, and later declarators in a single
statement. Each reserved name shadows top-level namesakes while uninitialized;
initialization then installs its projected type and preserves const/let
mutability and contract flags. `binding-initialization.ts` covers self-reference,
a later declarator, and an earlier initialized declarator; `destructuring.ts`
covers references within patterns. Block entry also reserves direct declarations before checking its statements,
after the entry condition has been interpreted in the enclosing environment.
One statement-list checker performs reservation and ordered checking for ordinary,
try, catch, and finally blocks. Their exception-write logs and scope merges
remain at the existing boundaries. `binding-initialization.ts` covers a later
finally declaration and separation between try and finally locals.
Reservation is idempotent by declaration position, so the statement pass cannot
replace the block's binding identity. The redeclaration check distinguishes
a future outer reservation from the current scope, preserving existing valid
callback parameters and sibling local-object reuse. Reserved placeholders
are not value claims and are omitted from exported statement environments. `binding-initialization.ts` covers a read
before a later statement and a condition evaluated before entering a block
with a same-named local. Nested blocks reserve their own direct declarations;
switch labels and case entries reserve the union of direct case declarations,
while explicit nested blocks stay separate. The discriminant is checked before
that scope is introduced. Each case starts conservatively uninitialized because
execution can jump to it directly; deferred reads and proving initialization
solely through case-to-case fallthrough remain separate limitations.
`switch-scope-merge.ts` covers cross-case and label lookup plus an explicit-block
control. Existing outer-variable switch merges retain their behavior. For-in
and for-of declarations use the same reservation before evaluating their source;
otherwise `for (const items of items)` could resolve the outer name instead of
rejecting the uninitialized loop binding. `for-in-for-of-invalid.ts` covers this
failure and restoration of a shadowed outer name after a valid loop.

Default-result typing now uses one `defaultedValueType` operation for object,
tuple, iterable, assignment, and whole-parameter defaults. It establishes the
source read type in the live substitution, removes `undefined`, and then unions
the default result. Previously subtraction left inferred field/element
candidates unresolved, so their `undefined` member survived: a supplied
`number | undefined` followed by a numeric default could not be returned as
`number`. An annotated source or an established tuple already worked.
`destructuring.ts` covers the repaired declaration and assignment paths and
retains rejection when the source includes `null` or the default can itself
return `undefined`. This is a completeness repair with a shared read contract;
the conditional-effect merge and general R2 obligations remain separate.

Nullish coalescing now checks its fallback in a child scope and uses the same
conditional scope merge as `&&` and `||`. Previously `??` checked the fallback
in the enclosing scope, so a skipped assignment could justify an invalid
numeric return. The fallback's current and stable result types are captured
inside its branch, before merging effects; the expression's selected value
does not acquire the untouched binding's old value. `nullish-coalescing.ts`
covers the rejected stale read, a possible invalidating write, and returning
the expression result. As with the other conditional merges, both effect
paths are conservatively retained even for a statically known left operand.

Optional method calls `obj?.m(args)` likewise merge argument effects with the
skipped path when the receiver may be nullish. Previously the receiver's
short-circuit contributed `undefined` to the result but argument writes were
unconditional in the surrounding scope. The existing receiver classification
keeps definitely present calls and always-nullish receivers on their original
paths. `optional-chaining-method-call.ts` covers a rejected read after a skipped
argument, a possible invalidating write, and using the optional result. This does
not add optional function-call or optional computed-access syntax.

Ternary expressions now merge both branch scopes after retaining their current
and stable result types. Previously both scopes were discarded: a possible
write could leave an earlier narrowing incorrectly available, while assigning
in both branches still failed definite assignment. `test_ternary_refinements.ts`
covers the rejected stale read, the newly accepted two-branch initialization,
and continued rejection when only one branch initializes. The existing scope
merge supplies the union of values and intersection of initialization facts;
there is no untouched third path for a ternary expression.

Condition refinement now carries a conservative write summary through logical
structure. Tests whose referenced names intersect that summary do not refine:
the expression has already run, and a fact about a pre-write value cannot be
applied to the post-evaluation scope. This rejects both a non-null test followed
by a null assignment in `&&` and a comparison that overwrites its own operand.
Tests independent of the written names still contribute facts.
`issue-89-and-or-narrowing.ts` covers both failures and an unaffected check.
The summary reuses `CaptureWrites`: shadowed and nested names may reduce
precision, and unknown write targets suppress condition refinement. It does
not model hidden callee effects or provide general alias-effect analysis.
Separate a write from a subsequent test when the conservative dependency check
cannot retain an otherwise valid narrowing.

The `satisfies` wrapper propagates the operand's stable alias contract and
returns its inferred expression type. Previously wrapping a narrowed object in
`x satisfies unknown` erased the stable-expression metadata, allowing both an
annotated narrow alias and an inferred alias to survive an invalidating write
through `x`. `satisfies.ts` covers both rejections and an accepted scalar snapshot.

Its mandatory subtype check now retains commitments in the live substitution.
`satisfiesValidationStability` demonstrates the previous rollback failure: an
inferred numeric field passed the check, a string write succeeded, and the same
check then failed. The incompatible write now rejects, matching strict tsc;
compatible writes remain accepted. This is a validation-stability repair, not
a demonstrated runtime counterexample or general immutable evidence.

Returning the inferred type does not mean undoing every inference commitment:
a writable target can determine literal fields' lasting types. The old
`testObjectPreservation` expected `8080` and `"localhost"` after validating against
writable `number`/`string` fields. Strict tsc rejects those literal annotations
too. The test now expects the rejection; `closed-type.ts` likewise records
numeric target widening through `Closed`. An explicit literal-target counterpart
and the scalar literal test retain their precision. This retains
TypeScript-compatible literal precision while keeping validation commitments;
it does not replace the result by the target type.

Non-null assertions now apply their nullish removal to the operand's stable
alias contract as well as its current expression type. Removing null from a
reference cannot strengthen the lasting contract of its fields.
`postfix-exclamation.ts` covers rejection of an annotated alias formed through
a redundant `!`, while a copied scalar still survives a later field write.
The existing assertion restrictions and for-in exception are unchanged.
Checked `as` casts now validate their target against the source's stable alias
contract. Previously a temporary field refinement could justify a lasting
target view that a later write invalidated. `as-operator.ts` covers rejection
at the cast and an accepted scalar snapshot; existing tests retain primitive
narrowing and object upcasts. The cast still produces the target type, including
during error recovery. This uses the same source-validation boundary as an
annotation rather than merely forwarding identity metadata.

`await` now carries an awaited stable operand contract when its operand has
transient field refinements. The normal expression result still uses the
current type; storing or passing an alias uses the stable contract, flattened
through the existing thenable operation. `promise-object.ts` covers an object
passed through `await` whose field is later overwritten and an accepted scalar
snapshot. Non-thenable awaits remain lint warnings. This closes a contract
propagation gap; it does not model mutations by other code during suspension.

Assignment expressions now forward the right-hand side's stable alias contract
at the shared assignment boundary, before property-write invalidation. Updating
the target correctly was insufficient: retaining `(y = x)` could still expose
`x`'s temporary field facts as a new alias contract. `unsound-refinement.ts`
covers rejection through that result and an accepted scalar assignment snapshot.
The right-hand side is looked up after its existing evaluation, not evaluated
again; target validation and recorded lvalue types are unchanged.

M1 implementation scope: visible property writes invalidate object-content
refinements on bindings with declared or inherited contracts. Object alternatives
come from the contract; current primitive alternatives remain, preserving scalar
and non-null reference facts. Destructuring and compound writes use the same
rule, as do member increments/decrements. Growable objects retain their separate
initialization state. Coverage is in
[`unsound-refinement.ts`](../tests/expect-error/unsound-refinement.ts), including
aliases established before narrowing, readonly views, and fresh checks after writes.
This also rejects the pipeline's compound-write #598 witnesses. Their obsolete
candidate generator has been retired; first-error exports and runtime results
remain tested. Direct annotated aliases and direct assignments into variables or
properties validate against that same stable content projection: a temporary field check
cannot justify a permanently narrow mutable or readonly view. Non-null
references, scalar snapshots, and selection
among declared discriminated-union alternatives remain usable. Existing
`field-refinement.ts` tests cover the latter; no duplicate examples are needed.
Existing property and index slots validate their contracts, including the local
object and constructor-initialization paths. Added fields store the stable type
of an aliased source. The regression distinguishes rejection at a fixed slot
from safe widening of an inferred slot followed by rejection of a stale read;
a checked scalar snapshot remains usable. Nested field narrowing is separate.
Named and computed object-literal fields use the same stable alias projection
before field inference/growth. This includes a conditional alias stored in a
computed field; the computation of the key does not change the value contract.
Object spread and rest keep current scalar snapshots while projecting copied
object aliases through stable source contracts, as described above. General
field subtyping remains separate.
Coverage is in `obj-literal-var-field-growth.ts`.
Array literals and readonly tuples store stable types for direct alias elements,
including the spread-array path. This protects subsequent destructuring as well
as saved arrays. Destructuring defaults use the same projection for assignments
and declarations (tuple, iterable, and object patterns). The declaration cases
include a callback escape and a fresh field check.
Conditional, logical and nullish selection compose stable alias types,
filtering the non-selected nullish/falsy alternatives as appropriate,
separately from their current read type. Storage and annotated alias validation
consume the composed type, including nested conditionals and inferred captures.
These symbolic expression contracts are not immutable substitution snapshots and
do not complete R2.
Return boundaries use stable alias contracts in block and expression bodies,
for explicit result checks and inference, before async awaiting. Fresh scalar
copies retain their precise result types. Field-refinement provenance distinguishes
these transient facts from runtime-kind checks (`typeof`, `instanceof`, and
`Array.isArray`), preserving the existing runtime-kind return tests. The marker
propagates through aliases and control-flow merges; combining runtime-kind and
field narrowing can still lose precision.
Ordinary call arguments also use stable contracts before parameter checking and
generic inference. The regression covers a retained readonly argument, a generic
identity result, and a fresh scalar copy. Contextual callback typing remains on
its existing path.
Direct receiver aliases now validate explicit `this` contracts using stable
contents while member lookup uses the current read type. The projection accepts
the selected receiver branch, preserving distributed union calls and optional
receiver short-circuiting. A retained receiver and a fresh scalar-copy receiver
are covered; existing receiver tests cover dot/index access and union dispatch.
Composed receivers with stable-expression metadata now retrieve the contract
using the whole expression type, then project it onto the selected call branch.
Previously optional chaining removed null before metadata lookup, so
`(choose ? x : null)?.read()` could retain a transient numeric field through an
explicit `this` contract. `optional-chaining-method-call.ts` covers rejection
of that call and acceptance when the receiver copies the checked scalar.
The projection reuses the narrowed-local rule, including branch compatibility
and primitive/nullish selection; member lookup keeps the current receiver type.
M1 stays open for other alias-producing expressions,
uncontracted inferred source objects, growing source objects, and effects hidden
behind calls. This validates recorded alias contracts, not general field subtyping. Assignment validation preserves the destination contract while the
current read type can still reflect the assigned value.

Extracting a class method now converts its implicit class receiver into an
explicit receiver requirement. The implicit receiver shortcuts are justified
for attached methods and whole-object comparisons; retaining them on a detached
value allowed both retyping a method to a different class's method type and
reattaching it to an incompatible object. The method could then access missing
fields on its new carrier. Strict tsc also accepts these unsafe programs.

`this-parameter-implicit-class.ts` covers incompatible retyping, direct
reattachment, and a declaration-level `typeof` alias, plus compatible
reattachment. Expression property reads (dot/index, including optional reads)
and declaration-level member `typeof` share the extraction rule. Object
destructuring applies it at field binding too, covering local and parameter
patterns that bypass expression property access; compatible carriers still
check. Direct attached calls keep their existing path, preserving
generic-container variance and union-receiver dispatch. This repairs receiver
provenance; general callee-effect tracking and R2 remain open.

Property-copy boundary: class-declared methods carry declaration provenance
separately from their callable receiver. Spread and rest make these
copied properties optional: lookup can find a prototype method that copying
omits, but an own override may supply the property. Existing spread merging
therefore keeps the earlier property's alternative instead of assuming that
the method always overwrites it. Copies also establish the extracted method's
explicit receiver requirement. Own function-valued fields and class data fields
remain copyable. `spread-callable.ts` pins the previously accepted missing-method
calls through spread/rest and these positive controls.

The shared property-copy operation removes the source's call and constructor
signatures. Rest previously retained both and accepted invoking the fresh plain
object. `spread-callable.ts` rejects both operations and preserves a callable
property on the copy. Spread already discarded these capabilities when merging
fields; both paths now apply the same rule before field processing. Copying
also establishes the non-array brand. Retaining an array source's brand made
the reachable negative branch of `Array.isArray(copy)` type as `never`, allowing
the plain copy to satisfy a Boolean return contract. `array-isarray-refinement.ts`
pins this rejection and numeric-entry access in that branch.

Annotated local initializers retain recorded class-method copy provenance
on matching fields of the annotation. This preserves the annotation's value
contract while avoiding a new promise about ownership. Names and unique-symbol
keys are tracked separately; any source branch carrying the marker makes the
corresponding annotated field conservative. `spread-callable.ts` covers a
readonly function-property annotation that previously enabled a missing-method
call, and an annotated own function field that remains copyable.

Runtime variable writes also retain the assigned value's recorded copy
provenance in the binding's declared contract. Capture can otherwise restore
an older structural annotation after a class-instance assignment and promise
that the missing method will be copied. `spread-callable.ts` pins this
assignment-to-capture path and the counterpart using an own function field.
The shared write path adds provenance monotonically; it does not replace the
declared value types with the assigned value's narrower types. Control-flow
merges retain the incoming contracts' copy provenance alongside the parent's
value contract: sibling and N-way merges, fallthrough, jump snapshots, and
finally edges follow this rule. Exception write logs recover it from their
recorded value types. The conditional-assignment and catch-capture regressions
in `spread-callable.ts` distinguish ordinary branch contracts from the type-only
exception log; both previously restored an unsafe contract for a closure.

The field marker is `mayBeOmittedByCopy`: instance methods can be inherited,
and static methods are own but non-enumerable. Both may be absent from a copy;
static data fields still copy. `spread-callable.ts` covers the static-method
failure and static-data counterpart. This generalizes the same copy rule rather
than inferring ownership from the callable's receiver.

Named-field subtyping rejects erasing recorded copy uncertainty. This
closes parameter and declared-result boundaries: a class instance cannot satisfy
a readonly function-property contract that would promise a copied method.
Local annotations and variable writes retain the marker before validation;
function boundaries can instead receive an explicitly constructed own property,
such as `{ read: source.read }`. `spread-callable.ts` pins parameter/result
erasure and this own-property counterpart. Nested named-field comparisons use
the same check; local provenance propagation remains shallow.

Declared index signatures retain copy uncertainty: they constrain lookup
values without promising own enumerable entries. This includes class, object,
and mapped index declarations. An `in` guard can make an indexed field required
without proving it will be copied; the materialized field keeps the marker.
The indexed-copy regression in `spread-callable.ts` rejects checking presence
on the source and then calling through the copy, while checking the copy's
presence remains accepted. Named-to-index subtyping also preserves the
constraint. Synthetic literal indexes remain inference-only and are excluded
from this field-contract check. The recursive EagerCollection regression
remains accepted; index contracts admit lookup-only members instead of
rejecting those values outright. The reverse comparison, from an index to an
optional named field, likewise rejects dropping the copy constraint. Optionality
allows absence during lookup; an `in` guard does not make an inherited entry
copyable. `index-signatures.ts` pins the erasing result contract and a counterpart
that reads the value and explicitly constructs an own field. Index-to-index
comparison preserves the same constraint: `typeof` an actual copy cannot be
reused to give its source an own-entry guarantee. `index-signatures.ts` covers
this annotation bypass and accepting an actual copy under the same contract.

This is a bounded repair for recorded method provenance, not a complete model
of own enumerable properties. Sources whose provenance is already absent,
including structural declarations without a recorded class-method origin,
remain outside that guarantee. Ordinary fields supplied by inherited accessors and non-enumerable
properties are not classified. Union field construction retains uncertainty
from either input; intersection preserves a definite copy guarantee from either
conjunct. The existing tuple refinement and variadic inference tests guard the
intersection of definite tuple elements with uncertain array indexes. A general
ownership contract must also constrain subtyping and provenance-erasing
annotations. Receiver types alone cannot supply that contract.

M3 implementation scope: loop entry widens possibly assigned mutable bindings
with declared or inherited contracts before the repeated condition/body is
checked. The syntactic summary includes `for` increments and nested bodies,
including `continue`/`finally` paths; unknown targets conservatively include all
such bindings. Fresh guards narrow again, and unwritten bindings retain their
facts. Scalar exit bounds combine entry values with actual runtime writes, so
a broader loop invariant does not invent extra exit values. Both while and for
conditions establish fresh body refinements. Coverage in
`loop-carried-narrowing.ts` distinguishes while-body writes,
for increments reached by continue, and for-of body writes. Hidden call effects,
uncontracted evolving bindings, and general alias mutation remain separate work.
The original reduction is rejected, the valid guarded counterparts pass, and
the existing break/finally exit tests retain their behavior. The checker suite
and all 41 pipeline suites pass with zero corpus mismatches; M3's stated
completion criterion is met.

M2 implementation scope: reads across a function boundary discard enclosing
flow refinements for **annotated captures** and **captured mutable bindings with
concrete primitive inferred types**, whose declared types every write must
preserve. Primitive initializers retain their inferred type as a contract
across all writes, including writes before a closure declaration. Captured bare
inference variables share an inferred contract between writes and reads, as
described below. A const
binding does not stabilize mutable object contents, so field-bearing const
captures also fall back to their declared type. A whole-function assignment
summary, including nested closures, parameter defaults, and defaults inside
binding patterns, recovers field-free capture facts when the binding is never
reassigned. Pattern binding names are declarations; default expressions supply
the writes and captures, at their actual closure depth. `stablePattern` retains
a never-written scalar capture alongside unrelated destructuring, while
`patternWriter` and `patternReader` preserve checks for writes and reads nested
inside defaults. Unknown write targets and uninspected method bodies
conservatively disable this recovery. Name-based
write collection can over-approximate shadowed bindings, never overlook them.
Checks made inside the closure still narrow its reads; const value snapshots
retain their types. Claim environments use the same capture view.

The guarded, never-reassigned parameter examples in `callables/unions.ts`
remain accepted. Direct local aliases now inherit an explicit or previously
inherited source object contract. Completed inferred values retain symbolic
contents contracts regardless of initializer syntax. Bare inference candidates
and object initialization retain their separate rules. Stability under later
substitution growth (R2) and general alias mutation (M1) remain open work. Coverage:
[`captured-read-stability.ts`](../tests/expect-error/captured-read-stability.ts).
The full checker suite and all 41 pipeline suites pass, including inferred
primitive contracts, with no corpus outcome mismatches. The completion audit
at `b12c517c` reran both original stale-capture reproductions: each rejects at
the captured nullable access. `checkedCapturedLocal` and
`snapshotCapturedLocal` remain accepted. This meets M2's stated criterion;
it does not establish general stability under later substitution growth (R2),
hidden-witness growth (R1), or arbitrary alias mutation (M1).

The M2 regressions in the same test file cover:

- `inferredAliasCapture` and `aliasThenNarrow` reject stale captured reads
  using the source's declared object contract, preserved through direct local
  alias declarations. `checkedAliasChain` keeps an invocation-time check usable;
  `reassignedAlias` rejects a replacement that would invalidate that contract.
  `LocalRef.hasDeclaredContract` distinguishes these lasting contracts from
  transient flow types; it includes explicit annotations and inherited aliases.
  Field-free value snapshots retain their copied type. This is a capture repair,
  not M1 completion: visible writes now invalidate refinements of established
  object contracts and direct annotated aliases use stable contents. The general
  field-subtyping gap remains. Completed values from destructuring, calls, and
  property access use the contents-contract propagation described below.
- The evolving-binding repair makes every write constrain the same bare
  inference variable used by captured reads. Resolution seals that variable:
  `evolvingNullCapture` now rejects the unguarded nullable read,
  `checkedEvolvingCapture` accepts an invocation-time null check, and
  `sealedEvolvingCapture` rejects a later string write. Local null checks resolve
  the variable before narrowing, following the existing undefined-check
  discipline. These changes are implemented and tested separately from inferred
  object capture contracts; they do not complete R2 for the whole checker.
  Recursive read-before-write inference may need an annotation: the AVL
  example declares its intended `node | null` root contract explicitly.
- `inferredObjectCapture` rejects the stale read, and `checkedInferredObject`
  now accepts its invocation-time check. A tracked object literal binding acquires a
  contents contract at its first read, after field initialization has finished. Captured writes also establish this
  contract: both whole-binding replacements and optimized property writes can
  run after the enclosing frame has changed the binding.
  The contract retains the symbolic inferred field types, so ordinary reads
  seal inference dependencies rather than taking an unprotected snapshot.
  Direct aliases inherit that contract; captured reads and visible property
  writes discard transient field facts through the existing contract machinery.
  Field refinement resolves candidates in the live substitution only when the
  binding has a contract. Doing so for uncontracted objects would make stale
  closure reads unsoundly pass. The contract is keyed by declaration position
  in the type-checking environment, so a first read inside a callback or branch
  constrains later whole-binding replacements after that scope has been left.
  `replacedObjectCapture` and `branchObjectCapture` reject replacements that
  would change a callback's result or remove a required field;
  `checkedMutableObjectReplacement` accepts a guarded compatible replacement.
  The writer-before-reader witnesses preserve earlier callback writes: an
  incompatible whole-binding replacement rejects; an open field candidate can
  widen, but the later reader must then handle the earlier numeric field write.
  Both const and mutable tracked bindings use the same contract. This is a
  symbolic inference dependency, not the immutable snapshot required by R2.
- Completed inferred initializers retain a symbolic contents contract at
  binding time, independently of their syntax. The exceptions are growable
  local object literals and bare inference candidates. This makes later
  replacements and captured reads obey the same contract as explicitly typed
  bindings, without expanding generic result fields. `replacedCallResult`,
  `narrowedCallResult`, and `replacedConstructorResult` reject the witnessed
  escapes; `checkedGenericCallResult` keeps a fresh nullable-field check and
  compatible replacement usable. Bare inference-variable results keep their
  existing evolving-binding discipline. Result contracts enter the recursive
  pattern binder, so object fields, tuple/iterable elements, defaults, and rest
  bindings use the same propagation as explicit contracts. This replaces the
  direct-variable-only result special case. `replacedDestructuredResult` rejects
  replacement of an extracted object; `checkedDestructuredDefault` accepts a
  fresh check after a tuple-slot default, while `staleDestructuredDefault` still
  rejects the creation-time field promise. The same rule handles selection
  expressions and property reads: `selectedResultReplacement` rejects an
  incompatible replacement, `propertyResultCapture` rejects a stale captured
  field, and `checkedPropertyResult` preserves a fresh check. Destructuring an
  object literal also extracts completed values; it does not start local shape
  initialization. Field-free snapshots and bare inference candidates are not
  eagerly converted into contents contracts.

Parameter defaults use an invocation scope distinct from the enclosing frame.
All parameter binding names, including nested patterns and rest bindings, are
reserved before initializer checking. One ordered binding pass checks defaults
and establishes each projected contract for subsequent parameters and the body.
A default's child scope is discarded because supplying a value skips the
initializer; its assignments cannot narrow later defaults or the body. Pending
parameter identities also prevent writes before initialization. Coverage in
`arrow-default-param-optional.ts` includes rigid generic dependencies through
plain and destructured parameters, chained defaults, skipped assignments,
self-reference, and collisions with top-level names, both across parameters and
inside patterns. `skippedPatternDefault` rejects a nullable return previously
justified by a write in an optional field initializer. Deferred references to
later parameters inside default-created closures remain unsupported. Allowing
such captures needs evidence about when callbacks execute: a subsequent default
can call them before the captured parameter is initialized, even in a program
accepted by tsc.

Whole-parameter defaults distinguish the incoming contract from the initialized
value: the latter is the union of non-undefined incoming values and the default
result. Plain parameters retain their original annotation as the write/capture
contract. Destructuring projects from the initialized value. Coverage includes
preserving null, defaults that return undefined, reassignment to undefined,
deferred reads after such writes, and an optional whole-object input.

The original four outcomes occurred with the saved pre-repair binary.
Strict tsc
rejects the two stale object callbacks and the evolving binding's implicit
`any`, and accepts the invocation-time object check. The evolving-binding
repair changes the SKJS outcomes described above; M2's bounded completion
criterion is met.

The initial M1–M3 Boolean/null reductions were accepted and returned null at a
declared Boolean result. Lean does not have to
reject the export before these SKJS fixes start. Do not accept them by
introducing covariant mutable views.

Reuse of a cached expansion may remain valid across substitution changes when
the cached body is symbolic in its type arguments. An unchanged substitution
cannot rescue a key that conflates two definitions (R3a). Each cache has its
own policy; they are not required to share one.

## Later

Do not start these as SKJS implementation work until R3a/R3b have landed and
R1/R2 or the mutation family are in progress:

- Conditional types
- Higher-rank polymorphism
- Parameter-changing recursion
- Hidden type arguments as a first-class feature (after R1's use-level criteria)

Checking concrete instantiations of a generic remains regression testing. It
does not certify a generic body.

## Do not

- Rewrite SKJS to “be” the independent calculus or the source adapter fragment.
- Follow tsc when tsc is unsound ([holes](typescript-soundness-holes.md), [skjs-rules](../skjs-rules.md)).
- Treat a verification-pipeline `reject:` as a disproof of SKJS, or a failed search as incompleteness.
- Paper over M1–M3 with a weaker cell contract or a covariant mutable view.
- Change SKJS acceptance, inference, or diagnostics as a side effect of verification extraction work.
- Count closed-operation export as completing R2.

## Verification prototype limits

These constrain what the pipeline currently demonstrates. They are not SKJS
implementation blockers, and they are not completion criteria for the rows
above.

- **Operation recording is selective.** Closed operations are serialized after
  a successful `Clauses::isSub` path. That does not cover every early
  acceptance path (shortcuts, cached answers) and does not prove that SKJS's
  acceptance stays valid after later inference. Before relying on those
  exports, record coverage of attempted, recorded, and omitted operations.
- **Generic source extraction recognizes a small family of shapes**
  (identity, T-copy, bounded return). Those functions are not sent through
  ordinary graph-certificate checking. The parameterized lemmas are the
  justification for those shapes, not independent checking of arbitrary
  generic-body claims.
