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

R3a (declaration identity), R3b (freeze-window), M2 (stale captured reads),
and M3 (loop-carried narrowing) meet their stated completion criteria.
The next architectural milestone is durable validation under substitution
changes (R2), including justified use of speculative clone results (R3c).
R1's later hidden-witness growth and M1's general alias mutation remain open.

| ID | Work | Status | Done when |
| --- | --- | --- | --- |
| R1 | Uses of `TParam`, inference `TVar`, and hidden witnesses preserve rigidity, scope, and identity | in progress | Specific forbidden transitions and escapes fail (a parameter is not solved as `?T`; a hidden witness does not become another object's; a captured/loop-escaped witness keeps its identity). Legitimate repeated uses of the *same* hidden witness still check. Not a wholesale TVar rewrite. |
| R2 | Propose vs validate, **and** later uses respect the snapshot | in progress | A subtype/expansion result is valid against an explicit snapshot **and** subsequent uses of that result respect the same snapshot, or the judgment is revalidated when a recorded dependency changes. Exporting a closed record under the subst at validation time does **not** count: that stabilizes the *exported* record, not SKJS's earlier acceptance. |
| R3a | Expansion keys identify the resolved declaration, not spelling | done | [expansion-key-collision](deep-dives/issues/expansion-key-collision.md): same-named aliases from different modules no longer share a cache entry; the unsound call is rejected; renaming the local alias still rejects; valid uses of each definition still check |
| R3b | Substitution-dependent answers track what can invalidate them | done | [freeze-window](deep-dives/issues/freeze-window-stale-memo-caches.md): a memo written while a candidate is unsealed is not reused after that candidate grows; the order-dependent acceptance is gone; the program without the priming call still rejects |
| R3c | Speculative clone results authorize the parent only with a justified transfer | in progress | A clone that does not commit cannot make the parent accept; any transfer of a clone result is justified by an explicit obligation |
| M1 | Alias writes: a narrow alias must not promise contents another alias may legally overwrite (`L-MUT-ALIAS`) | in progress | Reduced [narrowed-alias-stale-write](deep-dives/issues/narrowed-alias-stale-write.md) programs are rejected; a positive counterpart with a shared invariant still checks |
| M2 | Stale captured reads: a creation-time narrowing is not a captured arrow guarantee (`L-STALE-READ`) | done | Reduced [stale-closure-reads](deep-dives/issues/stale-closure-reads-narrowing.md) programs are rejected; a snapshot-or-null-check counterpart still checks |
| M3 | Loop-carried narrowing (`L-LOOP-CARRIED`) | done | SKJS rejects the [loop-carried](deep-dives/issues/loop-carried-narrowing-stale.md) reduction using its existing language and tests. Independent pipeline coverage of `let` is **not** a prerequisite. A counterpart that remains correct under SKJS's own loop checking (not source-level supplied invariants) still checks |

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
Later inference growth that introduces a hidden type after a boundary check
remains open; this does
not complete R1 or provide general existential packaging.

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
Object spread still reads current fields: copying a narrowed scalar is a
snapshot, while nested aliases and general field subtyping remain separate.
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
M1 stays open for spread-source contracts, distributed composed receivers, other alias-producing expressions,
uncontracted inferred source objects, growing source objects, and effects hidden
behind calls. This validates direct aliases, not general field subtyping. Assignment validation preserves the destination contract while the
current read type can still reflect the assigned value.

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
