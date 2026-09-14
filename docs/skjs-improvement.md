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

Local declaration statements reserve all their names before checking any
source or default, using the same pending-binding mechanism as parameters.
This includes plain names, nested patterns, and later declarators in a single
statement. Each reserved name shadows top-level namesakes while uninitialized;
initialization then installs its projected type and preserves const/let
mutability and contract flags. `binding-initialization.ts` covers self-reference,
a later declarator, and an earlier initialized declarator; `destructuring.ts`
covers references within patterns. Block entry also reserves direct declarations before checking its statements,
after the entry condition has been interpreted in the enclosing environment.
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
Composed receivers with stable-expression metadata now retrieve the contract
using the whole expression type, then project it onto the selected call branch.
Previously optional chaining removed null before metadata lookup, so
`(choose ? x : null)?.read()` could retain a transient numeric field through an
explicit `this` contract. `optional-chaining-method-call.ts` covers rejection
of that call and acceptance when the receiver copies the checked scalar.
The projection reuses the narrowed-local rule, including branch compatibility
and primitive/nullish selection; member lookup keeps the current receiver type.
M1 stays open for spread-source contracts, other alias-producing expressions,
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
