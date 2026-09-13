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

R3a (declaration identity, `1e9f6330`) and R3b (freeze-window, `68c3b742`)
are complete. M2 has an initial capture-contract repair (`66bc1e32`); the
next step is to establish contracts for the remaining inferred captures.

| ID | Work | Status | Done when |
| --- | --- | --- | --- |
| R1 | Uses of `TParam`, inference `TVar`, and hidden witnesses preserve rigidity, scope, and identity | not started | Specific forbidden transitions and escapes fail (a parameter is not solved as `?T`; a hidden witness does not become another object's; a captured/loop-escaped witness keeps its identity). Legitimate repeated uses of the *same* hidden witness still check. Not a wholesale TVar rewrite. |
| R2 | Propose vs validate, **and** later uses respect the snapshot | not started | A subtype/expansion result is valid against an explicit snapshot **and** subsequent uses of that result respect the same snapshot, or the judgment is revalidated when a recorded dependency changes. Exporting a closed record under the subst at validation time does **not** count: that stabilizes the *exported* record, not SKJS's earlier acceptance. |
| R3a | Expansion keys identify the resolved declaration, not spelling | done | [expansion-key-collision](deep-dives/issues/expansion-key-collision.md): same-named aliases from different modules no longer share a cache entry; the unsound call is rejected; renaming the local alias still rejects; valid uses of each definition still check |
| R3b | Substitution-dependent answers track what can invalidate them | done | [freeze-window](deep-dives/issues/freeze-window-stale-memo-caches.md): a memo written while a candidate is unsealed is not reused after that candidate grows; the order-dependent acceptance is gone; the program without the priming call still rejects |
| R3c | Speculative clone results authorize the parent only with a justified transfer | not started | A clone that does not commit cannot make the parent accept; any transfer of a clone result is justified by an explicit obligation |
| M1 | Alias writes: a narrow alias must not promise contents another alias may legally overwrite (`L-MUT-ALIAS`) | in progress | Reduced [narrowed-alias-stale-write](deep-dives/issues/narrowed-alias-stale-write.md) programs are rejected; a positive counterpart with a shared invariant still checks |
| M2 | Stale captured reads: a creation-time narrowing is not a captured arrow guarantee (`L-STALE-READ`) | in progress | Reduced [stale-closure-reads](deep-dives/issues/stale-closure-reads-narrowing.md) programs are rejected; a snapshot-or-null-check counterpart still checks |
| M3 | Loop-carried narrowing (`L-LOOP-CARRIED`) | not started | SKJS rejects the [loop-carried](deep-dives/issues/loop-carried-narrowing-stale.md) reduction using its existing language and tests. Independent pipeline coverage of `let` is **not** a prerequisite. A counterpart that remains correct under SKJS's own loop checking (not source-level supplied invariants) still checks |

R3a implementation note: the initial cache-key patch alone still accepted the
witness. Named-instance hashes and a subtype shortcut also identified types by
spelling. The repair covers those equality paths as well as expansion keys and
instantiation guards. Recursive subtype comparisons also use resolved identity,
so equivalent imported mentions do not lose their cycle guard. Regression coverage is in
[`tests/projects/expansion-key-collision`](../tests/projects/expansion-key-collision):
the rejected flow, reverse expansion order, a renamed declaration, and a renamed
re-export of the same declaration. `make test-in-docker`, `make verify`, and
strict tsc on the regression project pass. The declaration-identity repair is complete.

R3b implementation note: subtype and intersection results computed while
`freezeCandidates` is set are not inserted into the substitution caches.
Those queries can read open candidates without sealing them, so their results
have no stability guarantee after growth. Ordinary cache reuse is unchanged.
[`freeze-window-stale-cache.ts`](../tests/expect-error/freeze-window-stale-cache.ts)
checks rejection with and without priming, plus repeated valid queries when
later growth remains within the constraint. `make test-in-docker` and
`make verify` pass. The freeze-window repair is complete.

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
Array literals and readonly tuples store stable types for direct alias elements,
including the spread-array path. This protects subsequent destructuring as well
as saved arrays. Destructuring defaults use the same projection for assignments
and declarations (tuple, iterable, and object patterns). The declaration cases
include a callback escape and a fresh field check.
Conditional expressions compose stable alias types in their branch scopes,
separately from their current read type. Storage and annotated alias validation
consume the composed type, including nested conditionals and inferred captures.
These symbolic expression contracts are not immutable substitution snapshots and
do not complete R2.
M1 stays open for call/return boundaries, other alias-producing expressions
(including logical selection and nullish coalescing),
uncontracted inferred source objects, growing source objects, and effects hidden
behind calls. This validates direct aliases, not general field subtyping. Assignment validation preserves the destination contract while the
current read type can still reflect the assigned value.

M2 implementation scope: reads across a function boundary discard enclosing
flow refinements for **annotated captures** and **captured mutable bindings with
concrete primitive inferred types**, whose declared types every write must
preserve. Primitive initializers retain their inferred type as a contract
across all writes, including writes before a closure declaration. Captured bare
inference variables share an inferred contract between writes and reads, as
described below. A const
binding does not stabilize mutable object contents, so field-bearing const
captures also fall back to their declared type. A whole-function assignment
summary, including nested closures and parameter defaults, recovers field-free
capture facts when the binding is never reassigned. Unknown write targets,
destructuring patterns,
and uninspected method bodies conservatively disable this recovery. Name-based
write collection can over-approximate shadowed bindings, never overlook them.
Checks made inside the closure still narrow its reads; const value snapshots
retain their types. Claim environments use the same capture view.

The guarded, never-reassigned parameter examples in `callables/unions.ts`
remain accepted. Direct local aliases now inherit an explicit or previously
inherited source object contract. Fresh inferred objects, other alias-producing
expressions, and compound types containing inference variables remain open work. Other noncaptured bindings retain ordinary
type evolution. Coverage:
[`captured-read-stability.ts`](../tests/expect-error/captured-read-stability.ts).
The full checker suite and all 41 pipeline suites pass, including inferred
primitive contracts, with no corpus outcome mismatches. This is not completion
of M2; the remaining inferred-contract cases are still open.

The M2 regressions in the same test file distinguish three obligations:

- `inferredAliasCapture` and `aliasThenNarrow` reject stale captured reads
  using the source's declared object contract, preserved through direct local
  alias declarations. `checkedAliasChain` keeps an invocation-time check usable;
  `reassignedAlias` rejects a replacement that would invalidate that contract.
  `LocalRef.hasDeclaredContract` distinguishes these lasting contracts from
  transient flow types; it includes explicit annotations and inherited aliases.
  Field-free value snapshots retain their copied type. This is a capture repair,
  not M1 completion: visible writes now invalidate refinements of established
  object contracts and direct annotated aliases use stable contents. The general
  field-subtyping gap remains; destructuring, calls, and property-access initializers are
  outside the direct-alias transfer implemented here.
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
- `inferredObjectCapture` already rejects the stale read, but the safe
  `checkedInferredObject` is also rejected. Restoring invocation-time narrowing
  is a separate completeness obligation; widening every read would lose it.

The original four outcomes occurred with the saved pre-repair binary.
Strict tsc
rejects the two stale object callbacks and the evolving binding's implicit
`any`, and accepts the invocation-time object check. The evolving-binding
repair changes the SKJS outcomes described above; M2 remains in progress.

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
