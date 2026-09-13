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

Start with R3a (expansion-key collision), then R3b (freeze-window). Both have
witnesses, a local cache obligation, and a positive control. That demonstrates
contract → targeted repair → regression before broader R1/R2 restructuring.

| ID | Work | Status | Done when |
| --- | --- | --- | --- |
| R1 | Uses of `TParam`, inference `TVar`, and hidden witnesses preserve rigidity, scope, and identity | not started | Specific forbidden transitions and escapes fail (a parameter is not solved as `?T`; a hidden witness does not become another object's; a captured/loop-escaped witness keeps its identity). Legitimate repeated uses of the *same* hidden witness still check. Not a wholesale TVar rewrite. |
| R2 | Propose vs validate, **and** later uses respect the snapshot | not started | A subtype/expansion result is valid against an explicit snapshot **and** subsequent uses of that result respect the same snapshot, or the judgment is revalidated when a recorded dependency changes. Exporting a closed record under the subst at validation time does **not** count: that stabilizes the *exported* record, not SKJS's earlier acceptance. |
| R3a | Expansion keys identify the resolved declaration, not spelling | done | [expansion-key-collision](deep-dives/issues/expansion-key-collision.md): same-named aliases from different modules no longer share a cache entry; the unsound call is rejected; renaming the local alias still rejects; valid uses of each definition still check |
| R3b | Substitution-dependent answers track what can invalidate them | not started | [freeze-window](deep-dives/issues/freeze-window-stale-memo-caches.md): a memo written while a candidate is unsealed is not reused after that candidate grows; the order-dependent acceptance is gone; the program without the priming call still rejects |
| R3c | Speculative clone results authorize the parent only with a justified transfer | not started | A clone that does not commit cannot make the parent accept; any transfer of a clone result is justified by an explicit obligation |
| M1 | Alias writes: a narrow alias must not promise contents another alias may legally overwrite (`L-MUT-ALIAS`) | not started | Reduced [narrowed-alias-stale-write](deep-dives/issues/narrowed-alias-stale-write.md) programs are rejected; a positive counterpart with a shared invariant still checks |
| M2 | Stale captured reads: a creation-time narrowing is not a captured arrow guarantee (`L-STALE-READ`) | not started | Reduced [stale-closure-reads](deep-dives/issues/stale-closure-reads-narrowing.md) programs are rejected; a snapshot-or-null-check counterpart still checks |
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
