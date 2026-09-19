# R2/R3c: the first projection path

**State: executable reference integration; not wired into production SKJS.**
The checker source inspected here is `feb3ac4effb6f22f8c92eb9ad1e8aec679b1d6eb`
on `verification/graph-core`. This work changes the experiment only. R2/R3c
remain in progress in `docs/skjs-improvement.md`.

## What this pass implements

`projection.py` exercises a complete reference path:

```text
resolved alias + symbolic arguments
  -> capture-avoiding alias expansion in an immutable catalog
  -> numeric projection retaining original operands
  -> owner-local cache containing derived handles, not bare answers
  -> subtype consumer carrying the projection prerequisites
  -> final replay of the active journal and owner retirement
```

This is not another Boolean wrapper around an existing solver. Its validators
read immutable snapshots and cannot grow, seal, or choose candidate bindings.
All environment inputs are captured in the judgment descriptor. A `Derived`
handle has no public type-value extraction operation; its value and prerequisite
receipts live together in the pipeline. Python privacy is still a stand-in for
module-enforced capabilities, not a defense against reflection or malicious
callers. A compiler must also register all actual source premises.

The type fragment is finite atoms, unions, immutable-structure comparisons, and
known array/tuple shapes used for numeric type projection. Catalog binders are
alias placeholders, not a model of bounded universal quantification. Rigid atoms
can be retained as elements, but cannot be projected through an imagined bound.
Recursive graphs, general records/index signatures, mutable-storage subtyping,
effects, and the full SKJS type system are not established by this experiment.

## Three findings that affect the architecture

### Register a request before attempting to produce its answer

The original `Owner.observe` normalized first and registered an equality only
on success. An unsolved or unsupported normalization raised `Blocked` before
adding any journal entry. Catching that error and calling `close()` accepted an
empty journal. That was a bug in our reference protocol, not a newly demonstrated
SKJS bug.

`observe` now first records that the original operation must be defined. The
projection path does the same for alias expansion, shape inspection, and frozen
materialization. A failed mandatory operation remains pending; only abandoning
its enclosing alternative through rollback removes it. A speculative probe is
different: it records nothing in the parent until the parent requests replay.

Two new tests fail on the old model and pass after the six-line repair. The
rollback and retry controls pass in both versions.

### A symbolic element is not a frozen answer

For an established shape, these transformations need not solve `?E`:

```text
ElementOf<Array<?E>>  -> ?E
ElementOf<[?E, string]> -> ?E | string
```

The projected expression retains the candidate identity. If `?E` later grows,
the projection equality can remain valid. A consumer requiring `?E <= number`
is separately rechecked and fails on incompatible growth. A consumer requiring
`?E <= number | string` can remain valid. Neither case needs a global eager
freeze of inference.

Freezing the answer to `number` creates an additional requirement:

```text
Materialize(?E) = number
```

A copied `number <= number` check cannot replace that requirement. Closing an
outer candidate also does not close the candidates in its payload.

### Cache hits must preserve the incoming derivation

Identical input types may arrive through different proofs or materializations.
A cache indexed by type syntax can reuse the computation, but must not erase the
prerequisites of the new caller. The reference path uses this rule:

```text
cache(op, t) = (answer, cachePrerequisites)
input       = (t, incomingPrerequisites)
reuse       = (answer, cachePrerequisites UNION incomingPrerequisites)
```

For example, `Array<number>` can be a source annotation or a frozen observation
of an evolving candidate. A projection primed by the source annotation must not
launder the second origin. The cache-hit regression deliberately tests that order.
Receipts removed by rollback are not resurrected: a later request recomputes its
own entry. Repeated identical inputs deduplicate prerequisites and reuse their
handle instead of growing the journal on every cache hit.

## Native source correspondence and required changes

This table maps to the inspected source, not to an implemented port.

| Source boundary | Observed code | Required production boundary |
| --- | --- | --- |
| `src/TEnv.sk`, `normalize`, `TAGet` arm | Creates `Subst::mcreate(tcenvb)`, normalizes the operand, calls `numberIndexedType` | Preserve the resolved source operand as a symbolic indexed expression; mandatory evaluation registers a request before attempting it |
| `TEnv.numberIndexedType` | Expands with a covariant read, collects `nIdx.get`, numeric named `field.get`, and string-index fallback, then unions results | Separate read-only shape inspection from symbolic member expressions; attach the exact projection obligation whenever shape is materialized |
| `TEnv.instantiate` | Creates a private substitution and returns a plain `TType` | Return only uniform symbolic expansion or a derived result with explicit transfer prerequisites; a private seal is not a parent seal |
| `src/TType.sk`, `expandToVectors` | Stores/returns plain `TType` in `seenExpansion` and flattens it into clauses/instances | Carry prerequisites on both misses and hits and through flattening; keep resolved declaration identity in the key |
| `src/TTypeSubst.sk`, `SubstState.restore` | Rewinds `version`, bindings, origins, and caches | Roll back the active obligation journal with the alternative, but do not rewind validation identity |
| Consuming subtype checks | Can grow/seal candidates while checking | Keep that phase as inference; replay explicit original premises with a read-only validator before they authorize acceptance |
| Checking-environment publication | Expression/final-return/constructor paths may have final checks after the body | Require one final journal check after the last inference operation; retire or explicitly guard any exported owner-dependent result |

The known-array/tuple rule in the reference is not a substitute for the native
`TField.get` semantics. A native snapshot exporter/validator must preserve the
read types, optionality already embedded in them, occurrence constraints, and
resolved builtin identities. It must not recognize a user-defined `Array` merely
by its spelling. General numeric fields and string-index fallback are outside
the reference evaluator, even though the existing native method handles them.

The first native port therefore needs a frozen input representation for the
chosen fragment and an explicit refusal for unsupported cases, not an adapter
that silently routes blocked validations back to mutating `isSub`. Keep current
unsupported abstract-projection guards until their own semantics are established.
Speculative/declaration-only requests must not be accidentally made mandatory.

## Concrete native acceptance criteria

A production change is ready to authorize acceptance only when all of these are
checked in the actual Skip implementation:

1. The path above never drops the original projection operand or a prerequisite,
   including cached expansions, union/flattening, clone return, and source use.
2. Snapshot validation does not change candidate values, constraints, allocation,
   sealing, modes, or live caches. An unbound outer shape is blocked, while an
   established shape with an unbound symbolic member can retain that member.
3. A false or blocked mandatory request cannot vanish after error recovery.
   Alternative rollback restores both inference state and pending requirements.
4. Incompatible late growth and copied-result witnesses reject; symbolic-member,
   same-projected-type, and unrelated-growth controls remain accepted.
5. Native focused and full checker tests, verifier regressions, and bounded cost
   measurements pass. Python tests are not evidence that the native bridge is
   wired correctly or that SKJS's existing judgment validators are sound.

A closure or incremental consumer may outlive the function currently being
checked. Retiring an owner is valid only when inference really is finished there;
otherwise its published result remains guarded. The R1 escape checks and M1
runtime-effect policy are separate obligations, not replaced by this work.

## Executed checks

The combined reference suite passes **64 tests**: the original 27, four request-
registration cases, and 33 projection-path cases. It retains the 7,168 bounded
state traces and adds 150 finite shape cases with an independent set-of-element-
labels oracle. The shape oracle covers nested closed outer bindings, ordinary
growth, frozen mode, and sealing.

Five deliberate mutations are detected by assertion failures (not import or
syntax errors): removing failed-request registration; removing final replay;
rewinding snapshot identity; dropping incoming provenance on cache hits; and
retaining shape-existence checks while omitting projection equality. This checks
that the relevant tests fail when those defenses are removed. It is not an
exhaustive mutation campaign or a soundness proof.

A 1,000-request reuse test performs 2,000 alias/projection cache hits without new
validator evaluations, obligations, or derived handles. This is a bounded
reference-model count, not a native performance claim. Unrelated growth triggers
revalidation but preserves acceptance.

Run from the repository root:

```sh
python3 -m unittest discover -s experiment/validation-lifetime -v
python3 experiment/validation-lifetime/mutation_check.py
```

The Skip compiler and Docker are not installed in the execution environment used
for this pass. The native build, checker suite, and verifier suite were not run.
No production `.sk` files were changed. The outstanding deliverable is the native
port with its real regressions and performance checks; the reference path does
not close R2/R3c.
