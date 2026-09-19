# R2/R3c: snapshot-owned validation

**Status: executable architectural experiment; not integrated into SKJS.**
R2 and R3c remain open. This directory changes neither checker acceptance nor
inference. It specifies the replacement boundary and tests its state protocol
before a Skip implementation is attempted.

Reviewed source: `verification/graph-core` at
`ca8fbd75c1b76a0eebc2bc48b1453f2fecf15de8`.
The implementation-status authority remains
[skjs-improvement.md](../../docs/skjs-improvement.md); the pinned soundness
corpus and its ledger are not repinned or upgraded by this experiment.

## Decision

**Keep heuristic inference. Do not let its return values authorize acceptance.**
Introduce an owner-local validation broker. It checks explicit judgments against
an immutable substitution snapshot, retains the original symbolic premises,
and controls reuse, clone transfer, and final publication. Start with whole-owner
invalidation. Dependency-directed invalidation is a later optimization, not a
precondition for getting the lifetime rule right.

This is stronger than wrapping `TType` in `Stable<TType>`. An immutable answer
can be wrong about the current source of that answer.

## Why the existing interfaces are insufficient

The relevant source boundaries are concrete:

| Boundary | Existing behavior | Required change |
| --- | --- | --- |
| [`SubstState.restore`](../../src/TTypeSubst.sk) | Restores `version`, bindings, origins, and four caches | Keep restoration transactional, but use a separate non-rewinding validation identity |
| `Subst.mcreate` / `clone` | Return another mutable substitution; private state may diverge | Identify the owner, inherited environment, and proposal-only authority explicitly |
| `Subst.grow` / `get` | Propose bindings and seal direct candidates; `SVClosed` may contain symbolic types | Invalidate snapshot receipts whenever semantic state changes; closing a binding is not transitive stability |
| [`TEnv.instantiate`](../../src/TEnv.sk) | Creates a private `Subst` from the caller's state and returns plain `TType` | Return a symbolic transformation or a derived result with retained obligations; no implicit private-to-parent promotion |
| `seenExpansion` | Caches `TType` under declaration identity and symbolic arguments | Preserve result provenance, not just the argument identity |
| Shape projections / alternative elimination | May erase an inspected dependency from their output | Retain the operation's original operands and the precise contract that licensed erasure |
| Source acceptance/publication | Uses successful local checks | Validate every active prerequisite at one snapshot, then retire the owner or retain an explicit guarded dependency on it |

This is a map of the first migration surface, not a new claim to have exhaustively
inventoried every function. The existing validation-lifetime and normalization-
transfer inventories remain useful. They do not supply the new API invariant.

## A minimal failure that determines the design

Consider a closed outer binding that still refers to an open inner one:

```text
rho(a) = Closed(b)       rho(b) = Open(number)
u = normalize(a)         // materialized result: number
check(u <= number)       // succeeds
rho(b) grows to number | string
```

Revalidating `number <= number` cannot find the lost dependency. Keeping an
immutable copy of `u`, sealing only `a`, or invalidating an expansion cache is
insufficient: `u` may already have escaped that cache into a later type.

The retained obligations must include:

```text
NormalizeEquals(original a, materialized number)
Subtype(materialized number, number)
```

After growth the first obligation fails, even though the second still succeeds.
For an approximating operation, retain its specified inclusion/containment
contract instead of inventing an equality requirement. A rejected replay may
require rebuilding the dependent derivation; it need not mean the source program
is unsafe. The first implementation may conservatively refuse that publication.

## Semantic interface

Let `E` be the immutable environment: resolved declaration identities, rigid
binder identities and bounds, language mode, and any other semantic inputs.
Let `S` be an immutable candidate store owned by `o`. A judgment descriptor `J`
contains its original symbolic operands, its environment, and its operation kind.
Write `holds(E, S, J)` for the intended contract, not for a successful call to
SKJS's existing mutating `isSub`.

The proposed public result categories are:

```text
Symbolic<A>       A transformation valid uniformly over the allowed stores
Proposal<J>       Guidance produced by speculative inference; no proof authority
Checked<J>        J was validated at (owner, snapshot, environment)
Derived<A>        A materialized answer plus every prerequisite used to derive it
```

`Symbolic` is a restricted interface, not an unchecked tag that callers can add.
Its constructors must not inspect mutable candidate meanings. Binder-aware
substitution and occurrence-level bounds remain part of its correctness contract.
Universal parameters and fixed hidden witnesses stay rigid; neither is solved by
the inference owner. A symbolic operator on an abstract parameter must not be
replaced by an operation on its upper bound merely to obtain a concrete answer.

`Checked<J>` is indexed by the **actual judgment**, not just its result type.
A receipt proving `A <= B` cannot authorize `C <= D`. Constructors are private to
the broker. `Derived<A>` composition unions its prerequisite handles; consumers
cannot extract an acceptance-relevant `A` while silently discarding them.
Printing and diagnostic previews may inspect proposals but cannot issue receipts.

The pure validator has no `grow`, sealing `get`, fresh-candidate allocation,
rollback, or live-cache-write capability. It returns a checked receipt or a
failure/blocked result. An unresolved candidate is not silently interpreted as
an inferred `never`. Recursive or unsupported cases without an established rule
are blocked, not accepted by an invented cycle convention. Failure to prove a
judgment is not in general a semantic disproof.

## Three gates

### 1. Reuse

The broker retains `J`, not only evaluated types. A receipt may be reused only
at its exact owner/snapshot/environment and for its recorded judgment. Otherwise
the broker replays **the original J** read-only against the current snapshot.

All semantic mutation invalidates the owner's checked-receipt cache initially.
This includes determination, growth, sealing, relevant mode changes, and restore.
It is intentionally conservative: an unrelated change may trigger extra checking
but must not cause a false rejection when the original judgment still holds.

The identity must not be `Subst.version`: that counter rewinds on restore and
can recur after different growth. Use an owner identity and a non-rewinding
snapshot nonce. Candidate identities also must not be accidentally reissued to
escaping clone-local or rolled-back references. The prototype uses session-wide
freshness; a production representation can instead prove equivalent owner/scope
isolation, but numeric counter equality alone is not that proof.

### 2. Clone transfer

A probe returns `Proposal<J>`. Parent acceptance ignores the probe's Boolean
preview and validates `J` in the parent's snapshot. This is **replay**, not
copying a child receipt or silently committing child constraints. Even a
non-mutating successful probe establishes nothing about later parent states.

Clone-created candidates cannot be smuggled into the parent by reusing numeric
IDs. A parent replay encountering an unresolved/private candidate is blocked.
When inference really needs a successful child's assignments, introduce a
separate transactional solver-commit operation: validate the base snapshot,
rename/check private identities, and commit the solver delta and prerequisite
journal together, then run pure validation. Such merging is not in the prototype;
it must not be hidden inside evidence transfer.

### 3. Publication

The active journal contains all acceptance-relevant judgments and materialization
premises. `finish` checks them at one immutable snapshot. Validation does not
change that snapshot, so there is no inference fixed point *inside* validation.
If inference runs again, its earlier tickets are stale and validation runs again.

An acceptance ticket identifies both the snapshot **and the complete active
obligation set**. Adding a premise invalidates an older ticket even if no
candidate changes. Failed checks remain pending; catching an exception does not
remove a typing requirement. Rolling back an abandoned alternative restores its
bindings and journal together. An escaped receipt for a rolled-back obligation
cannot be consumed.

Final publication retires the owner (`close` in the prototype). No later
inference mutates that owner. A continuing computation instead uses guarded
receipts, not an irrevocable acceptance verdict. Exported types must either be
closed in that validated store or retain its owner explicitly; a raw type graph
must not become reinterpretable under another mutable owner's substitution.
Cross-function or incremental consumers must carry this boundary too.

## The small theorem this architecture supports

Assume (1) the pure validator's success implies `holds(E,S,J)`, (2) every
acceptance-relevant premise, including provenance of materialized results, is
registered, and (3) broker constructors and store mutation obey the interfaces.
Then a successfully closed owner has

```text
for every J in its final active journal: holds(E, S_final, J).
```

Proof: `finish` checks every active descriptor at the same snapshot. Reused
receipts have the identical snapshot/environment and judgment. Stale receipts
are replayed; proposals have no authority. Final publication checks journal
coverage and retires the store. Therefore neither a changed substitution nor a
discarded child can justify a premise in the published journal.

This is a protocol argument, **not a Lean theorem or a soundness proof of SKJS**.
Premise (2) is substantive: wrapping subtyping's Boolean without retaining
normalization provenance, negative branch decisions, or caller scope does not
satisfy it. Runtime alias/effect soundness (M1), rigid-param semantics, and the
correctness of each operation's validator remain separate obligations.

## First production migration

Choose one complete vertical path:

```text
shape-inspecting normalization
  -> TEnv.instantiate
  -> seenExpansion
  -> the consuming subtype/source obligation
  -> checking-environment publication
```

Start with numeric indexed projection on a known tuple/array shape. Keep
unsupported abstract projections refused. A symbolic element can stay symbolic;
a materialized answer must retain the original projection judgment. This seam
exercises precisely the private-state/materialization boundary described by the
existing normalization-transfer audit.

Implement the broker and read-only snapshot view first. Route this path through
`Derived` results without an unchecked unwrap. Cache entries include prerequisite
handles. At the consumer and final publication gates, replay the original
projection alongside the subtype obligation. Cover nested candidate growth,
clone-only determination, rollback, and same-shape compatible controls. This
is one path-wide migration, not a claim to have closed all of R2/R3c.

Do **not** retry globally live normalization as the first change. The previous
owner prototype was withdrawn after resource failures; this design does not
make inference more eager. Nor is calling the current mutating `isSub` on a
clone a pure validator: that can solve the very question being checked.

Before making this production path authoritative, run the Skip build, focused
regressions, full checker suite, and verifier regressions. Measure repeated
normalization and cache growth against the unchanged branch. Do not trade away
accepted positive controls merely to satisfy an evidence wrapper. Only after
correctness and costs are measured should coarse invalidation be replaced with
transitive dependency tracking. That optimization needs read-set propagation
through cache hits, constraints, negative results, and fresh/private identities.

R2/R3c completion requires migrating every acceptance-relevant boundary and
establishing the above premises across them. This experiment does not change
those rows' `in progress` status.

## Executable evidence

From the repository root, with Python 3.10 or newer:

```sh
python3 -m unittest discover -s experiment/validation-lifetime -v
python3 experiment/validation-lifetime/demo.py
```

`model.py` implements immutable snapshots, proposal-only forks, original-operand
obligations, gated materialization, transactional journals, non-rewinding
freshness, read-only validation, and owner retirement. The type fragment consists
only of scalar atoms, finite unions, immutable tuples/records, and a few exact
projections. It deliberately blocks recursive candidate graphs and unsupported
shapes. It does not implement TypeScript or mutable-array subtyping.

`test_model.py` passes **27 tests**, including **7,168 length-three traces** over
initial types, target unions, growth, save/restore, freezing/thawing, and sealing.
That bounded slice uses an independently tracked finite-set oracle, not the
validator itself as its expected-result function. Dedicated tests cover the
private-solution, transitive-closed-binding, materialization, wrong-judgment,
identity, and publication boundaries outside that slice.

The demo prints three abstract counterexamples to insufficient protocols:

```text
Clone-only solution: probe preview = True
  Parent validation: BLOCKED (an unbound candidate is not an inferred bottom type)
Copied output: frozen downstream check = True
  Retained source-normalization obligation: REJECTED
Rollback/regrowth: numeric version repeats = True
  Snapshot identity repeats = False
```

These are **model traces**, not newly reproduced SKJS runtime counterexamples.
Python private attributes stand in for module-enforced capabilities; this is not
a claim of static enforcement by Python's type system. The standalone suite was
run; the Skip build and full SKJS/verifier suites were not run for this experiment.
No `.sk`, TypeScript acceptance fixture, or verification-calculus file is changed.
