# Unsound: `instanceof Array` narrowing installs a mutable `Array<top>` view

Proposed labels: `soundness`, `bug`, `narrowing`, `mutation`.

## Finding

The soundness model treats object membership as get-only and snapshot;
cross-view preservation is registry row `L-MUT-ALIAS`: a checked write
through one mutable view must preserve the membership guarantees of every
live alias. The property holds only while every mutable view of an object
carries set-types at or below the object's actual write capability. SKJS's
subtyping enforces exactly that: parameter and set
positions are checked contravariantly, so the covariant upcast

```ts
const x: Array<unknown> = a; // a: Array<number>
```

is rejected ("target parameter type unknown must be assignable to source
parameter type number"). No declared assignment can produce a wide mutable
view of an array.

The refiner produces one anyway. `evalInstanceof` special-cases `Array` to
the closed argument `top` on the mutable `Array` class, so the true branch
of `x instanceof Array` types `x` as `Array<top>` — a view whose index
set-type is `top` — for a runtime value whose actual element type may be
narrower. A write through that view is checked against `top` and accepted,
and it falsifies the sibling checked view's membership: after the write,
the value of an `Array<number>` local is no longer in `sem(Array<number>)`.
A later read typed through that membership then yields a value outside its
checked type, falsifying the capstone `L-TC`.

`L-INST` is not the broken row: `Array<top>` is membership-correct
(membership constrains through get-types, and every runtime array's
elements are in `sem(top)`). The failure is the write half — a set-governed
write through a view that subtyping would never have derived.

## Witness

Reproduction:
[`repros/instanceof-array-mutable-top-view.ts`](repros/instanceof-array-mutable-top-view.ts).
Run:

```sh
make check-file-in-docker \
  FILE=docs/deep-dives/issues/repros/instanceof-array-mutable-top-view.ts \
  BIN=target/host/dev/skjs
```

The essential program is:

```ts
function corrupt(a: Array<number>): number {
  const x: unknown = a;

  if (x instanceof Array) {
    x[0] = "s"; // accepted: the installed view is mutable Array<top>
  }

  return a.reduce(
    (acc: number, item: number): number => item,
    0,
  );
}

console.log(corrupt([1]));
```

- SKJS accepts with no diagnostics and no use of `any`.
- Node prints `s`: the `number`-typed `corrupt` returns a string.
- The control experiment replacing the narrowing with the declared upcast
  `const x: Array<unknown> = a; x[0] = "s"` is **rejected** by SKJS with
  the contravariance diagnostic above. The wide mutable view is reachable
  only through `instanceof Array`.
- tsc (strict) also accepts the witness, but through its declared escape
  hatch: it narrows `unknown` to `any[]`. tsc additionally accepts the
  covariant upcast by design (method bivariance). SKJS rejects that
  upcast, so within SKJS this is not a covariance-parity hole: the refiner
  mints a view the checker's own subtyping refuses to derive.

## Implementation correspondence

- `evalInstanceof` special-cases `Array` to the argument list `[top]` and
  builds the narrowed object from the mutable `Array` class
  (`src/TypeCheckRefine.sk`).
- The write `x[0] = "s"` resolves against `Array<top>`'s number index,
  whose set-type is `top`, and passes.
- The safe pattern is implemented next door: `evalIsArray` (the
  `Array.isArray` narrowing) intersects with `ReadonlyArray<unknown>`, and
  its comment says why — "never mutable `Array`"
  (`src/TypeCheckRefine.sk`). `ReadonlyArray` exposes no write surface, so
  the `top` argument is harmless there.

## Sound repair shape

Narrow `instanceof Array` through `ReadonlyArray<top>`, mirroring
`evalIsArray`. Reads keep working at `top`; writes through the narrowed
view are rejected, which is the correct verdict — the branch has no
evidence about the element type it would be writing at. Any repair that
keeps a mutable view must bound its set capabilities by the actual
arguments, which for `instanceof`-narrowing means a rigid/existential
argument rather than `top` (the same representation question as
[`instanceof-type-argument-sealing.md`](instanceof-type-argument-sealing.md)).

## Corpus location

The main paper owns `L-MUT-ALIAS` (`violated`), the cross-view facet of the
mutation model. This witness is distinct in
mechanism from issue #598 (same-view staleness: a write through the
narrowed view itself leaves the narrowed get-type stale; deep dive F's
rule W-Field repairs it). W-Field cannot repair this instance — the write
goes through `x`, and no rule firing on `x` can mend `a`'s membership.
Deep dive F's adequacy lemma for W-Field names the undischarged
cross-alias coherence hypothesis this witness realizes; here the
incoherent pair of views is created by refinement itself, with no declared
alias involved. Registry row affected: `L-MUT-ALIAS`.
