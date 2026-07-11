# Unsound: field narrowing admits an alias whose view a later legal write breaks

Proposed labels: `soundness`, `bug`, `narrowing`, `mutation`.

## Finding

Cross-view mutation coherence (registry row `L-MUT-ALIAS`) requires that a
checked write through one view preserve the membership guarantees of every
live alias. The checker's admission gate (`isSub`'s field arms, registry
row `L-SUB-FIELDS-SET`) enforces the downward half: an admitted view's
set-types sit below the source's, so writes through the *alias* stay legal
for the *source*. Coherence of the pair additionally needs the source to be
**write-self-consistent** — its set-types below its own get-types — so that
writes through the *source* stay inside the guarantees it exported to the
alias.

Field narrowing manufactures exactly the non-self-consistent sources that
defeat this. `R-EqField`-style narrowing updates the field's get-type only;
the set-type keeps the declared width. The narrowed object then passes the
admission gate — the covariant get check sees the narrowed get, the
contravariant set check passes against the untouched wide set — and the
resulting pair of views is incoherent in **both directions**:

- *forward*: the source retains a write capability (`set` strictly above
  `get`) that a strictly narrower admitted view cannot survive — one legal
  write through the source falsifies the alias's membership;
- *reverse*: any admitted view whose set-type exceeds the source's
  narrowed get (already a same-type alias suffices) accepts a legal write
  that falsifies the source's own narrowing.

Either way, a later read typed through the falsified view yields a value
outside its checked type, falsifying the capstone `L-TC`.

## Witness

Reproduction:
[`repros/narrowed-alias-stale-write.ts`](repros/narrowed-alias-stale-write.ts).
Run:

```sh
make check-file-in-docker \
  FILE=docs/deep-dives/issues/repros/narrowed-alias-stale-write.ts \
  BIN=target/host/dev/skjs
```

The essential program is:

```ts
function w(x: { f: number | null }): number {
  if (x.f !== null) {
    const y: { f: number } = x; // admitted after narrowing
    x.f = null;                 // legal for x's declared set-type
    return y.f;                 // stale: y guarantees number
  }
  return 0;
}

console.log(w({ f: 1 }));
```

- SKJS accepts with no diagnostics; Node prints `null` — the
  `number`-typed `w` returns `null`.
- A `readonly` target shows the same failure and isolates the read half:
  `const y: { readonly f: number } = x` is likewise admitted (the readonly
  gate demands nothing of the source), and `y.f` goes stale the same way.
  Also accepted at the pin.
- The control experiments confirm the admission is narrowing-specific:
  without narrowing, the same alias assignment is rejected (get-covariance
  fails against the declared `number | null`), and the plain covariant
  field upcast `{f: number} → {f: number | string}` is rejected by the
  contravariant set gate — declaration-only aliasing cannot build this
  pair of views.
- tsc (strict) rejects the witness: it narrows the *access* `x.f`, not
  the type of `x`, so the alias assignment fails TS2322. SKJS narrows the
  whole object type, which is what reaches the gate. Not a parity hole.

The reverse direction
([`repros/narrowed-alias-stale-write-reverse.ts`](repros/narrowed-alias-stale-write-reverse.ts))
needs no narrower alias at all — a same-type alias is trivially admitted,
and the write goes through *it* while the *source's* narrowing goes stale:

```ts
function w(x: { f: number | null }): number {
  if (x.f !== null) {
    const y: { f: number | null } = x;
    y.f = null;  // legal for y
    return x.f;  // stale: x's narrowed view promises number
  }
  return 0;
}
```

Also accepted at the pin; Node prints `null`. (tsc accepts this shape too
— it does not connect `y`'s write back to `x.f`'s narrowing — so the
reverse direction, unlike the forward one, is tsc-parity.)

## Implementation correspondence

- Field narrowing installs a get-narrowed object type; the field's
  set-type is not updated (`src/TypeCheckRefine.sk`, `narrowField` /
  `evalFieldEqualityType` via `withGet`).
- The admission gate checks get covariantly against the *narrowed* get and
  set contravariantly against the *declared* set, so the pair passes
  (`src/TTypeSubtyping.sk`, `TFields::isSub_`, shared-field arm).
- The write is checked against the source's resolved set-type
  (`src/TType.sk`, `TFields::resolveFieldType` with `isLValue`), which is
  still the declared `number | null`; it passes.

Each step is locally correct against its own row; the defect is the
composition: admission from a view whose get-types sit strictly below its
set-types exports a snapshot guarantee the source's own write surface can
revoke.

## Sound repair shape

The coherence property is symmetric, so a sound admission-time repair
must restore it in both directions. When a source field's get-type sits
strictly below its set-type (a narrowed field), admitting a mutable alias
requires **both** cross containments: the source's set-type below the
target's get-type (blocks the forward witness) **and** the target's
set-type below the source's get-type (blocks the reverse witness — for a
readonly target this direction is vacuous). Equivalently: a mutable alias
may be exported from a narrowed source only if the pair is pairwise
coherent, which for self-consistent (declared) sources is exactly the
existing gate — declaration-only programs are unaffected. A one-sided
check is not a repair: it compensates for one consequence of the source's
self-inconsistency while leaving the other exposed.

Alternatives: re-widen (drop) the source's narrowing when a mutable alias
is exported, restoring self-consistency before the pair exists; or the
invalidation route of deep dive F — extend the W-Field / P4 discipline so
a write through any view updates the flow entries of every same-object
local, including declared-typed ones — heavier, and needed anyway for
aliases created before narrowing.

## Corpus location

Deep dive H (`docs/deep-dives/view-coherence.tex`) owns `L-MUT-ALIAS` and
grades this as the narrowing-admission site (the minted-view site is
[`instanceof-array-mutable-top-view.md`](instanceof-array-mutable-top-view.md)).
It shares its root with issue #598 — get-only narrowing breaks
write-self-consistency — but exploits it through an admitted alias rather
than through the narrowed view itself, in either direction, so deep dive
F's W-Field rule (which repairs #598 by re-widening the written view) does
not repair the forward shape (the write goes through `x`, and no update to
`x`'s entry mends `y`'s); the reverse shape is the same-function alias case
F's extended W-Field/P4 discipline is specified to havoc. Registry row
affected: `L-MUT-ALIAS` (`violated`).
