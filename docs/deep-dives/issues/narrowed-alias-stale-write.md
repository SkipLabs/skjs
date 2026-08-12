# Unsound: field narrowing admits an alias whose view a later legal write breaks

Proposed labels: `soundness`, `bug`, `narrowing`, `mutation`.

## Finding

Registry row `L-MUT-ALIAS` requires a checked write through one alias to
preserve the types promised by every other live alias. Field subtyping
(`L-SUB-FIELDS-SET`) checks that values writable through a new alias are
also writable through the source. It does not check the converse: the
source may still accept a value that the alias's read type excludes.

Field narrowing exposes that missing check. `R-EqField`-style narrowing
changes the field's read type but leaves its write type at the wider
declared type. The narrowed object can then pass the covariant read and
contravariant write checks used to create an alias, even though a legal
write can invalidate either view:

- *write through the source*: the source retains a write type wider than
  its narrowed read type, which a narrower alias cannot survive — one legal
  write through the source falsifies the alias's membership;
- *write through the alias*: any alias whose write type exceeds the source's
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
  check imposes no write requirement on the source), and `y.f` goes stale
  the same way.
  Also accepted at the pin.
- The control experiments confirm the admission is narrowing-specific:
  without narrowing, the same alias assignment is rejected (get-covariance
  fails against the declared `number | null`), and the plain covariant
  field upcast `{f: number} → {f: number | string}` is rejected by the
  contravariant write check — declaration-only aliasing cannot build this
  pair of views.
- tsc (strict) rejects the witness: it narrows the *access* `x.f`, not
  the type of `x`, so the alias assignment fails TS2322. SKJS narrows the
  whole object type, which is what reaches the subtyping check. This is not
  a TypeScript-compatibility issue.

The write-through-alias witness
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
write-through-alias case, unlike the write-through-source case, matches tsc.)

## Implementation correspondence

- Field narrowing installs a get-narrowed object type; the field's
  set-type is not updated (`src/TypeCheckRefine.sk`, `narrowField` /
  `evalFieldEqualityType` via `withGet`).
- Subtyping checks reads covariantly against the *narrowed* read type and
  set contravariantly against the *declared* set, so the pair passes
  (`src/TTypeSubtyping.sk`, `TFields::isSub_`, shared-field arm).
- The write is checked against the source's resolved set-type
  (`src/TType.sk`, `TFields::resolveFieldType` with `isLValue`), which is
  still the declared `number | null`; it passes.

Each step satisfies its local check, but their composition exports a read
guarantee that a later legal write through another alias can invalidate.

## Suggested repairs

The repair must cover writes through either alias. When a field has been
narrowed, creating a mutable alias requires both cross-checks: the source's
write type must be contained in the target's read type, and the target's
write type must be contained in the source's narrowed read type. The second
check is vacuous for a readonly target. For ordinary declared fields these
conditions reduce to the existing checks, so declaration-only programs are
unaffected. Adding only one cross-check leaves one of the two witnesses
accepted.

Alternatives: re-widen (drop) the source's narrowing when a mutable alias
is exported, restoring agreement between its read and write types before
the pair exists; or the
invalidation route of deep dive F — extend the W-Field / P4 discipline so
a write through any view updates the flow entries of every same-object
local, including declared-typed ones — heavier, and needed anyway for
aliases created before narrowing.

## Corpus location

Deep dive H (`docs/deep-dives/view-coherence.tex`) owns `L-MUT-ALIAS` and
analyzes this as the alias-created-after-narrowing case. The separate
readonly-index problem in a type introduced by `instanceof` narrowing is
registry row `V-MINT-ROIDX`.
It shares its root with issue #598 — get-only narrowing leaves a wider
write type behind — but exploits it through an alias rather than through
the narrowed view itself. Deep dive
F's W-Field rule (which repairs #598 by re-widening the written view) does
not repair a write through `x`, because updating `x`'s entry does not repair
`y`'s stale type. A write through `y` is the same-function alias case that
F's extended W-Field/P4 discipline is specified to invalidate. Registry row
affected: `L-MUT-ALIAS` (`violated`).
