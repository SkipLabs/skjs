# Unsound: the `isSub` reflexive-TSInst fast path accepts on an unsealed candidate binding, so a later contravariant grow breaks reads through the alias

Proposed labels: `soundness`, `bug`.

## Summary

`TType::isSub`'s reflexive-TSInst fast path accepts `TSInst<tvar> <:
TSInst<K>` when both sides carry the same name value and the tvar's
`peekRaw` binding equals the concrete argument. `peekRaw` returns the
*current* candidate of an **unsealed** `SVOpen` binding — without the
covariant seal the slow path performs (`Subst::get` covariant flips
`SVOpen → SVClosed`). Equality at the moment of the check is therefore
not stable: a later contravariant grow widens the candidate, and every
read through an alias the fast path blessed sees the widened value. The
accepted program below puts the string `"s"` in a `const n: number`.

## Minimal reproduction (self-contained)

Reproduction: [`repros/reflexive-tsinst-unsealed-read.ts`](repros/reflexive-tsinst-unsealed-read.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/reflexive-tsinst-unsealed-read.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

```ts
class Box<T> {
  v: T;
  constructor(x: T) { this.v = x; }
  get(): T { return this.v; }
  set(x: T): void { this.v = x; }
}
function mk<T>(x: T): Box<T> {
  return new Box(x);
}
function main(): void {
  const one: number = 1;
  const b = mk(one);          // T1 := open candidate `number`
  const r: Box<number> = b;   // FAST PATH: peekRaw(T1) = number; T1 NOT sealed
  b.set("s");                 // contravariant grow widens T1 to number|string
  const n: number = r.get();  // r aliases b: returns "s" typed number
  console.log(n);
}
main();
```

- SKJS: **exit 0, zero diagnostics**.
- node: prints `s` — `n: number` holds the string `"s"`.
- tsc `--strict`: rejects `b.set("s")` with `TS2345` (`b` is inferred
  `Box<number>` and stays it).

Differential probes isolating the mechanism (each **rejected**, i.e. the
protection works everywhere except through the fast path):

- annotate `const r: Box<number> | null = b` — the union blocks the fast
  path; the slow path's covariant grow **seals** T1, and `b.set("s")` is
  rejected;
- annotate `b: Box<number>` directly — rejected;
- move `b.set("s")` *before* `const r` — `peekRaw(T1)` is then
  `number|string ≠ number`, the fast path misses, rejected.

## Root cause

The arm (in `TType::isSub`, before `isSub_`) compares each argument pair
for equality, resolving a lone sub-side tvar via `subst.peekRaw` — a
`readonly` lookup that neither seals the binding nor registers any read
discipline. The slow path protects the same read by sealing at the
covariant grow (`isSub_` step (2) → `Subst::get` covariant,
`SVOpen → SVClosed`, `src/TTypeSubst.sk:199-208`). The arm's advertised
virtue — guidance-free, no state write — is exactly what skips the seal.
Equality of an open candidate is a fact about the *present* substitution
only; acceptance based on it is an exact-value read of an unsealed
candidate, which later contravariant growth (`Subst::grow`,
`src/TTypeSubst.sk:158-186`) invalidates.

A second, independent gap in the arm's justification: `peekRaw` ignores
`tvar.constraints`, so for a constrained variable the occurrence denotes
`⟦t₂⟧ ∩ ⋂⟦C⟧`, not `⟦t₂⟧` — the equality that lets the arm ignore the
variance of the argument position fails as stated.

## Relation to existing issues/PRs

- #737 introduced the arm (compare TSInst names by value in the isSub
  fast path), targeting an OOM on deep recursive generics. It added no
  regression test.
- #759 (post-merge review of #737) finds the arm **not load-bearing** on
  current `main` — the #736 `mapTParams` fix prevents the blowup
  upstream, and the fast path fires 0 times across the generated
  examples — and its "the algorithm is sound … it only fires when the
  tvars are already bound (so no inference/growth is skipped)" verdict
  is exactly what the witness above refutes: *bound* is not *sealed*.
- #758 tracks the separate name-collision hardening (name value alone
  does not identify a declaration across files); it is latent and
  unwitnessed, and unaffected by this issue.
- The corpus tracks this as the third witnessed instance of its
  monotone-reads obligation (registry rows L-SUB-TSINST, OBL-MONOTONE),
  alongside `instanceof-type-argument-sealing.md` and
  `freeze-window-stale-memo-caches.md`; unlike the memo instance it is
  not memo-mediated.

## Suggested fix

Three options, strongest first given #759's finding that the arm rescues
nothing on current `main`:

1. **Revert the arm** and rely on #736 (per #759's action item); re-add
   only with a load-bearing regression test.
2. **Restrict the arm to sealed bindings**: accept only when
   `subst.isClosed(tv)` (peekRaw of an `SVClosed` binding is stable),
   keeping the arm write-free.
3. **Seal what it reads**: resolve the tvar through a covariant
   `Subst::get` (sealing `SVOpen → SVClosed`) before accepting — keeps
   the arm's coverage at the cost of the no-state-write property.
