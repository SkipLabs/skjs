# Unsound: `STypes::inter` zeroes the whole intersection when any shared tag is empty

Proposed labels: `soundness`, `bug`, `narrowing`. Priority: **high** — local
fix identified.

## Summary

Intersecting two unions that share a tag whose per-tag intersection is empty
collapses the *entire* result to bottom, discarding tags whose intersection is
nonempty. Equality narrowing (`x === y`) consumes this intersection, so a
reachable branch is typed `never` — and notably the checker emits **no**
"comparison is always false" warning for the same pair, i.e. its own overlap
analysis disagrees with `inter`.

## Minimal reproduction (self-contained)

Reproduction: [`repros/stypes-inter-zeroing.ts`](repros/stypes-inter-zeroing.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/stypes-inter-zeroing.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS at `9108f339`: **exit 0, zero diagnostics** (and no overlap warning).
- node: prints `a` — the branch is taken with `x = y = "a"`; the string `"a"`
  inhabits `never` and is laundered into a `number` binding.
- tsc `--strict`: rejects, `TS2322: Type '"a"' is not assignable to type
  'never'` (tsc narrows `x` to `"a"`).

Completeness dual (same root cause, not a soundness bug): the type
`("a" | 0) & ("a" | 1)` collapses to `never`, so `const c: C = "a"` is
spuriously rejected.

## Root cause

`STypes::inter`'s per-tag merge (`mapInterOption`/`mergeOption` in
`src/TTypeInter.sk`) treats any shared-tag-empty result as the zero of the
whole map instead of dropping that tag.

## Relation to existing issues/PRs

#584 / PR #592 introduced `x === y` narrowing; its pinned tests cover only
same-tag overlaps (`tests/expect-error/local-vs-local-refinement.ts`, e.g.
`"a" | "b"` compared with `"b" | "c"`). This witness is the mixed-tag case:
one shared string literal should survive while the numeric tag pair drops.
PR #677 (overlap warnings) computes overlap correctly, in tension with
`inter`. #655 is a different root cause (literal spellings). Not previously
tracked.

## Suggested fix

Drop empty shared tags from the intersection; return bottom only when *all*
tags drop.

## Verified fix

The suggested fix is implemented and verified — patch
[`fixes/stypes-inter-per-tag-zeroing.patch`](fixes/stypes-inter-per-tag-zeroing.patch)
(one line in `mapInterOption`: an empty shared key drops that key instead of
zeroing the whole map). Verified against the built checker: the witness above
flips from accepted to rejected, and the full test suite passes with no
regressions. Not landed in this branch — the registry row stays `violated` at
the pinned revision.

## Provenance

Deep dive B (`docs/deep-dives/lattice-operations.tex`, violated stratum
L-INTER-c); adversarially verified with runtime execution 2026-07-05.
Main-paper assumption row: L-INTER-BOT (the bottom-implies-disjointness
clause).
