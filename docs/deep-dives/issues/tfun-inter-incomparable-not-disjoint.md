# Unsound: `TFun::inter` treats incomparable function signatures as disjoint

Proposed labels: `soundness`, `bug`, `narrowing`.

## Summary

`TFun::inter` returns `None` when neither signature subsumes the other, and
`TFields::inter` converts that into dropping the branch pair — but
"incomparable" is not "disjoint": a single function can inhabit both types
(e.g. via parameter contravariance). Equality narrowing between two such
function-typed values therefore types a reachable branch `never`.

## Minimal reproduction (self-contained)

The unsoundness is demonstrable end-to-end in one accepted program: the call
`t(h, h)` below is itself accepted (sound contravariance,
`(x: unknown) => void` is a subtype of both parameter types), so the branch
is reachable.

Reproduction: [`repros/tfun-inter-incomparable.ts`](repros/tfun-inter-incomparable.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/tfun-inter-incomparable.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS at `9108f339`: **exit 0, zero diagnostics** (including the `t(h, h)`
  call).
- node: prints `[Function: h]` — a function value inhabits `never` and flows
  into a `number` binding.
- tsc `--strict` (6.x): rejects the comparison with `TS2367` (no overlap);
  either way tsc rejects the program.

## Root cause

`TFun::inter` (`src/TTypeInter.sk`) returns `None` for incomparable
signatures; the consumer treats `None` as semantic disjointness.

## Relation to existing issues/PRs

The *type-level* collapse (`{(): string} & {(): number}` = `never`) is
acknowledged as a FIXME in `tests/expect-error/intersection-collapsing.ts:35`
and pinned in `tests/expect-error/function-intersection.ts` — known
incompleteness, no tracker issue found. The *soundness* consequence via
`===` narrowing is not tracked anywhere.

## Suggested fix

`TFun::inter` on incomparable signatures should over-approximate (e.g. keep
one side, or represent the intersection as an overloaded callable) rather
than return bottom; alternatively the `===` narrowing must not treat a
`None` function intersection as branch-dropping.

## Provenance

Deep dive B (`docs/deep-dives/lattice-operations.tex`, violated stratum
L-INTER-d); adversarially verified end-to-end 2026-07-05 — the witness is
a single accepted program. Main-paper assumption row: L-INTER-BOT (the bottom-implies-disjointness clause).
