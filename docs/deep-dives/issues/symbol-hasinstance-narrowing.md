# Unsound (tsc-parity, low priority): `instanceof` narrowing ignores `Symbol.hasInstance`

Proposed labels: `soundness`, `tsc-parity`, `low-priority`.

## Summary

`x instanceof C` narrows `x` to `C` even when `C` declares a
`static [Symbol.hasInstance]` that makes the check true for non-instances.
TypeScript has exactly the same behavior (verified), so this is a
tsc-parity unsoundness — filed for the record because the source explicitly
scopes it out and no tracker entry exists.

## Minimal reproduction (self-contained)

Reproduction: [`repros/symbol-hasinstance.ts`](repros/symbol-hasinstance.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/symbol-hasinstance.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS at `9108f339`: **exit 0, zero diagnostics**.
- node: prints `undefined` at type `number`.
- tsc `--strict --target es2022`: **also exit 0** — parity confirmed.

## Root cause (acknowledged in source)

`src/TypeCheckExpr.sk:2652-2655`, above `isInstanceofRhs`:

> Whether `rhsTy` is a valid `instanceof` right-hand side: every member of
> the type is a Function-like object (each branch carries a construct or
> call signature). Mirrors tsc's TS2359 acceptance (modulo
> `Symbol.hasInstance`, which SKJS does not model).

## Relation to existing issues/PRs

Closest existing coverage is #697 / PR #702 and
`tests/expect-error/instanceof-rhs.ts`, which check that the RHS value is
Function-like so `instanceof` itself will not throw. This issue is the
opposite side of the same source comment: the RHS is a valid class value, but
`Symbol.hasInstance` makes the runtime membership test disagree with the
nominal class narrowing. No existing test covers that narrowing effect.

## Suggested resolution

Either accept as a documented tsc-parity limitation (add to the known-unsound
documentation, cf. PR #600), or reject/ignore narrowing when the RHS class
declares `Symbol.hasInstance`.

## Provenance

Deep dive A (`docs/deep-dives/runtime-grounding.tex`, finding 10, assumption
A-HASINST); adversarially verified with runtime execution and tsc-parity
check 2026-07-05.
