# Unsound: `void === undefined`-typed comparison narrows the void side to `never` in the taken branch

Proposed labels: `soundness`, `bug`, `narrowing`.

## Summary

The checker's `void` type includes the runtime value
`undefined`: strict equality relates the two (`undefined === g()` is
true for a void-returning `g`). The dedicated undefined-literal rule
respects this — `x === undefined` filters the undefined and void units
jointly. But a comparison against an undefined-**typed** variable takes
the generic equality rule, which narrows the LHS by intersecting its
type with the RHS type — and the intersection treats the `void` and
`undefined` units as disjoint, producing `never`. A void-typed operand
of `===` draws only a warning (deliberately: using the value is
runtime-sound and tsc permits it), so the narrowing runs, and the
branch the runtime takes with both operands holding `undefined` is
typed as unreachable.

## Minimal reproduction (self-contained)

Reproduction: [`repros/void-undefined-equality-never.ts`](repros/void-undefined-equality-never.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/void-undefined-equality-never.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS: **exit 0, zero errors** (one warning,
  `@typescript-eslint/no-confusing-void-expression`, on the `===`
  operand).
- node: prints `branch taken at type never: undefined` — the
  `never`-typed binding holds `undefined` in a branch the runtime takes.
- tsc `--strict` (7.0.2): rejects, `TS2322: Type 'void' is not
  assignable to type 'never'` (tsc does not narrow `void` here) — the
  unsoundness is SKJS-specific.

## Root cause

`evalVarEquality`'s generic arm (`src/TypeCheckRefine.sk`, the
non-literal `otherExpr` case) installs
`inter(localType, otherType)` on the true branch; `TType::inter` keeps
the `TVoid` and `TUndefined` units disjoint, so
`inter(void, undefined) = never`. The dedicated undefined-literal case
immediately above it filters the two units jointly and is sound; only
the variable-RHS path reaches the disjoint intersection. The
void-operand check on `===` operands is a warning by design
(`src/TypeCheckExpr.sk`, "runtime-sound and tsc permits it"), so it
does not prevent the narrowing.

## Relation to existing issues/PRs

The undefined-literal comparison and the joint undefined/void treatment
in typeof narrowing are correct at the pin; this is specifically the
variable-RHS equality path. Not previously tracked.

## Suggested fix

Route strict-equality narrowing against an RHS whose type is the
`undefined` or `void` unit through the same joint-tag filter as the
`undefined`-literal case (keep or drop the undefined **and** void units
together), instead of the generic intersection. Equivalently: make the
equality-narrowing intersection ≈-closed by identifying the two units,
without changing `inter` elsewhere (assignability between `void` and
`undefined` should stay rejected).

## Provenance

Main paper (`docs/skjs-type-soundness.tex`), the strict-equality
closure hypothesis of the R-Eq rule (assumption L-SEQ) and its worked
example; adversarially verified with runtime execution 2026-08-07.
