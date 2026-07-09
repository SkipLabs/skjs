# Unsound: `instanceof` narrowing's fresh type argument is sealed by the first covariant use

Proposed labels: `soundness`, `bug`, `narrowing`, `inference`.

## Summary

Narrowing `x instanceof Box` instantiates `Box` with a fresh inference
variable as the type argument. That variable is then *sealed by the first
covariant use* in the branch (`grow(cov)` on unbound → `SVClosed`), so the
narrowed type commits to whatever type the first read demanded — order-
dependent and unsound. The `instanceof Array` special case (argument fixed
to ⊤) is immune, which indicates the fix: instantiate narrowing-born
arguments at ⊤ (or as read-only), not as growable candidates.

## Minimal reproduction (self-contained)

Reproduction: [`repros/instanceof-arg-sealing.ts`](repros/instanceof-arg-sealing.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/instanceof-arg-sealing.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS at `9108f339`: **exit 0, zero diagnostics**. No `any` appears anywhere
  in the program.
- node: prints `42` — a number returned from a `string`-typed function.
- Order dependence (mechanism confirmation): adding a second read
  `const n: number = x.v` after the first makes SKJS reject with the error
  pointing at the *earlier* line — the first covariant use seals the
  argument.
- tsc `--strict` (5.7): **also accepts** — but by narrowing `unknown` to
  `Box<any>`, i.e. through its declared `any` escape hatch (both a `string`
  and a `number` read are accepted simultaneously). SKJS's failure is
  `any`-free and order-dependent, which is a different and worse failure
  mode; matching tsc would mean an explicit top/`any` argument, not a sealed
  one.

## Root cause

`evalInstanceof` builds the instance type via `makeTArgs` → fresh inference
candidates carrying declared bounds (`src/TypeCheckRefine.sk:352-365`); a
later covariant `Subst::get`/`grow` seals the unbound candidate to the first
expected type (`src/TTypeSubst.sk:188-208`). `instanceof Array` hardcodes
`[top]` and is immune.

## Relation to existing issues/PRs

Checked: #697/PR #702 (instanceof RHS constructibility), PRs #713/#721/#740
(candidate-widening discipline — different write path). The local
`tests/expect-error/instanceof-rhs.ts` file exercises RHS validity and
accepted construct/function RHS forms, but it does not inspect the type
arguments minted by successful narrowing. Not previously tracked.

## Suggested fix

Instantiate `instanceof`-born type arguments at ⊤ (as the `Array` case
already does), or mark them read-only so covariant contact cannot seal them.

## Provenance

Deep dive A (`docs/deep-dives/runtime-grounding.tex`, finding 11);
adversarially verified with runtime execution 2026-07-05; tsc's behavior
(accepts via `Box<any>`) confirmed in the same pass. Main-paper obligation
affected: Monotone Reads Under Growth (this
is a witnessed violation instance).
