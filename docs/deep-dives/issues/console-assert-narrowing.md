# Unsound: `console.assert(e)` narrows as if the assertion terminated, and matches by spelling alone

Proposed labels: `soundness`, `bug`, `narrowing`.

## Summary

After checking a call whose callee is spelled `console.assert`, the
checker applies the true refinement of the first argument to the
subsequent path. JavaScript gives no such guarantee: a failed
`console.assert` logs the failure and continues, so the code after the
call runs with the condition false. The match is also purely syntactic —
it does not verify that `console` denotes the global — so a local or
parameter named `console` with an arbitrary `assert` method triggers the
same refinement, letting any user-supplied method establish the
condition. Registry row L-ASSERT records that both required premises
are violated.

## Minimal reproduction (self-contained)

Reproduction: [`repros/console-assert-narrowing.ts`](repros/console-assert-narrowing.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/console-assert-narrowing.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS: **exit 0, zero diagnostics** — `x` is narrowed to `string` after
  the call.
- node: prints `Assertion failed`, continues, and throws
  `TypeError: Cannot read properties of null (reading 'length')` at the
  narrowed use.
- tsc `--strict`: rejects, `TS2322: Type 'string | null' is not
  assignable to type 'string'` (lib's `console.assert` is not an
  assertion signature) — the unsoundness is SKJS-specific.

Shadowed-receiver variant:
[`repros/console-assert-shadowed.ts`](repros/console-assert-shadowed.ts)
(expect: **accepted**) — a parameter named `console` whose `assert`
does nothing; node prints `n = null` at type `string`; tsc rejects the
same way.

## Root cause

`TypeCheckExpr.sk:2473-2481`: after a call is checked, the callee shape
`Dot(NormalDot(), Var("console"), "assert")` with at least one argument
triggers `evalCond(args[0], true)` on the current scope. Neither the
binding of `console` nor any termination property of the callee is
consulted.

## Relation to existing issues/PRs

The main paper documents the behavior in its refinement-rule list
(matched by call shape, receiver unverified) but no registry row
justified it; this report registers it as row L-ASSERT. Not previously
tracked.

## Suggested fix

Remove the refinement, or replace it with a genuine terminating
assertion intrinsic whose contract is registered (and whose receiver is
resolved, not spelled). Verifying that `console` is the global is not
sufficient: the global `console.assert` does not terminate on failure in
Node or browsers.

## Provenance

Found by the adversarial referee pass over the main paper
(`docs/adversarial-review-findings-2026-08-11.md`, finding 2); witnesses
executed against the pin binary, Node, and tsc. Main-paper rule list
entry: the `console.assert` clause of the refinement master list.
