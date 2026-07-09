# Unsound: string literal types store undecoded lexemes — escapes and line continuations (string-kind sibling of #655)

Proposed labels: `soundness`, `bug`, `literal-types`. Related: #655 (numeric
sibling; explicitly scoped to numeric/bigint, does not cover strings).

## Summary

String literal *types* store raw source lexemes with escape sequences
undecoded (`unquoteString` only strips quotes; its body carries a
`// TODO: handle escaped sequences`). Two spellings of the same string —
`"a"` and `"\x61"` — are therefore distinct literal types with empty
intersection, so equality narrowing types a runtime-reachable branch
`never`.

## Minimal reproduction (self-contained)

Reproduction: [`repros/string-escapes-injectivity.ts`](repros/string-escapes-injectivity.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/string-escapes-injectivity.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS at `9108f339`: **exit 0**; only a warning (SKJS2074 "comparison is
  always false") — which is itself wrong, since the comparison is true at
  runtime.
- node: prints `true branch, z = a typeof: string` — the string `"a"`
  inhabits `z: 0`.
- tsc `--strict`: rejects, `TS2322: Type '"a"' is not assignable to type
  '0'` (tsc decodes the escape and narrows the true branch to `"a"`).

Completeness dual (same root cause): with `x: "\x61" | 0` and the test
`x === "a"`, SKJS spuriously rejects the else-branch assignment that tsc
accepts.

## Second manifestation: falsiness (L-LIT(iii)), via line continuation

A LineContinuation (backslash + line terminator) has ECMAScript string
value `""` (empty). Its lexeme is non-empty, so `isFalsy` (`lexeme == ""`,
`TType.sk`) classifies the literal type *truthy* — the opposite of its
runtime falsiness. Witnessed end-to-end at the pin: a union of a
line-continuation string literal type with `0` is accepted where the
`else` of `if (x)` requires `x : 0`, while that branch runs at `x = ""`;
the canonical `"" | 0` control is correctly rejected (two falsy members).
This is distinct from the `\x61` injectivity case above (L-LIT(ii)): here
the escape corrupts *falsiness* classification (L-LIT(iii)). Same fix
(decode escapes/continuations when constructing string literal types).

Reproduction: [`repros/string-continuation-falsiness.ts`](repros/string-continuation-falsiness.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/string-continuation-falsiness.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

## Root cause

`src/ParserUtils.sk:38-39` — `unquoteString` strips quotes only; literal
types compare by raw lexeme (`src/PrimLiterals.sk`).

## Relation to existing issues/PRs

#655 tracks the same raw-lexeme problem for numeric and bigint literal types;
its body is explicitly about numeric/bigint normalization and truthiness, not
string escape decoding. `tests/expect-error/equality.ts` has a numeric spelling
FIXME (`1e3` versus `1000`) for that family, but local test search found no
string-escape counterpart. #156 is only about quote choice and literal
widening, not escape decoding. Not previously tracked.

## Suggested fix

Decode escape sequences when constructing string literal types (part of the
canonicalization design in deep dive G, which specifies canonical forms per
literal kind).

## Provenance

Deep dive G (`docs/deep-dives/literal-canonicalization.tex`, the
string-escapes finding); witnessed end-to-end. Main-paper assumption row: L-LIT(ii)
(injectivity — the string-kind instance).
