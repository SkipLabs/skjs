# Unsound: enum string-concat folding mints a member literal whose spelling is not the runtime string

Proposed labels: `soundness`, `bug`, `enums`.

## Summary

The enum constant folder concatenates string members from operand
*lexemes*: the `BOAddition` arms build `EFStr(a + b)` for
`(EFStr, EFStr)`, `(EFStr, EFNum)`, and `(EFNum, EFStr)`. The numeric
operand contributes its raw spelling, and — unlike numeric fold
*results*, which pass through the `enumNumOrUnknown` double-safe gate —
a direct numeric-literal operand is taken as-is. A beyond-precision
spelling therefore reaches the concat: `"x" + 1e-400` folds to the
member literal `"x1e-400"`, while at runtime `1e-400` underflows to `0`
before `ToString`, so the member's value is `"x0"`. The minted literal
type is inhabited by no run of the program, and the member's actual
value escapes its static type: an assignment at the wrong literal type
is accepted, `===` narrowing against the spelling takes branches that
never run, and a switch judged to cover the member's value set can drop
the path the runtime takes.

## Minimal reproduction (self-contained)

Reproduction: [`repros/enum-concat-imprecise-fold.ts`](repros/enum-concat-imprecise-fold.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/enum-concat-imprecise-fold.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS: **exit 0, zero diagnostics** — `E.A` is typed at the literal
  `"x1e-400"`.
- node (enum compiled by tsc): `E.A` evaluates to `"x0"`;
  `E.A === "x1e-400"` is `false`.
- tsc `--strict` (7.0.2): accepts the enum but types `E.A` as `E` —
  it mints no literal — and rejects the assignment,
  `TS2322: Type 'E' is not assignable to type '"x1e-400"'`. The
  unsoundness is SKJS-specific.

## Root cause

`enumFold`'s string-concat arms (`src/TypeCheckEnum.sk:439-457`) build
the folded lexeme by textual concatenation of operand lexemes. Numeric
fold results are gated by `enumNumOrUnknown` (double-safe range, exact
integer arithmetic), but a numeric *literal* operand enters via
`enumFoldOfMemberValue`/the expression fold with its stored spelling and
no precision check, so a spelling that is not `String(Number(spelling))`
— the beyond-precision range of `L-LIT` — is concatenated verbatim.

## Relation to existing issues/PRs

Adjacent to `beyond-precision-numeric-literals.md` (the same defective
spelling range), but a distinct producer: there the parser stores a
user-written spelling; here the folder *synthesizes* a new string
literal from one, converting a num-kind spelling defect into a
string-kind literal whose denotation is wrong. Not previously tracked.

## Suggested fix

Either fold the numeric operand through its value — concatenate
`String(Number(lexeme))`, matching runtime `ToString` — or
conservatively reject a string fold whose numeric operand fails the
round-trip predicate (`isPreciseJSNumberLiteral`). Note the numeric
route's widen-to-untracked philosophy does not transfer directly: the
representation has an untracked-*number* member but no untracked-string
analogue, and refusing the constant fold currently routes into the
computed-member path, which expects a number and may reject rather than
widen; adding an untracked-string member is a larger design change.

## Provenance

Deep dive G (`docs/deep-dives/literal-canonicalization.tex`), the enum
producer-inventory audit; registry row L-LIT-FOLD. Adversarially
verified with runtime execution 2026-08-07.
