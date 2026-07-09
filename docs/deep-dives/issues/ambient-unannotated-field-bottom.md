# Unsound: an un-annotated field on an ambient class reads as `never` (bottom)

Proposed labels: `soundness`, `bug`. Priority: medium (bounded to ambient
declarations; behaves like an unsound `any`).

## Summary

An un-annotated field on an ambient (`declare`) class is given a placeholder
`TSInst` type. When that placeholder is head-expanded, `instantiate` returns
it unchanged (the missing-annotation early return), the identity is dropped by
the expansion worklist's seen-set dedup, and the field's type collapses to
**bottom**. Since `⊥` is a subtype of everything, a read of the field is
accepted into *any* target type — including `never`.

## Reproduction

Reproduction: [`repros/ambient-field-bottom-collapse.ts`](repros/ambient-field-bottom-collapse.ts)
— run `make check-file-in-docker
FILE=docs/deep-dives/issues/repros/ambient-field-bottom-collapse.ts
BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS at `9108f339`: exit 0. Reads `c.x` into both `string` and `never`.
- Writing `c.x = "hello"` is rejected ("not assignable to type
  `Missing_type_annotation_for_C_x`") — the write side keeps the placeholder
  opaque; only the **read** side collapses to `⊥`.
- tsc `--strict`: rejects at the declaration (TS7008, implicit any).

## Root cause

`instantiate` has two identity-returning paths; the missing-annotation
placeholder return (`TEnv.sk:122-124`) fires with `seenInstantiate` empty, at a
top-level `seenExpansion` cache-fill site. In `expandToVectors` (`TType.sk`)
the re-emitted identity equals the popped instance and is dropped by the seen
dedup, leaving empty clauses → `expand` yields `⊥`. This is the exact
bottom-collapse the E-GUARD obligation was meant to exclude, reached through a
sibling identity path the obligation's audit did not inventory.

## Relation to the corpus

Deep dive C, obligation E-GUARD (its recursion-guard scope is empirically
safe; this placeholder path is the realized violation). Registry row
`E-GUARD-PLACEHOLDER` (owner C, violated). Not the same as #655/string-escapes
(those are literal-lexeme bugs).

## Suggested fix

In `expandToVectors`, keep an identity `instantiate` result as a residual
instance (do not let the seen dedup drop it), or have the missing-annotation
return carry a top clause (`⊤`) so reads reject as intended rather than
collapsing to `⊥`.
