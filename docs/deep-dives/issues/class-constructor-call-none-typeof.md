# Unsound: class-constructor values are typed with no call signature, so `typeof x === "function"` narrows them away

Proposed labels: `soundness`, `bug`, `narrowing`.

## Summary

A class-constructor *value* (`const F = C`) gets an object type whose call
mode is `None` — which refinement reads as "definitely not callable". But
class constructors implement `[[Call]]` (`typeof C === "function"` in JS), so
the `typeof x === "function"` true branch, which drops `call = None`
branches, drops the constructor — typing the branch as if it cannot contain
`F` while the runtime takes it.

This is one symptom of a representation-level dichotomy: subtyping's
`isSubOptTFuns` `(_, None())` arm reads `None` as "callability unknown"
(accepting callable ≤ `{}`), refinement reads it as "definitely not
callable"; no single reading validates both (deep dive D, finding F-CALL).
A fix here should decide the representation, not just patch this witness.

## Minimal reproduction (self-contained)

Reproduction: [`repros/constructor-typeof-function.ts`](repros/constructor-typeof-function.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/constructor-typeof-function.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS at `9108f339`: **exit 0, zero diagnostics**.
- node: prints `[class C]` — a function typed as returning `string` returns
  the class-constructor object.
- tsc `--strict`: rejects, `TS2322: Type 'typeof C' is not assignable to
  type 'string'`.

## Root cause

`newStaticObject` builds constructor-value object types with
`call = None()` (definitely-not-callable per the refinement reading);
`evalTypeofEquality`'s `"function"` case drops such branches
(`src/TypeCheckRefine.sk:286-299`).

## Relation to existing issues/PRs

Checked: #273 (closed, instance-side typeof), #311/PR #412, #684/#695,
#697/PR #702, #698/PR #703, #699/PR #706; `tests/expect-error/typeof.ts`
covers `typeof x === "function"` for plain functions and callable object
types, but not class-constructor values stored in locals. The constructor
value-space issues above cover whether names can be used as values or
constructors; they do not cover `typeof` refinement dropping an existing
constructor value. Not previously tracked.

## Subtyping-arm facet (F-CALL), witnessed

The same `call = None` dichotomy has a subtyping-side witness independent of
the constructor path: `isSubOptTFuns` accepts `(Some(sig), None)`, so a
callable is a subtype of `{}`; `typeof o === "function"` then drops the
`call = None` branch and narrows `o` to `never`.

Reproduction: [`repros/fcall-subtyping-arm.ts`](repros/fcall-subtyping-arm.ts)
— run `make check-file-in-docker
FILE=docs/deep-dives/issues/repros/fcall-subtyping-arm.ts
BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

## Suggested fix

Give constructor values a definite call/new mode consistent with ECMAScript
(constructible ⟹ callable), or introduce a genuine third "unknown
callability" state so subtyping and refinement can both be right — see the
`call = None` dichotomy (deep dives A finding 8 and D finding F-CALL).

## Provenance

Deep dives A (`docs/deep-dives/runtime-grounding.tex`) and D
(`docs/deep-dives/subtyping-validation.tex`); adversarially verified with
runtime execution 2026-07-05. Main-paper definition affected: Signature
Modes (`None` = definitely not callable).
