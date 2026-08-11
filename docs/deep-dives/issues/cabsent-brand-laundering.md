# Unsound: a callable laundered through `{}` into a class-instance type is narrowed away by `typeof x === "function"`

Proposed labels: `soundness`, `bug`, `narrowing`.

## Summary

Callability is a four-point lattice (`CPresent ≤ CFunction ≤ CUnknown`,
`CAbsent ≤ CUnknown`). Subtyping deliberately accepts two lax steps:
`(CPresent, CUnknown)` — a callable is a subtype of `{}` (TS structural
assignability) — and `(CUnknown, CAbsent)` — `{}` flows into a
class-instance type, whose call mode is the `CAbsent` brand. Composed, a
callable launders `Function -> {} -> C` in two individually-accepted
steps. Refinement then trusts the brand as a proof of non-callability:
the `typeof x === "function"` true branch drops `CAbsent` branches, so a
binding that holds a function at runtime is narrowed to `never` in the
branch the runtime takes.

The brand is trustworthy only for values *constructed* at class-instance
types; subtyping's lax `(CUnknown, CAbsent)` arm admits values that
falsify it. The same trust model — refinement narrowing on a brand that
subtyping never validates — is deep dive D's finding F-BRAND (the array
brand); this is its callability instance.

## Minimal reproduction (self-contained)

Reproduction: [`repros/cabsent-brand-laundering.ts`](repros/cabsent-brand-laundering.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/cabsent-brand-laundering.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS: **exit 0, zero diagnostics**.
- node: the branch is taken and prints a function value at type `never`.
- tsc `--strict` (7.0.2): rejects, `TS2322: Type 'Function' is not
  assignable to type 'never'` — the unsoundness is SKJS-specific.

## Root cause

`TFields::isSubCallability` accepts `(_, CUnknown)` (structural `{}`
admits callables) and, separately, `(CUnknown, CAbsent)` — the code
comment documents the laundering route as a known cost of TS structural
assignability (`src/TTypeSubtyping.sk`, `isSubCallability`, the
`CAbsent` arm). Class-instance types carry `call = CAbsent`
(`src/TEnv.sk`, instance-type construction), and
`narrowByTypeofFunction` drops `CAbsent` branches in the `"function"`
true case (`src/TType.sk`).

## Relation to existing issues/PRs

The direct-constructor and subtyping-arm symptoms of the former
`call = None` representation were fixed by the `Callability` lattice
(#774 and the tri-state refactor); this witness survives that fix on the
brand path. Not previously tracked.

## Suggested fix

Either close the laundering arm — reject `(CUnknown, CAbsent)` when the
left side is not itself `CAbsent` (at the price of TS parity on
`{} -> C` assignability) — or downgrade refinement's trust: treat
`CAbsent` under `typeof "function"` as droppable only for types whose
values are all class-constructed (nominal instances with no structural
admission route), mirroring whatever resolution F-BRAND's array-brand
trust gets.

## Provenance

Deep dive D (`docs/deep-dives/subtyping-validation.tex`), the
callability-arm audit; refinement side in deep dive A
(`docs/deep-dives/runtime-grounding.tex`). Adversarially verified with
runtime execution 2026-08-06.
