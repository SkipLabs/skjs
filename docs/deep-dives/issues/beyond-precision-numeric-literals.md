# Unsound: beyond-precision numeric literals — spellings of one double narrow to `never`, and a normalized underflow lexeme is classified truthy

Proposed labels: `soundness`, `bug`, `narrowing`.

## Summary

Numeric literals that fail the round-trip `String(Number(s)) = s` —
16–17-digit decimals, radix forms above 2^53, over/underflow exponent
forms — are stored as distinct lexemes even when they denote the *same*
double, and they are never merged. Never-merging keeps subsumption sound
but is precisely the unsound direction wherever an empty lexeme
intersection is read as *disjointness*: `===` narrowing between two
spellings of one double types a live branch `never`. A second
manifestation hits falsiness: the normalizer rewrites a longhand
10^-400 decimal to the lexeme `1e-400`, whose IEEE value underflows to
+0 — falsy at runtime, classified truthy by the lexeme test `isFalsy`.

## Minimal reproduction (self-contained)

Reproduction: [`repros/beyond-precision-spurious-never.ts`](repros/beyond-precision-spurious-never.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/beyond-precision-spurious-never.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

```ts
function t(x: 9007199254740993 | "q", y: 9007199254740992 | "r"): void {
  if (x === y) {          // true at runtime: both literals are 2^53
    const z: never = x;   // ACCEPTED — spurious never
    const s: string = z;  // a number flows into string
    console.log(s);
  }
}
t(9007199254740993, 9007199254740992);
```

- SKJS: **exit 0, zero diagnostics** (including the call, which makes
  the branch live).
- node: the branch runs and prints `9007199254740992` — a number
  inhabits `never` and flows into a `string` binding.
- tsc `--strict`: rejects (`TS2322`, both literals are the type
  `9007199254740992`, so `x` narrows to it, not to `never`).

The same shape reproduces with `0x20000000000001` vs `9007199254740993`
(hex/decimal of one value) and with `1e309` vs `2e309` (both
`Infinity`).

## Second manifestation: falsiness, via exponent underflow

Reproduction: [`repros/underflow-zero-truthy.ts`](repros/underflow-zero-truthy.ts) — run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/underflow-zero-truthy.ts BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

A longhand decimal `0.(399 zeros)1` (value 10^-400, i.e. the double +0)
is normalized to the lexeme `"1e-400"`; `isFalsy` (`lexeme == "0"`)
reads it truthy. With `x: 10^-400-longhand | ""`, safe mode accepts
`if (x)` (one falsy member) and the else branch narrows to `""` — while
at runtime `x` holds +0 and takes the else branch: `const z: "" = x`
holds the number `0`. This falsifies the `isFalsy` comment that
beyond-precision literals "can never be zero" (`src/TType.sk:1346-1347`).

## Root cause

Parse-time normalization (`normalizeJSNumber`) is exact only within
precision: its fast path keeps any ≤21-digit decimal that passes
`isJSNumericString` (`src/JSNumericString.sk:499`), and the slow path
rewrites over/underflow exponent forms (`1e309 → "1e+309"`, longhand
10^-400 → `"1e-400"`) rather than folding them to their double's
canonical rendering. Distinct stored lexemes are treated as distinct
literal types by `PrimLiterals::inter` (lexeme-set intersection), and
the narrowing/intersection path (`TypeCheckRefine.sk`, `TTypeInter.sk`,
`PrimLiterals.sk`) carries **no precision guard**. The comparison *lint*
already knows the runtime truth — `checkComparisonOverlap` is silenced
for imprecise operands by `hasImpreciseNumberLiteral`
(`src/TypeCheckExpr.sk:1448-1458`), its comment citing
`9007199254740993 === 9007199254740992` — so the checker suppresses the
warning and still performs the unsound narrowing.

## Relation to existing issues/PRs

- #655 (normalize numeric/bigint literal types instead of comparing raw
  source lexemes): covers the within-precision spellings, whose
  parse-time normalization landed; this issue is the beyond-precision
  residue that normalization deliberately left non-canonical.
- `tests/expect-error/number-literal-precision.ts` pins the never-merge
  behavior and its header calls it "sound, but … stricter than tsc";
  the witnesses above falsify that rationale — the header (and the
  `isFalsy` comment) need updating with whatever fix lands.
- `isPreciseJSNumberLiteral` (`src/JSNumericString.sk:87`) already
  classifies exactly the problematic lexemes, and documents the
  collisions honestly.

## Suggested fix

Either direction restores soundness; the first also restores tsc parity:

1. **Normalize beyond-precision literals to their double's canonical
   rendering** (`String(Number(s))`: `9007199254740993 → "9007199254740992"`,
   `1e309 → "Infinity"`, underflow forms → `"0"`), making literal-type
   identity value identity everywhere (tsc's semantics). `Infinity` as a
   stored lexeme needs an `isFalsy`/rendering audit.
2. **Make narrowing and intersection precision-aware exactly like the
   lint**: treat any pair involving an imprecise lexeme
   (`isPreciseJSNumberLiteral` false) as *overlapping* (no branch drop,
   no `never`), and make `isFalsy` recognize underflow-to-zero
   renderings (or normalize them to `"0"` at mint time).
