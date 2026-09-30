# Unsound: a getter `get p()` is typed as a method, so `c.p()` type-checks and throws

Proposed labels: `soundness`, `bug`. Priority: medium (needs an accessor
member; SKJS-specific — tsc rejects).

## Summary

SKJS types a class/object getter `get p(): T` as a **method** `p(): T` (a
call signature), not as a property of type `T`. The parser records an
`isGetSet` marker on the member AST node, but the type checker never reads
it, so a getter — which is syntactically method-shaped — is checked as a
method. Setters are likewise typed as methods (and then rejected for
lacking a return type).

Consequence in the **call** direction: `c.p()` type-checks (a `() => T`
returns `T`), but at runtime `c.p` already invoked the getter and yields
the value, so `c.p()` calls a non-function and throws.

(The **read** direction, `const n: T = c.p`, is soundly *rejected* — a
method is not assignable to `T` — which is what the existing
`callgraph-unsupported/getter-calls.ts` pins. Only the call direction is
unsound, and it is untracked.)

## Reproduction

Reproduction: [`repros/getter-typed-as-method.ts`](repros/getter-typed-as-method.ts)
— run `make check-file-in-docker
FILE=docs/deep-dives/issues/repros/getter-typed-as-method.ts
BIN=target/host/dev/skjs` (expect: **accepted** at the pin).

- SKJS: exit 0, zero diagnostics.
- Node: `TypeError: c.p is not a function`.
- tsc `--strict`: rejects (TS6234, expression is not callable).

## Root cause

The accessor marker `isGetSet` (`FGet`/`FSet`) is produced by the parser
(`src/ParserDefs.sk:194-245`, `src/ParserExpr.sk:549-564`,
`src/ParserType.sk:487-527`) and stored on the member AST node
(`src/Ast.sk:146`), but **no type-checker code consults it** — the member
is checked as a `ClassFieldMethod`, i.e. a method with a call signature.
The generic non-callable-value error (`TypeCheckExpr.sk:1815`) is exactly
what SKJS fails to raise for `c.p()`.

## Relation to existing material

- Known only as a **callgraph** gap: `tests/callgraph-unsupported/getter-calls.ts:1`
  and `setter-calls.ts:1` carry `// FIXME: missing callgraph edge for
  getter access (getter treated as method)`. Neither frames it as a
  type-soundness bug, and neither exercises `c.p()`.
- Distinct from row `L-GETSET` and deep dive F's "accessor caveat", which
  concern re-widening / get-set coherence of *fields*, not method-typing
  of accessor members.

## Suggested fix

Have the class/object/type-literal member typing consult `isGetSet`: type
a getter member as a field with get-type `T` (and `set = bottom` unless a
setter is present), a setter as a field with set-type and no call
signature. Then `c.p` is a value of type `T` (narrowable), `c.p()` is
correctly rejected, and the read direction still holds.
