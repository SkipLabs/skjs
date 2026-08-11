# Unsound: same-named type aliases from different modules collide in the expansion cache

Proposed labels: `soundness`, `bug`, `types`.

## Summary

The expansion cache (`subst.seenExpansion`) is keyed by `ExpansionKey` —
bare name text plus type arguments — not by resolved definition. Name
resolution itself is per-module and correct (diagnostics prove each
reference resolves to its own module's definition), but the cache
conflates two *different* definitions that share a name text and argument
list: whichever expands first under a substitution fills the entry, and
every later mention of the *other* definition reuses it. Zero-argument
aliases are the compounding case (`ExpansionKey("Box", [])` for both).

Both failure directions are observable in one program shape:

- **Unsound acceptance**: the local alias expands first; a call into the
  imported module then checks its argument against the local body. A
  `{ n: number }` value flows into a `{ s: string }` parameter; at
  runtime the callee reads `b.s === undefined` at static type `string`.
- **False rejection** (order reversed): the imported alias expands
  first; the local declaration is then rejected against the *imported*
  body, with the diagnostic pointing at the other module's definition —
  the position in the error is the imported module's, proving the cached
  entry crossed definitions.

The implementation comment on `ExpansionKey` acknowledges the missing
module qualifier but claims the collision is "not yet triggerable"
(upstream #889); both witnesses refute that.

## Minimal reproduction (self-contained pair)

Reproduction: [`repros/expansion-key-collision/`](repros/expansion-key-collision/)
(`main.ts` + `dep.ts`; a multi-file witness — the two same-named aliases
must live in different modules). Run
`make check-file-in-docker FILE=docs/deep-dives/issues/repros/expansion-key-collision BIN=target/host/dev/skjs`
(the directory argument checks both files together; expect: **accepted**
at the pin).

- SKJS: **exit 0, zero diagnostics**.
- node: compile the pair first, then run the emitted JavaScript
  (`npx tsc docs/deep-dives/issues/repros/expansion-key-collision/*.ts`
  despite the expected tsc error, then `node .../main.js`): prints
  `undefined` — a `string`-typed call result is `undefined`. (`main.ts`
  imports `./dep.js`, the emitted-file specifier, so direct
  strip-types execution of the `.ts` pair is not the supported route.)
- tsc `--strict`: rejects the call — the local `Box` (`{ n: number }`)
  is not assignable to `dep.ts`'s `Box` (`{ s: string }`), reported as
  a missing property `s`. Exact message and code vary by tsc version;
  the asserted fact is the rejected relationship between the two
  same-named definitions.

Controls, both verified at the pin:

- Renaming the local alias (`Box` → `Box2`, no collision) makes SKJS
  reject the same flow: `The field 's' is missing`.
- Reordering so the imported alias expands first (call the imported
  function before declaring a local `Box` value) yields the dual false
  rejection: `const b: Box = { n: 1 }` is rejected as
  `not assignable to type '{ s: string; }'` with the diagnostic anchored
  at `dep.ts`'s definition.

## Root cause

`ExpansionKey(name: String, targs: TArgs)` uses `name.value` — the
unqualified name text (`src/TType.sk`, `ExpansionKey` /
`expansionCacheKey`). Both expansion sites share the one map:
`TType::expandToVectors` (`src/TType.sk`, the `TSInst` arm) and
`growTVars`'s `collectTVars` (`src/TTypeSubtyping.sk`). A single
substitution spans checking a statement sequence that mentions both
definitions, so the entry filled for one serves the other.

## Relation to existing issues/PRs

Upstream #889 tracks adding a module qualifier to the key; the code
comment there considers the collision not yet triggerable. Not
previously witnessed.

## Suggested fix

Key the cache by definition identity, not spelling: include the
defining module (or a definition id from the defMap) in `ExpansionKey`
— the same identity `instantiate`'s recursion guard should use. Any
interim mitigation that clears `seenExpansion` at module boundaries
repairs only cross-file checking orders, not mixed statement sequences,
and is not recommended as a fix.

## Provenance

Deep dive C (`docs/deep-dives/type-expansion.tex`), the cache-exactness
audit at the pin; adversarially verified with runtime execution
2026-08-06. Registry row: E-EXPKEY.
