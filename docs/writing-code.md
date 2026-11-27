# Writing Code

## Implementation Language

SKJS is implemented in **Skip** (`.sk` files in `src/` and `src/absint/`). `.ts` files in this repo are user programs checked by SKJS, not implementation code.

## Skip Style

- **Non-linear control flow**: Make early returns, `continue`, and `break` visually prominent with explicit braced `if`/`else` blocks rather than flattening them.
- **Exhaustive pattern matches**: Enumerate variants explicitly rather than using a wildcard (`_`) catch-all, so adding a variant forces an explicit decision at every match site.
  - Two-arm matches (`| SomePattern -> ... | _ -> ...`) are fine when "match this shape, otherwise no-op" is genuinely safe for future variants.
  - Multi-arm matches with `_` are fragile — avoid unless unavoidable (e.g., tuple cross-products without nested or-patterns), and document why the default is safe for future variants.
- **Skip Code Notes**: Read [SkipLabs/skip `docs/skip-code-notes.md`](https://github.com/SkipLabs/skip/blob/main/docs/skip-code-notes.md) (`../skip/docs/skip-code-notes.md`) before writing `.sk` code; append Skip-writing lessons there in the Skip repo.

## Error Messages

Error messages are read by both agents and humans — keep them actionable:

- **Name the offending construct, say why it is rejected, and — when applicable — what to use instead.** Prefer `abstract classes are not supported by SKJS; use a concrete base class` over `Invalid class`.
- **Match `tsc`'s wording when rejecting the same thing `tsc` rejects**, including single-quoted type/identifier names (e.g. `Type 'number' is not assignable to type 'string'`). Verify with `npx tsc --strict --noEmit`.
- **Every diagnostic carries an error code**, in priority order:
  1. Matching TypeScript code (`TS2322`, …)
  2. ESLint / typescript-eslint rule name (`no-var`, `@typescript-eslint/strict-boolean-expressions`, …)
  3. `SKJS####` code (1xxx syntax, 2xxx semantic/type, 5xxx options, 9xxx not yet supported)
- **Sync on message changes**: Update test annotations (`UPDATE_EXPECT=2 make test-in-docker`, then review diff) and any quoted message in `skjs-rules.md` / `docs/error-format.md` in the same commit.

## TypeScript Subset & Keeping Docs in Sync

[skjs-rules.md](../skjs-rules.md) is the normative spec of the supported TypeScript subset (no top-level `let`, explicit function parameter and named-function return annotations, no `any`, minimal `console` surface, relative imports with `.js` in `node16`/`nodenext` mode, etc.).

When changing what SKJS accepts or rejects (restrictions, lifted gaps, soundness rules, workarounds), update `skjs-rules.md` (and `docs/typescript-soundness-holes.md` when closing or discovering a soundness hole) in the same commit or PR.
