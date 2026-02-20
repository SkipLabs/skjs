# Writing Code

## Implementation Language

SKJS is implemented in **Skip** (`.sk` files in `src/`). The TypeScript files (`.ts`) in this repo are user programs that SKJS type-checks — they are not part of the implementation.

## TypeScript Subset Rules

[skjs-rules.md](../skjs-rules.md) is the definitive spec of the supported TypeScript subset. Examples and user programs should follow these rules; tests intentionally exercise and violate them to verify error reporting. Key points:

- No top-level `let`; use functions or classes
- All function parameters need explicit type annotations; named functions need return types
- No `any` type — use specific types, unions, or generics
- Discriminated unions must use `kind` as the discriminator field
- Only `console.log`, `console.assert`, and `console.error` are available
- Imports must be relative (`./` or `../`) with `.js` extension in node16/nodenext mode

## Keeping Docs in Sync

When changing the TypeScript support surface (new restrictions, lifted gaps, workarounds), update `skjs-rules.md` in the same commit or PR so the documented subset matches reality.
