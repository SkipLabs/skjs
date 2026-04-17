# Writing Code

## Implementation Language

SKJS is implemented in **Skip** (`.sk` files in `src/`). The TypeScript files (`.ts`) in this repo are user programs that SKJS type-checks — they are not part of the implementation.

## Coding Style

**Non-linear control flow:** Early returns, `continue`, and `break` are bug farms. When a function has early returns, or a loop has `continue` or `break`, make them visually prominent by using explicit if/else blocks with braces rather than flattening them. This makes the non-linear control flow obvious to readers.

**Exhaustive pattern matches:** Prefer exhaustive pattern matches wherever possible. Enumerate all variants explicitly rather than using a wildcard (`_`) catch-all, so that adding a new variant to the matched type triggers an exhaustiveness error and forces an explicit decision at every match site. Use a wildcard only when the default behavior is genuinely correct for any future variant, and document why.

Two-arm matches of the form `| SomePattern -> ... | _ -> ...` are acceptable: the "do the thing for exactly this shape, otherwise nothing" idiom is low-risk because a new variant lands in the safe no-op bucket. The fragility concern is specifically about multi-arm matches with a wildcard, where a new variant silently falls into whichever bucket the wildcard shared — and that bucket wasn't designed for it.

Exhaustive matching is sometimes impractical because Skip does not support nested or-patterns. This typically arises when matching on a tuple of variant types: the cross-product of cases is large, but most combinations collapse to the same result, and without or-patterns they cannot be grouped. In those cases a wildcard is unavoidable; document why the default is correct for any future combination.

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
