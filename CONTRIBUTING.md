# Contributors Guide

- SKJS is written in the Skip language.
- When changing the TypeScript support surface, update [skjs-rules.md](skjs-rules.md) in the same patch so the documented subset matches reality (include new restrictions, lifted gaps, and workarounds).
- Tests live under `tests/` (unit-style `.ts` suites) and `examples/src/` (runnable programs). Add or adjust tests whenever diagnostics, typing rules, or code generation changes—`skargo test` must stay green.
- For intentional rejections, prefer `tests/expect-error/*.ts` with `// @ts-expect-error` (for errors TypeScript would produce too) or `// @skjs-expect-error` (for errors only SKJS produces) annotations so regressions are caught automatically.
- Remember that SKJS is a typechecker and will not run code, hence tests must exercise the typechecker, not the runtime (calling `console.log` or test functions is useless)
- Commits in this repository must respect the following rules:
  - each commit should pass formatting (`make fmt`), run `make setup-git-hooks` once to ensure this;
  - each commit should pass tests (`skargo test`);
  - the message should start with `AIGEN` if the code has been produced with the help on an AI.
