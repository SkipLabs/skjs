# Contributors Guide

- When changing the TypeScript support surface, update [skjs-rules.md](skjs-rules.md) in the same patch so the documented subset matches reality (include new restrictions, lifted gaps, and workarounds).
- Tests live under `tests/` (unit-style `.ts` suites) and `examples/src/` (runnable programs). Add or adjust tests whenever diagnostics, typing rules, or code generation changes—`skargo test` must stay green.
- For intentional rejections, prefer `tests/expect-error/*.ts` with `// @ts-expect-error` annotations so regressions are caught automatically.
