# AGENTS.md

- SKJS is implemented in **Skip** (files ending in `.sk`) but it is a **TypeScript type checker**; treat `.ts` files as user programs that must conform to the SKJS subset of TypeScript.

- The accepted TypeScript subset, supported workarounds, and intentional gaps are documented in [skjs-rules.md](skjs-rules.md); never generate patches that contradict those rules.
- Never emit or accept **top-level** `const` declarations that destructure (`const {x} = ...` or `const [a] = ...` at module scope): SKJS loads top-level constants as literal scalars only, so bind to a simple `const tmp = ...` and destructure inside a block/function instead.
