# AGENTS.md

- SKJS is implemented in **Skip** (files ending in `.sk`) but it is a **TypeScript type checker**; treat `.ts` files as user programs that must conform to the SKJS subset of TypeScript.

- The accepted TypeScript subset, supported workarounds, and intentional gaps are documented in [skjs-rules.md](skjs-rules.md); never generate patches that contradict those rules.
- Never emit or accept **top-level** `const` declarations that destructure (`const {x} = ...` or `const [a] = ...` at module scope): SKJS loads top-level constants as literal scalars only, so bind to a simple `const tmp = ...` and destructure inside a block/function instead.

## Running Tests

Use the standard Skip Docker container to run tests (only Linux is supported for compilation).

**Prerequisites:** The [Skip repository](https://github.com/SkipLabs/skip) must be checked out as a sibling directory (`../skip`).

```bash
# Build SKJS (produces ./target/host/dev/skjs)
docker run --rm -v "$(pwd):/work/skjs" -v "$(pwd)/../skip:/work/skip" -w /work/skjs skiplabs/skip:latest skargo build

# Run all tests
docker run --rm -v "$(pwd):/work/skjs" -v "$(pwd)/../skip:/work/skip" -w /work/skjs skiplabs/skip:latest skargo test

# Check a specific TypeScript file with skjs (build first if needed)
docker run --rm -v "$(pwd):/work/skjs" -v "$(pwd)/../skip:/work/skip" -w /work/skjs skiplabs/skip:latest ./target/host/dev/skjs check --import-stubs import-stubs <file>
```
