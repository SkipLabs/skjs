# Generated examples

A **frozen corpus of real-world TypeScript** that SKJS is run against as an
acceptance suite. Each subdirectory is a complete [Skip Runtime](https://skiplabs.io)
service — `package.json`, `tsconfig.json`, `helpers/index.d.ts`, and a `src/`
tree of resources, mappers, reducers, and types — one project per generator
benchmark (`counter`, `blog-post`, `chat-room`, …). There are 38 projects
(~650 files).

## Where it comes from

The code is emitted **verbatim** by SkipLabs' _skipper_ code generator. Nothing
here is hand-written or hand-edited — the point of the corpus is that it is
_exactly what the generator produces_, so it exercises SKJS against idiomatic,
machine-generated TypeScript at scale rather than against curated examples (for
those, see [`examples/`](../examples/)).

## Regenerating (SkipLabs-internal)

Regeneration is **not reproducible outside SkipLabs**: it requires the private
skipper repository, a paid `SKIPPER_API_KEY` (generation is AI-driven and
billed), and `bun`. It is also non-deterministic — each run yields a _fresh_
corpus that will not byte-match the committed files; the contract is "genuine
generator output that SKJS accepts", not reproduction of specific files. See
[`scripts/regenerate-generated-examples.sh`](../scripts/regenerate-generated-examples.sh)
for the internal procedure. **External contributors are not expected to
regenerate this corpus.**

## Checking it locally (public)

_Verifying_ the corpus, unlike regenerating it, needs only a built `skjs` and
`node` — no skipper access. It runs each project through both `tsc --noEmit` and
`skjs check`:

```bash
./scripts/check-generated-examples.sh
```

See [`scripts/check-generated-examples.sh`](../scripts/check-generated-examples.sh)
for options.
