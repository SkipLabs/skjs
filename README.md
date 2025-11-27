# skjs

SKJS is a typechecker for a dialect of TypeScript that reject programs that would fail at runtime for type reasons and restricts the type system to tractable constructs (see `skjs-rules.md`).

## Building

`skargo build` will produce `skjs` in `target/host/dev/`.

## Running

`skjs check --import-stubs import-stubs examples`

## Documentation

See `skjs --help`

## Hacking

See `CONTRIBUTING.md`
