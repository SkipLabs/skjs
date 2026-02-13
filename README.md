# skjs

SKJS is a typechecker for a dialect of TypeScript that reject programs that would fail at runtime for type reasons and restricts the type system to tractable constructs (see `skjs-rules.md`).

## Building & Testing

Requires the [Skip repository](https://github.com/SkipLabs/skip) checked out as a sibling directory (`../skip`).

```bash
make build-in-docker   # Build (produces ./target/host/dev/skjs)
make test-in-docker    # Run all tests
make check-in-docker   # Type-check without building
make clean-in-docker   # Clean build artifacts
```

## Documentation

See `skjs --help`

## Hacking

See `CONTRIBUTING.md`
