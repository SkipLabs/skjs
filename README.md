# skjs

SKJS is a typechecker for a dialect of TypeScript. Its goal is soundness — rejecting programs that would fail at runtime for type reasons — while restricting the type system to tractable constructs (see `skjs-rules.md`). Soundness is what SKJS aims for rather than a finished guarantee: some unsound programs are still accepted today, and known gaps are tracked as issues.

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
