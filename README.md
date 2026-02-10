# skjs

SKJS is a typechecker for a dialect of TypeScript that reject programs that would fail at runtime for type reasons and restricts the type system to tractable constructs (see `skjs-rules.md`).

## Building & Testing

Requires the [Skip repository](https://github.com/SkipLabs/skip) checked out as a sibling directory (`../skip`).

```bash
# Build (produces ./target/host/dev/skjs)
docker run --rm -v "$(pwd):/work/skjs" -v "$(pwd)/../skip:/work/skip" -w /work/skjs skiplabs/skip:latest skargo build

# Run all tests
docker run --rm -v "$(pwd):/work/skjs" -v "$(pwd)/../skip:/work/skip" -w /work/skjs skiplabs/skip:latest skargo test

# Check a specific TypeScript file (builds if needed)
docker run --rm -v "$(pwd):/work/skjs" -v "$(pwd)/../skip:/work/skip" -w /work/skjs skiplabs/skip:latest skargo run -- check --import-stubs import-stubs <file>
```

## Documentation

See `skjs --help`

## Hacking

See `CONTRIBUTING.md`
