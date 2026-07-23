# skjs

SKJS is a typechecker for a dialect of TypeScript. Its goal is soundness — rejecting programs that would fail at runtime for type reasons — while restricting the type system to tractable constructs (see `skjs-rules.md`). Soundness is what SKJS aims for rather than a finished guarantee: some unsound programs are still accepted today, and known gaps are tracked as issues.

## Incremental

SKJS is incremental: after the first run it re-analyses only the files affected by a change, so re-checks are faster than checking from scratch. Use `--init` to prime an on-disk cache and `--data` to reuse it — see [docs/incremental.md](docs/incremental.md).

## Quickstart

Grab a released binary, unpack the bundled type stubs, and check a file:

```bash
# Download the latest linux/amd64 build + type stubs
gh release download --repo SkipLabs/skjs \
  --pattern 'skjs_*_linux_amd64' --pattern 'import-stubs.tgz'
chmod +x skjs_*_linux_amd64
mkdir import-stubs && tar -xzf import-stubs.tgz -C import-stubs

# Check a TypeScript file
./skjs_*_linux_amd64 check --import-stubs ./import-stubs path/to/file.ts
```

See [docs/binary-distribution.md](docs/binary-distribution.md) for arm64 builds, checksums, and other install details.

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
