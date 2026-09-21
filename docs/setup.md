# Setup

One-time steps to get a working development environment.

## Prerequisites

- The [Skip repository](https://github.com/SkipLabs/skip) checked out as a sibling directory (`../skip`)

## Git Hooks

Run once to set up automatic formatting checks on commit:

```bash
make setup-git-hooks
```

## Docker compiler and sibling standard library

`make build-in-docker` uses a compiler from `DOCKER_IMAGE` and the standard
library source from `SKIP_DIR` (default: `../skip`). These must be compatible.
An error while compiling `std` can therefore be a toolchain mismatch even when
both repositories have clean working trees.

Use the ignored `Makefile.local` for checkout-specific settings. Define variables
with `?=` so environment and command-line overrides still take precedence:

```make
DOCKER_IMAGE?=skiplabs/skip@sha256:d922830461016494d14ef2839e440c2a714f48f4dfaeceda115c408ed6c0c7fe
# Set SKIP_DIR here too if Skip is not a sibling checkout.
```

This image is the tested A3 toolchain (`70511b0832ff`), paired locally with Skip
`cb030b5ac`. On 21 September 2026, the locally installed `skiplabs/skip:latest`
(`5b9908726f0b`) rejected that standard library's longstanding
`private native fun .open_file` declaration. Selecting the tested compiler fixes
that local mismatch; it does not repair or update the newer compiler/library pair.
Do not remove `private` from library declarations or retag `latest` as a workaround.

When switching compiler images, first run `make clean-in-docker`: the compilers
may use incompatible `target/` cache formats (`static_state.db`). This removes
generated build files, not sources. Then run the ordinary commands:

```sh
make build-in-docker
make test-in-docker
make verify-census
```

Make exports the selected image and Skip path to its verification recipes too.
Direct commands such as `verification/run.sh` or `node verification/examples.mts`
do not read `Makefile.local`; provide `DOCKER_IMAGE` and `SKIP_DIR` in their
environment when invoking them directly. CI retains its own toolchain settings.

`Makefile.local` is not committed. For a new checkout, recreate the setting above
or supply `DOCKER_IMAGE=...` on the command line. Verify a different compiler and
standard-library pair before changing the local selection.
