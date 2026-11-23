# Releasing SKJS

How maintainers cut a release. If you just want to download and run a released
binary, see [binary-distribution.md](binary-distribution.md).

## Releasing a new version

1. Bump `version` in `Skargo.toml` (PRs are expected to do this — see [commits-and-prs.md](commits-and-prs.md)).
2. After the bump lands on `main`, tag and push:

   ```bash
   git tag v1.2.3
   git push origin v1.2.3
   ```

3. The release workflow runs and publishes to `https://github.com/SkipLabs/skjs/releases/tag/v1.2.3`.

The workflow fails fast if the tag (with `v` stripped) doesn't match `version` in `Skargo.toml`, so a mistagged release won't produce assets.

## CI overview

| Pipeline | When it runs | What it does |
| --- | --- | --- |
| CircleCI `build_and_test` | Every push to a branch | Runs the test suite |
| GitHub Actions `release.yml` | Every `v*` tag push | Builds, smoke-tests, and publishes the GitHub Release |

CircleCI no longer publishes any binaries — it's only used for testing on branch pushes.

Both test pipelines cache the dev binaries (`target/host/dev/{skjs,test}`) keyed on a content hash of their build inputs (sources, `build.sk`, transitive `../skip` path deps, toolchain — see `bin/ci_build_cache.sh`). On a hit, `make test` runs the prebuilt test binary directly (`SKJS_PREBUILT=1`) instead of rebuilding via `skargo test`, skipping the multi-minute compile. The cache is saved only after tests pass, and only under an exact key, so a restored binary always matches the current inputs.

### Skipping the expensive steps

The CircleCI job first classifies the branch's diff against `main` (see `bin/ci_classify_changes.sh`, unit-tested via `make check-sh`). A docs-only diff (`docs/`, root `*.md`, `LICENSE`) halts the job green immediately; an infra-only diff (only `bin/`, `.vibe/`, `.github/`, `scripts/`, `devtools/`, `npm/`, `Makefile`, …) still runs the cheap checks (`make check-fmt`, `make check-sh`) and then halts green before the Skip clone, the build and the tests. The job always reports green when it halts, so the required `ci/circleci: build` check stays satisfied and the PR stays mergeable. Anything else — or any uncertainty — gets the full clone + build + test (fail safe).

## Troubleshooting the release workflow

### Workflow fails on "Verify tag matches Skargo.toml version"

The tag's version (with `v` stripped) doesn't match `version` in `Skargo.toml`. Either bump `Skargo.toml` and push a new tag, or delete the bad tag and re-cut.

### Workflow fails with `MAP FAILED: Cannot allocate memory`

The runtime can't satisfy its mmap request on this runner. The job sets `SKIP_CAPACITY=8G` to cap the heap; lower it (e.g. `4G`) if needed.
