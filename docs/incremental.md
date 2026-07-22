# Incremental checking

SKJS is incremental: after an initial run it re-analyses only the files affected
by a change, so re-checks are faster than checking from scratch. This is backed
by a persistent on-disk cache.

## Priming the cache

Initialize a cache directory with `--init`. This runs a full check and writes the
analysis state to the directory you name:

```bash
skjs check --init .skjs-cache --import-stubs ./import-stubs
```

## Re-checking incrementally

On later runs, point at the same cache with `--data`. SKJS reuses the cached
analysis and only re-checks what your edits affected:

```bash
skjs check --data .skjs-cache --import-stubs ./import-stubs
```

## Seeing what a change affected

With a primed cache, `--log-affected-files` prints (to stdout) the files a change
touched, without re-checking the whole project. It requires `--data`:

```bash
skjs check --data .skjs-cache --log-affected-files --import-stubs ./import-stubs
```
