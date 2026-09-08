# Direct closure-proof construction: measured effects

Measured on 2026-09-08, macOS 26.3.1, arm64. These are measurements of the
current small closure fixture, not a claim about arbitrary programs.

The baseline is the uncommitted straight-line closure implementation following
`a2a5e5c1`, including source-guided intermediate-type search. Its executable was
saved before this change. Binary and input SHA-256 hashes and every measured
sample are in [direct-proof.json](direct-proof.json).

## Method

Frozen parser output and real SKJS claims for
[closures.ts](../tests/stateful-source/closures.ts), identical across variants.
Each row selects one independent function, except “All nine,” which retains the
whole file. One warm-up, then five sequential runs per case and binary; medians
reported below. No builds or other benchmark variants ran concurrently.

Production timing includes process startup, source/claim decoding, extraction,
proof production, the producer's independent validation, and certificate output.
It excludes Lean compilation, TypeScript parsing and SKJS claim export.
Consumer timing is a separate process reading the generated certificate.
Every positive run had to produce and independently check successfully. The
negative run had to reject an annotation claiming `true` for a `false` local.

The baseline was rerun after the candidate and component measurements: medians
were 2.072 s for all nine functions and 0.823 s for `localBlock`, agreeing with
the original measurements below.

## Results

| Case | Before | Direct construction + reuse | Speedup |
| --- | ---: | ---: | ---: |
| Captured reader | 0.177 s | 0.072 s | 2.5× |
| Assignment body | 0.321 s | 0.046 s | 6.9× |
| Closure calling a closure | 0.282 s | 0.072 s | 3.9× |
| Single-return block | 0.204 s | 0.072 s | 2.8× |
| Block with allocation, local, write and read | 0.823 s | 0.050 s | 16.3× |
| All nine functions | 2.074 s | 0.289 s | 7.2× |
| Wrong local annotation: rejection | 0.025 s | 0.025 s | unchanged |

Two changes contribute. The following component measurement retains the old
source-guided search for the graph certificate while constructing supplemental
proofs directly:

| Configuration | Local block | All nine |
| --- | ---: | ---: |
| Original guided search | 0.823 s | 2.074 s |
| Direct supplemental proofs; graph still searched | 0.135 s | 0.594 s |
| Direct proofs reused by exact root judgment | 0.050 s | 0.289 s |

For all nine functions, consumer time was 0.026 s before and 0.024 s after:
roughly unchanged at this scale, with process startup included. The evidence
file grew from 114,499 to 116,740 bytes (+2.0%). The assignment-body certificate
grew by 14%, while the local-block certificate grew by 0.1%. Fixing intermediate
types can yield different valid proofs and additional explicit coercions; this
change does not promise smaller certificates.

Both binaries checked each other's certificates on all six positive cases
(12 successful cross-consumer checks). The calculus, consumer rules and wire
protocol did not change. Source extraction's existing graph-equality and
execution regressions remain in force. Forged recipes and reused proofs are
checked by the ordinary consumer, and corrupt composite write claims now also
have a producer-rejection regression.

## Reproduce

Save the baseline executable before rebuilding. Generate and freeze the AST and
claims once using the normal parser/export commands. Run each binary separately:

```sh
python3 verification/tools/bench-closures.py \
  --binary /path/to/saved/verifier-before --name before \
  --ast /path/to/closures.ast.json --claims /path/to/closures.claims.json \
  --file-key verification/tests/stateful-source/closures.ts \
  --output-dir /tmp/closure-benchmark

python3 verification/tools/bench-closures.py \
  --binary verification/lean/.lake/build/bin/verifier --name after \
  --ast /path/to/closures.ast.json --claims /path/to/closures.claims.json \
  --file-key verification/tests/stateful-source/closures.ts \
  --output-dir /tmp/closure-benchmark
```

The script preserves per-case inputs, evidence and raw timings. `--cases all
localBlock` selects just the combined and larger single-function cases. The
component binary was built with direct supplemental proof construction retained
but the graph producer given the old sequent suggestions and no reusable proofs.
That measurement-only source change was then reverted.
