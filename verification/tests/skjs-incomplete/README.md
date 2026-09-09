# SKJS incompleteness examples

Programs rejected by SKJS whose declared types are true. These are precision
gaps, not unsafe programs. In most of them the independent verifier establishes
the result after the producer’s claims are repaired; where it does not, the entry
below says so, since being rejected by a checker whose annotation holds is what
makes an example belong here, and what today’s rules can certify is a separate
fact.

`negated-loop-exit.ts` demonstrates incompleteness, not unsoundness. SKJS rejects
its `true` return annotation because it forgets the condition's false edge after
`while (!flag)`. The function returns true for both Boolean inputs: the loop body
returns true, and reaching the following return entails `flag = true`.

`negation.js` takes SKJS's normal-mode partial export (without `--keep-going`).
The original broad exit claim does not suffice under local verification. The test
independently checks an explicit repair of the final binding and expression to
true and rejects an incorrect false exit binding. No SKJS behavior is changed.

`singleton-negation.ts` is another producer precision gap: SKJS types `!flag` as
`boolean` even for `flag : true`. Changing just that expression claim to `false`
makes its declared `false` result independently verifiable. The `ifKnown` rule
checks the condition's singleton type before selecting the false-valued arm;
the test rejects the opposite claimed result. Normal partial collection suffices.

`null-loop-exit.ts` isolates the same issue for `while (value === null) { continue; }`.
For Boolean inputs the loop is skipped; null diverges. Reaching the return therefore
implies a Boolean value. SKJS rejects it. `null-tests.js` repairs the final entry
binding and returned-expression claim to `boolean`, independently checks the
certificate, and rejects an opposite null exit refinement. No keep-going export
or termination claim is involved.

`write-refined-read.ts` records a post-write precision gap. The function assigns
`true` to a Boolean cell and returns its current contents. It always returns true;
SKJS rejects the singleton result annotation, whereas TypeScript accepts it.
Normal first-error collection records the final read as `boolean`.

[WriteRefinedRead.lean](../../lean/Verification/ExperimentState/WriteRefinedRead.lean)
proves the modeled body safe at true and separately proves its terminating
execution. [Program typing](../../PROGRAM-TYPING.md#current-content-rules-semantic-layer)
documents the rules used by that proof.

The original broad return-entry claim does not verify locally: it forgets the
write's current-true fact. An explicit candidate with `{ value: boolean = true }`
at that entry verifies, even if the read's expression claim stays Boolean. The
incoming write edge justifies the observation and the return statement uses it
locally. False entry or read claims fail. `write-observations.js` checks these
outcomes, the source shape, and runtime and producer behavior. The three unsafe
original exports are independently audited by `refinement-witnesses.js`.

`undefined-completes.ts` is the one entry the verifier establishes with no
repair at all. A body that completes returns undefined, which is what it
declares; SKJS rejects it as not returning on every path. The exit carries
undefined and discharges the annotation directly, so the producer's partial
export is enough. `skjs-unsound/never-completes.ts` is the same SKJS check
skipped rather than too strict.
