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

`negation.js` takes SKJS's normal-mode partial export (without `--keep-going`),
changes exactly the final statement's `flag` binding and its returned-expression
claim from `boolean` to `true`, and produces a certificate accepted by the
independent consumer. An incorrect `false` exit binding is rejected. This tests
manual completion of producer claims using the calculus's own rules; it does not
change SKJS's behavior or infer correctness from SKJS's diagnostic.

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

This is **not yet a certificate produced by the source checker**. Editing the read
claim to true still fails current proof search; graph typing and certificate
checking do not yet consume observations. `write-observations.js` pins the source
shape used by the model proof, checks both TypeScript/SKJS outcomes and runtime
results, and retains this distinction. See [Current-content assertions](../../DESIGN.md#current-content-assertions).
