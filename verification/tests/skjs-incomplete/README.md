# SKJS incompleteness examples

Programs rejected by SKJS that the independent verifier can establish after
repairing the producer’s claims. These are precision gaps, not unsafe programs.

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
