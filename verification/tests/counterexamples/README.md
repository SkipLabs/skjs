# Producer counterexamples

`captured-refinement.ts` is accepted by SKJS. `staleCapturedCell(true)` returns
`false`, contradicting its declared `true` result: a callback writes the captured
cell after the branch test, but SKJS retains the read refinement.

The current verifier distinguishes two checks in `primitive-callbacks.js`:

1. The actual export is rejected because its refined read type and mutable write
   type do not describe one invariant cell contract. This is a contract boundary.
2. A manually weakened candidate forgets only reference read refinements, retaining
   SKJS's expression types. It reaches proof checking and fails at the stale read.

The test pins the source location and the runtime result. It does not label the
original gate rejection as a semantic proof that the program is unsound.
`stableSnapshot` in `stateful-source/primitive-callbacks.ts` verifies and returns
true: it tests and returns the same immutable value saved before the callback.

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
