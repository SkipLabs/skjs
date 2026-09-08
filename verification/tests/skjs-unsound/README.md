# SKJS unsoundness examples

Programs accepted by SKJS whose declared types are contradicted by runtime behavior.

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
`stableSnapshot` in [the primitive callback fixture](../stateful-source/primitive-callbacks.ts) verifies and returns
true: it tests and returns the same immutable value saved before the callback.

