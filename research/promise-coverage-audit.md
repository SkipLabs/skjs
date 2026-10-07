<!-- Research note awaiting relocation: each rule still missing once the native-promise work lands becomes a row in verification/WORK.md. -->
# Promise rules beyond native contracts and `Awaited`

Six mechanisms that promise-related fixtures need, each beyond native promise contracts and a generic `Awaited<T>`. Each names the fixtures it would let verify; these are judgments from reading the sources, not checker runs.

| Rule | What it establishes | Fixtures |
| --- | --- | --- |
| **F**, fresh object | A freshly allocated ordinary object with no own `then`, under an unmodified prototype with no callable or getter `then`, fulfills with itself at that resolution step, keeping its field contracts. The fact concerns that step only; later aliases may add a `then`. | `async-object-result-refused.ts`; `nested_async_test.ts` `createCounterService`; `unsound-refinement.ts` `freshReturnSnapshot` |
| **K**, known thenable | A stable typed `then` that passes values of type $`V`$ to its resolving callback fulfills with what resolving those values gives; its own return value plays no part. `PromiseLike<number>` and `PromiseLike<Promise<number>>` give `number`. Lookup, invocation and continuations keep their effects. | `await-thenable-refused.ts`; `promise-object.ts` `testAwaitThenable`, `testAwaitThenableNested` |
| **E**, executor effect | Every value $`u : U`$ an executor passes to its resolver resolves within the constructed `Promise<B>`; the executor keeps its written arrow type, the effect records what it submits, and an untracked escape refuses. | `invalid-new-promise-object.ts` (with F) |
| **S**, settled-state correlation | Entering a fulfillment callback records `Fulfilled(p, T)` for that native identity; settlement is immutable, so the fact survives heap havoc and makes a rejection callback on the same unreassigned `p` unreachable. | `invalid-promise-then-chained.ts` |
| **C**, terminal-free cycles | A recursive component whose every resolution edge keeps a stable typed callable `then` and has no terminal exit has no successful resolution; it discharges value obligations only, never termination or effects. | `promise-object.ts` `testAwaitSelfThenable`, `testAsyncReturnSelfThenable`, `testArrowSelfThenable` |
| **N**, native no-success | When every value of $`B`$ has a stable callable `then`, a native `Promise<B>` never fulfills; it is still inhabited by rejecting and pending promises. | `promise-object.ts` `testAwaitNested` |

Three fixtures named `invalid-*` are safe under these rules: `invalid-new-promise-object.ts` (E with F), `invalid-promise-then-chained.ts` (S), and `invalid-nested-promise-instance.ts` (N: its ambient `wrap<T>(x: T): Promise<T>` at `T = Promise<number>` states a promise that never fulfills).
