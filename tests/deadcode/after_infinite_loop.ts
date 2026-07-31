// Two kinds of dead code around a non-returning function:
//   - Intra-procedural: the `return` after the infinite loop is unreachable.
//     Note this one is settled before the dataflow runs: the dataflow ignores
//     conditions, so it alone would let `while (true)` fall through. It is the
//     CFG builder that consults `stmtTerminations`, sees the loop cannot
//     complete normally, and emits `return 0` into a block nothing jumps to.
//   - Inter-procedural: because `afterInfiniteLoop` never returns, `neverReached`
//     — invoked after it at the top level — never executes, so the whole
//     function is dead. Nothing sequenced past a non-returning call runs.

function afterInfiniteLoop(): number {
  while (true) {
    let x = 1;
  }
  return 0;
}

function neverReached(): number {
  return 1;
}

const r1 = afterInfiniteLoop();
const r2 = neverReached();
