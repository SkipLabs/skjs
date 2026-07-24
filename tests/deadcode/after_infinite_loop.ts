// NOTE: currently deadcode analysis ignores conditions so the loop _does_ fall through

// Two kinds of dead code around a non-returning function:
//   - Intra-procedural: the `return` after the infinite loop is unreachable.
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
