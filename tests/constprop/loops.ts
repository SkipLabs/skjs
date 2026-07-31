// Loops: the back edge is what makes constant propagation a real fixpoint
// computation, and it is where `updateState` widens instead of joining.
//
// A variable that takes a different value on the back edge than on the entry
// edge cannot converge by joining constants — it ascends to `top` in one
// widening step rather than climbing 0, 1, 2, ... forever. A variable that is
// unchanged around the loop is unaffected: widening only loses the bindings
// that actually disagree.
//
// In the expectations, `top` is represented by absence: `setVar` drops a
// variable from the environment rather than binding it to `top`, so a widened
// `i` simply does not appear in the loop blocks.

function counted(n: number): number {
  let i = 0;
  while (i < n) {
    // `i` is 0 on the entry edge and 1 on the back edge, so the loop head
    // widens it to `top` — which in turn makes `i < n` unknown, keeping both
    // the body and the exit live.
    i = i + 1;
  }
  return i; // top
}

function loopInvariant(n: number): number {
  let s = 3;
  let i = 0;
  while (i < n) {
    s = 3; // same constant on both edges: `s` survives the widening
    i = i + 1;
  }
  return s; // 3
}

function forSum(): number {
  let total = 0;
  for (let j = 0; j < 3; j = j + 1) {
    total = total + j;
  }
  return total; // top: `total` disagrees around the back edge
}

function main(): number {
  const a = counted(4);
  const b = loopInvariant(4);
  const c = forSum();
  return a + b + c;
}

// Module top-level code is the entrypoint; it invokes main.
const _ = main();
