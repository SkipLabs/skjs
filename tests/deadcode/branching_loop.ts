// A branchy graph (sequential diamonds) whose merge points are reachable along
// many paths, feeding a loop — exercises back-edge detection on a non-trivial
// CFG. Only the statement after `return` is dead.

function branchyWithLoop(a: boolean, b: boolean, c: number): number {
  let x = 0;
  if (a) {
    x = 1;
  } else {
    x = 2;
  }
  if (b) {
    x = x + 1;
  }
  while (x < c) {
    x = x + 1;
  }
  return x;
  x = 999;
}

// Top-level entrypoint that makes the function reachable.
const result = branchyWithLoop(true, false, 3);
