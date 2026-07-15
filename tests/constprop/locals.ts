// Intraprocedural propagation: literals and folding through bindings, branch
// pruning on a known condition, and invalidation on reassignment.

function main(): number {
  let x = 1;
  const y = 2;
  const z = x + y; // folded to 3

  if (z === 3) {
    x = 10; // taken
  } else {
    x = 20; // pruned: z === 3 is known true
  }

  return x; // 10
}
