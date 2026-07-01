// Functions with no dead code: every block is reachable, including both arms of
// a branch and the body/exit of a terminating loop.

function bothBranches(b: boolean): number {
  if (b) {
    return 1;
  }
  return 2;
}

function countingLoop(n: number): number {
  let sum = 0;
  let i = 0;
  while (i < n) {
    sum = sum + i;
    i = i + 1;
  }
  return sum;
}
