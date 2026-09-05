// Outside the fragment: the gate must reject a loop.
function count(n: number): number {
  while (n === 0) {
    return n;
  }
  return n;
}
