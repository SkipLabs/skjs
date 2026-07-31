// Calls nested inside a larger expression are now resolved interprocedurally
// (previously they folded to `top`). `five()` nested inside `... + 1` resolves
// to 5, so `a` is 6; `five()` passed as an argument to `double` resolves too,
// so `double` is seen with `n = 5` and `b` is 10. `main` returns 16.

function five(): number {
  return 5;
}

function double(n: number): number {
  return n * 2;
}

function main(): number {
  const a = five() + 1;
  const b = double(five());
  return a + b;
}

// Module top-level code is the entrypoint; it invokes main.
const _ = main();
