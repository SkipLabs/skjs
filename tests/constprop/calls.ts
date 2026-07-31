// Interprocedural binding + return values: `add`/`pick` are seen only through
// their (single) call sites, so their formals are bound to the actuals, and
// their return values flow back into `main`.

function add(a: number, b: number): number {
  return a + b;
}

function pick(c: boolean): number {
  // With `c` bound to `true` at the only call site, the `else` edge is pruned.
  if (c) {
    return 10;
  }
  return 20;
}

function main(): number {
  const s = add(2, 3);
  const u = pick(true);
  return s + u;
}

// Module top-level code is the entrypoint; it invokes main.
const _ = main();
