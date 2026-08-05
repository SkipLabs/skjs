// Loops and conditionals, with comments throughout: the point of inserting
// annotations into the source text rather than reprinting the AST is that
// every comment in this file survives into the annotated output verbatim.

function counted(n: number): number {
  let i = 0;
  // `i` disagrees around the back edge, so the loop head widens it to top.
  while (i < n) {
    i = i + 1;
  }
  return i;
}

function loopInvariant(): number {
  let s = 3;
  let i = 0;
  while (i < 4) {
    s = 3; // same constant on both edges: `s` survives the widening
    i = i + 1;
  }
  return s;
}

/* A block comment, to check that those are left alone too. */
function classify(n: number): string {
  if (n < 0) {
    return "negative";
  } else if (n === 0) {
    // Reached only when n is exactly zero.
    return "zero";
  }
  return "positive";
}

function pick(n: number): number {
  switch (n) {
    case 0:
      return 10;
    case 1:
      return 20;
    default:
      return 30;
  }
}

function forSum(): number {
  let total = 0;
  for (let j = 0; j < 3; j = j + 1) {
    total = total + j;
  }
  return total;
}

function main(): number {
  const a = counted(4);
  const b = loopInvariant();
  const c = forSum();
  const d = pick(1);
  const e = classify(0);
  const f = e.length;
  return a + b + c + d + f;
}

// Module top-level code is the entrypoint; it invokes main.
const _ = main();
