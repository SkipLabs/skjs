// An opaque call (no CFG for `console.log`) must return `top` and leave
// execution reachable, not mark the continuation dead.

function main(): number {
  const x = 5;
  console.log(x);
  return x;
}
