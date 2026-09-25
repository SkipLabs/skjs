// A loop over a `Set`: `for...of` steps `%Iterate%`, stated for arrays only
// (DESIGN.md, "Loops over arrays").
function sum(s: Set<number>): number {
  let total = 0;
  for (const x of s) total += x;
  return total;
}
