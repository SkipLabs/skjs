// The clauses of a switch share one scope: `n`, declared in case 1, is the
// same binding in case 2, uninitialized there when case 2 is entered. Each
// clause's statements are lowered in a scope of their own, so the gate
// refuses a name read outside the clause declaring it.
function shared(x: number): number {
  switch (x) {
    case 1:
      const n = 1;
      return n;
    case 2:
      return n;
  }
  return 0;
}
