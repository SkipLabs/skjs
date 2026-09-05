// SKJS must reject: the branch taken when `x === null` holds null, not string.
function pick(x: string | null): string {
  if (x === null) {
    return x;
  }
  return "other";
}
