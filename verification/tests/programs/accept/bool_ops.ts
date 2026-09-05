function both(a: string | null, b: string | null): string {
  if (a !== null && b !== null) {
    return a;
  }
  if (!(a === null)) {
    return a;
  }
  return "neither";
}

function either(flag: boolean, s: string | null): string {
  if (flag || s === null) {
    return "left";
  }
  return s;
}
