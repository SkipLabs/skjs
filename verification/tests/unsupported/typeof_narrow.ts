function describe(x: string | number | null): string {
  if (typeof x === "string") {
    return x;
  }
  if (typeof x === "number") {
    return "a number";
  }
  return "null";
}
