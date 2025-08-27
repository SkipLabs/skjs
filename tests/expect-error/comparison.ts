function singleTypeLhs(x: number | string): boolean {
  // @ts-expect-error Invalid comparison. You can only compare strings, numbers, and booleans.
  return x < 0;
}

function singleTypeRhs(x: number | string): boolean {
  // @ts-expect-error Invalid comparison. You can only compare strings, numbers, and booleans.
  return 0 < x;
}

function sameType(x: number, y: string): boolean {
  // @ts-expect-error Invalid comparison. Both operands must have the same type.
  return x < y;
}
