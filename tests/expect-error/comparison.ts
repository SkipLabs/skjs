function singleTypeLhs(x: number | string): boolean {
  // @skjs-expect-error A comparison operand must be a string, number, bigint, or boolean
  return x < 0;
}

function singleTypeRhs(x: number | string): boolean {
  // @skjs-expect-error A comparison operand must be a string, number, bigint, or boolean
  return 0 < x;
}

function sameType(x: number, y: string): boolean {
  // @skjs-expect-error Both operands of a comparison must have the same type
  return x < y;
}
