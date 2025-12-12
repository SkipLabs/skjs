// INCOMPLETENESS: SKJS supports literal types but not literal value narrowing

// PART 1: Literal types ARE supported
function literalTypesWork(): void {
  const one: 1 = 1;           // OK: literal 1 has type 1
  const two: 2 = 2;           // OK: literal 2 has type 2
  const n: number = one;      // OK: 1 is assignable to number
  const union: 1 | 2 = one;   // OK: 1 is assignable to 1 | 2

  // @skjs-expect-error number is not assignable to literal type 1
  const bad: 1 = n;           // ERROR: number not assignable to 1
}

// PART 2: Literal value narrowing is NOT supported (the incompleteness)
// This is a valid TypeScript program that SKJS incorrectly rejects.
function literalNarrowingFails(x: 1 | 2): 2 {
  if (x === 1) {
    return 2;  // Early return when x is 1
  }
  // TypeScript: x is narrowed to 2 here
  // SKJS: x is still 1 | 2 (no narrowing performed)
  return x;  // SKJS ERROR: '1 | 2' not assignable to '2'
}

// This program is valid TypeScript but rejected by SKJS.
