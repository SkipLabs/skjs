// INCOMPLETENESS: Missing strict-equality refinement for primitive literals
//
// This is a MISSING IMPLEMENTATION CASE, not a representation limitation.
// SKJS can represent 1|2 and can represent 2, but the refinement for
// "x === 1" is not implemented for primitive literals.
//
// See: docs/skjs-type-soundness.tex, Section 7.1

// PART 1: Literal types ARE supported
function literalTypesWork(): void {
  const one: 1 = 1; // OK: literal 1 has type 1
  const two: 2 = 2; // OK: literal 2 has type 2
  const union: 1 | 2 = one; // OK: 1 is assignable to 1 | 2
}

// PART 2: Strict-equality refinement for literals is NOT implemented
// This is a valid TypeScript program that SKJS incorrectly rejects.
function literalNarrowingFails(x: 1 | 2): 2 {
  if (x === 1) {
    return 2; // Early return when x is 1
  }
  // TypeScript: x is narrowed to 2 (subtracts {1} from {1,2})
  // SKJS: x is still 1|2 (strict-equality refinement not implemented for literals)
  // @skjs-expect-error Invalid return type
  return x;
}

// Could be implemented: intersect/subtract literal-set payloads on === checks.
