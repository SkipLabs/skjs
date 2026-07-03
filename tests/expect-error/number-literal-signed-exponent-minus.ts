// ES exponent parts may carry a sign: 1e-3 is the literal 0.001. The lexer
// ends the numeric token at the sign, so 1e-3 parses as the arithmetic
// expression (1e) - 3 and types as plain number.

// FIXME: tsc accepts: 1e-3 is the literal 0.001
function signedExponentMinus(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 0.001 = 1e-3;
}

// FIXME: tsc accepts: 1e-7 is a valid literal type
function signedExponentType(): void {
  // @skjs-expect-error A 'const' declaration must be initialized
  // @skjs-expect-error The left-hand side of an assignment must be a variable or a property access
  const a: 1e-7 = 0.0000001;
}
