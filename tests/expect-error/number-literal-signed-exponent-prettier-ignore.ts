// ES exponent parts may carry a sign: 1e+3 is the literal 1000. The lexer
// ends the numeric token at the sign, so 1e+3 parses as the arithmetic
// expression (1e) + 3 and types as plain number.
// (prettier rewrites 1e+3 to 1e3, hence the file name)

// FIXME: tsc accepts: 1e+3 is the literal 1000
function signedExponentPlus(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const a: 1000 = 1e+3;
}
