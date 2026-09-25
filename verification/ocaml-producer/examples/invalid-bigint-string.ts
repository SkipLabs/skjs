// A string literal `BigInt` does not parse: `BigInt("1.5")` throws a
// SyntaxError. An arbitrary string is refused for the same reason.
function parsed(): bigint {
  return BigInt("1.5");
}
