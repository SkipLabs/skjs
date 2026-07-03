// An exponent marker with no digits: a syntax error (tsc TS1124).
// (prettier also rejects the malformed literal, hence the file name)
// @skjs-expect-error Digit expected
const invalidDanglingExponent: 1 = 1e;
