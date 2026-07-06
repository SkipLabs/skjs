// '8' is not an octal digit: a syntax error (tsc TS1178).
// (prettier also rejects the malformed literal, hence the file name)
// @skjs-expect-error Octal digit expected
const invalidOctalDigit: 8 = 0o8;
