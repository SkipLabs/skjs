// '2' is not a binary digit: a syntax error (tsc TS1177).
// (prettier also rejects the malformed literal, hence the file name)
// @skjs-expect-error Binary digit expected
const invalidBinaryDigit: 2 = 0b12;
