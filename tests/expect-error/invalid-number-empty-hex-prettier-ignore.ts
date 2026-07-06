// A hex prefix with no digits: a syntax error (tsc TS1125).
// (prettier also rejects the malformed literal, hence the file name)
// @skjs-expect-error Hexadecimal digit expected
const invalidEmptyHex: 0 = 0x;
