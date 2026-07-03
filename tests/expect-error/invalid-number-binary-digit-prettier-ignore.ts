// '2' is not a binary digit: tsc reports a syntax error (TS1177).
// (prettier also rejects the malformed literal, hence the file name)
// FIXME: SKJS accepts 0b12 and mis-values it as 2
const invalidBinaryDigit: 2 = 0b12;
