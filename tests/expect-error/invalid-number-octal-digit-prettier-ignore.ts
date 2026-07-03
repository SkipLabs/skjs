// '8' is not an octal digit: tsc reports a syntax error (TS1178).
// (prettier also rejects the malformed literal, hence the file name)
// FIXME: SKJS accepts 0o8 and mis-values it as 8
const invalidOctalDigit: 8 = 0o8;
