// An exponent marker with no digits: tsc reports a syntax error (TS1124).
// (prettier also rejects the malformed literal, hence the file name)
// FIXME: SKJS accepts 1e and mis-values it as 1
const invalidDanglingExponent: 1 = 1e;
