// A hex prefix with no digits: tsc reports a syntax error (TS1125).
// (prettier also rejects the malformed literal, hence the file name)
// FIXME: SKJS accepts 0x and mis-values it as 0
const invalidEmptyHex: 0 = 0x;
