// Consecutive numeric separators: tsc reports a syntax error (TS6189).
// (prettier also rejects the malformed literal, hence the file name)
// FIXME: SKJS strips the separators and accepts 1__0 as 10
const invalidDoubleSeparator: 10 = 1__0;
