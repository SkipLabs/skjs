// A trailing numeric separator: tsc reports a syntax error (TS6188).
// (prettier also rejects the malformed literal, hence the file name)
// FIXME: SKJS strips the separator and accepts 1_ as 1
const invalidTrailingSeparator: 1 = 1_;
