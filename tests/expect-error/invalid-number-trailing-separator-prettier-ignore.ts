// A trailing numeric separator: a syntax error (tsc TS6188).
// (prettier also rejects the malformed literal, hence the file name)
// @skjs-expect-error Numeric separators are not allowed here
const invalidTrailingSeparator: 1 = 1_;
