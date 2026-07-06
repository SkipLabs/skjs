// Consecutive numeric separators: a syntax error (tsc TS6189).
// (prettier also rejects the malformed literal, hence the file name)
// @skjs-expect-error Multiple consecutive numeric separators are not permitted
const invalidDoubleSeparator: 10 = 1__0;
