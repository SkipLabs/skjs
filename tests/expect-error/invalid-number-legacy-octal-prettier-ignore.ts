// A legacy octal literal (leading zero): tsc reports a syntax error (TS1121)
// and its sloppy-mode JS value is 8, never 10.
// (prettier also rejects the malformed literal, hence the file name)
// FIXME: SKJS strips the leading zero and accepts 010 as 10
const invalidLegacyOctal: 10 = 010;
