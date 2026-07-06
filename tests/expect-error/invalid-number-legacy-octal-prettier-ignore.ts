// A legacy octal literal (leading zero): a syntax error (tsc TS1121); its
// sloppy-mode JS value is 8, never 10.
// (prettier also rejects the malformed literal, hence the file name)
// @skjs-expect-error Octal literals are not allowed. Use the syntax '0o10'
const invalidLegacyOctal: 10 = 010;
