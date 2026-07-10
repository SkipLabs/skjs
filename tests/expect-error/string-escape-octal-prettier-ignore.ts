// prettier-ignore
// A legacy octal escape sequence. tsc rejects these under --strict (TS1487);
// leaving them undecoded is unsound (issue #771), so skjs rejects them too.
// @skjs-expect-error Octal escape sequences are not allowed
type T = "\1";
