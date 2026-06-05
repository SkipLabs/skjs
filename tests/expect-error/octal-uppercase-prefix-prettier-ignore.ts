// prettier-ignore
// Octal literals with the uppercase 0O prefix (prettier rewrites 0O to 0o,
// hence the prettier-ignore file)

// Valid: octal number literal with uppercase prefix
const octalUpper = 0O17;

// Valid: octal bigint literal with uppercase prefix
const octalUpperBig = 0O17n;
