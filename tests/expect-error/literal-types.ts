// Test literal type annotations with unary operators

// Valid: negative number literal types
const negativeNum: -42 = -42;

// Valid: negative bigint literal types
const negativeBig: -100n = -100n;

// Valid: positive number literals (without unary +)
const positiveNum: 42 = 42;

// Valid: positive bigint literals (without unary +)
const positiveBig: 100n = 100n;

// Valid: octal number literal
const octalNum = 0o17;

// Valid: octal number literal type matching itself
const octalType: 0o17 = 0o17;

// Valid: octal bigint literal
const octalBig = 0o17n;
