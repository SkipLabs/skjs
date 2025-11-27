// Test that positive bigint type literals with unary + are rejected

// @ts-expect-error Unexpected token
const plusBig: +100n = 100n;
