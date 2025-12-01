// Test that positive bigint type literals with unary + are rejected

// @ts-expect-error Expected token ' or " or ` or < or [ or ( or { or - or a number or a bigint or a variable name
const plusBig: +100n = 100n;
