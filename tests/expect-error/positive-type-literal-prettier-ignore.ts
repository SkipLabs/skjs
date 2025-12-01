// Test that positive type literals with unary + are rejected

// @ts-expect-error Expected token ' or " or ` or < or [ or ( or { or - or a number or a bigint or a variable name
const plusNum: +42 = 42;
