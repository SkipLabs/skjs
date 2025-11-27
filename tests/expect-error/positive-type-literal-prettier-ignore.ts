// Test that positive type literals with unary + are rejected

// @ts-expect-error Unexpected token
const plusNum: +42 = 42;
