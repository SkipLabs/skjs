// Test that positive type literals with unary + are rejected

// @skjs-expect-error ''' or '"' or '`' or '<' or '[' or '(' or '{' or '-' or 'a number' or 'a bigint' or 'a variable name' expected
const plusNum: +42 = 42;
