// Test that positive bigint type literals with unary + are rejected

// @skjs-expect-error ''' or '"' or '`' or '<' or '[' or '(' or '{' or '-' or 'a number' or 'a bigint' or 'a variable name' expected
const plusBig: +100n = 100n;
