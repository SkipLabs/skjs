// Test that empty statements (;) after if are rejected (parse error)

function testEmptyIfStmt(): void {
  const x: number = 5;

  // @ts-expect-error The body of an 'if' statement cannot be the empty statement
  if (x > 0);
