// Test if/else with blockOrStmt (allows single statements without braces)

function testIfElse(): void {
  const x: number = 5;
  let y: number = 0;

  // Valid: single statement without braces (assignment)
  if (x > 0) y = 10;

  // Valid: block with statement
  if (x > 10) {
    y = 20;
  }

  // Valid: if-else with statements
  if (x > 0) y = 1;
  else y = 2;

  // Valid: if-else with blocks
  if (x > 5) {
    y = 30;
  } else {
    y = 40;
  }

  // Empty if block - what happens?
  if (x > 0) {
  }

  // Empty else block - what happens?
  if (x > 0) {
    y = 50;
  } else {
  }
}
