// Test blockOrStmt: single statements and empty statements (;) after control structures

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

  // Valid: empty if block
  if (x > 0) {
  }

  // Valid: empty else block
  if (x > 0) {
    y = 50;
  } else {
  }

  // Valid: empty statement (;) after if
  if (x > 0);

  // Valid: empty statement (;) after else
  if (x > 0) y = 1;
  else;

  // Valid: empty statement (;) after if with block else
  if (x > 0);
  else y = 2;
}

function testWhile(): void {
  let x: number = 5;

  // Valid: single statement after while
  while (x > 0) x = x - 1;

  // Valid: block after while
  while (x > 0) {
    x = x - 1;
  }

  // Valid: empty statement (;) after while
  while (x > 0);

  // Valid: empty block after while
  while (x > 0) {}
}

function testFor(): void {
  let x: number = 0;
  const arr = [1, 2, 3];

  // Valid: single statement after for
  for (let i: number = 0; i < 5; i = i + 1) x = i;

  // Valid: empty statement (;) after for
  for (let i: number = 0; i < 5; i = i + 1);

  // Valid: empty block after for
  for (let i: number = 0; i < 5; i = i + 1) {}

  // Valid: single statement after for-in
  for (const key in arr) x = 1;

  // Valid: empty statement (;) after for-in
  for (const key in arr);

  // Valid: single statement after for-of
  for (const val of arr) x = val;

  // Valid: empty statement (;) after for-of
  for (const val of arr);
}
