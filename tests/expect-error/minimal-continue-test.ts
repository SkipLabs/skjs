// Minimal test to verify continue statement works

function testContinue(): void {
  let count = 0;

  for (let i = 0; i < 5; i++) {
    if (i === 2) {
      continue; // Skip when i equals 2
    }
    count = count + 1;
  }

  // count should be 4 (skipped one iteration)
  console.log(count);
}

function testContinueInWhile(): void {
  let i = 0;
  let processed = 0;

  while (i < 3) {
    i = i + 1;
    if (i === 2) {
      continue; // Skip when i equals 2
    }
    processed = processed + 1;
  }

  // processed should be 2 (skipped one iteration)
  console.log(processed);
}
