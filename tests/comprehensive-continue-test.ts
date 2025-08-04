// Comprehensive test for continue statement functionality

function testContinueInForLoop(): void {
  let sum = 0;
  
  for (let i = 0; i < 10; i++) {
    if (i % 2 === 0) {
      continue; // Skip even numbers
    }
    sum += i; // Only odd numbers: 1+3+5+7+9 = 25
  }
  
  if (sum !== 25) {
    throw new Error(`Expected sum to be 25, got ${sum}`);
  }
}

function testContinueInWhileLoop(): void {
  let count = 0;
  let processed = 0;
  
  while (count < 10) {
    count++;
    if (count <= 3) {
      continue; // Skip first 3 iterations
    }
    processed++;
  }
  
  if (processed !== 7) {
    throw new Error(`Expected processed to be 7, got ${processed}`);
  }
}

function testContinueInNestedLoops(): void {
  let result = 0;
  
  for (let i = 0; i < 3; i++) {
    for (let j = 0; j < 3; j++) {
      if (j === 1) {
        continue; // Skip middle iteration of inner loop
      }
      result += i * 10 + j;
    }
    if (i === 1) {
      continue; // Skip middle iteration of outer loop
    }
    result += 100; // Add 100 for non-skipped outer iterations
  }
  
  // Expected: (0+2) + 100 + (20+22) + 100 = 244
  if (result !== 244) {
    throw new Error(`Expected result to be 244, got ${result}`);
  }
}

// Test that break and continue work together
function testBreakAndContinue(): void {
  let count = 0;
  let sum = 0;
  
  for (let i = 0; i < 20; i++) {
    if (i > 15) {
      break; // Exit loop after 15
    }
    if (i % 3 === 0) {
      continue; // Skip multiples of 3
    }
    count++;
    sum += i;
  }
  
  // Numbers processed: 1,2,4,5,7,8,10,11,13,14 (10 numbers)
  // Sum: 1+2+4+5+7+8+10+11+13+14 = 75
  if (count !== 10 || sum !== 75) {
    throw new Error(`Expected count=10 and sum=75, got count=${count} and sum=${sum}`);
  }
}

// Test to ensure continue doesn't affect outer scope
function testContinueScope(): void {
  let outerSum = 0;
  
  for (let i = 0; i < 5; i++) {
    let innerValue = i * 2;
    if (i === 2) {
      continue;
    }
    outerSum += innerValue;
  }
  
  // Should add: 0 + 2 + (skip 4) + 6 + 8 = 16
  if (outerSum !== 16) {
    throw new Error(`Expected outerSum to be 16, got ${outerSum}`);
  }
}