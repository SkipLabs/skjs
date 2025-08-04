// Test file to verify continue statement behavior in loops

function testContinueInForLoop(): string[] {
  const result: string[] = [];
  
  for (let i = 0; i < 10; i++) {
    if (i % 2 === 0) {
      continue; // Skip even numbers
    }
    result.push(i.toString());
  }
  
  return result; // Should contain ['1', '3', '5', '7', '9']
}

function testContinueInWhileLoop(): number {
  let count = 0;
  let i = 0;
  
  while (i < 20) {
    i++;
    if (i % 3 === 0) {
      continue; // Skip multiples of 3
    }
    count++;
  }
  
  return count; // Should be 20 - 6 = 14 (6 multiples of 3 between 1-20)
}

function testNestedLoopsWithContinue(): number[][] {
  const result: number[][] = [];
  
  for (let i = 0; i < 3; i++) {
    const row: number[] = [];
    for (let j = 0; j < 5; j++) {
      if (j === 2) {
        continue; // Skip j=2 in inner loop
      }
      row.push(i * 10 + j);
    }
    if (i === 1) {
      continue; // Skip row i=1
    }
    result.push(row);
  }
  
  return result; // Should be [[0,1,3,4], [20,21,23,24]]
}

// Test to verify continue works with array iteration
function testContinueWithArrayIteration(): string {
  const items = ['a', 'b', 'skip', 'c', 'skip', 'd'];
  let result = '';
  
  for (const item of items) {
    if (item === 'skip') {
      continue;
    }
    result += item;
  }
  
  return result; // Should be 'abcd'
}