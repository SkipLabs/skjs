function classify(n: number): string {
  if (n < 0) {
    return "negative";
  } else {
    if (n === 0) {
      return "zero";
    }
  }
  return "positive";
}

function sumTo(n: number): number {
  let total = 0;
  let i = 0;
  while (i < n) {
    i = i + 1;
    if (i % 2 === 0) {
      continue;
    }
    if (i > 100) {
      break;
    }
    total = total + i;
  }
  for (let j = 0; j < n; j = j + 1) {
    total = total + j;
  }
  return total;
}

function sumArray(xs: number[]): number {
  let total = 0;
  for (const x of xs) {
    total = total + x;
  }
  return total;
}
