function finallyOnly(n: number): number {
  let log = 0;
  try {
    if (n > 0) {
      throw new Error("positive");
    }
    log = 1;
  } finally {
    log = 2;
  }
  return log;
}

function breakThroughFinally(xs: number[]): number {
  let count = 0;
  for (const x of xs) {
    try {
      if (x < 0) {
        break;
      }
      count = count + 1;
    } finally {
      count = count * 2;
    }
  }
  return count;
}

function nestedFinallys(n: number): number {
  let m = n;
  try {
    try {
      return m;
    } finally {
      m = m + 1;
    }
  } finally {
    m = m + 2;
  }
}
