// The next iteration can read null despite the pre-loop string narrowing.
function staleLoopRead(x: string | null, again: boolean): void {
  if (x !== null) {
    while (again) {
      // @ts-expect-error Type of value is not assignable to the variable's type annotation
      const text: string = x;
      x = null;
    }
  }
}

// The increment is part of the back edge, even when the body continues.
function staleIncrementRead(x: string | null, again: boolean): void {
  if (x !== null) {
    for (; again; x = null) {
      // TypeScript also accepts this stale read.
      // @skjs-expect-error Type of value is not assignable to the variable's type annotation
      const text: string = x;
      continue;
    }
  }
}

function staleForOfRead(x: string | null, values: number[]): void {
  if (x !== null) {
    for (const value of values) {
      // A fresh iteration variable does not stabilize an outer binding.
      // @ts-expect-error Type of value is not assignable to the variable's type annotation
      const text: string = x;
      x = null;
    }
  }
}

// A condition checked on each iteration establishes a fresh narrowing.
function guardedLoopRead(x: string | null, again: boolean): void {
  while (x !== null && again) {
    const text: string = x;
    x = null;
  }
}

// Preserve facts about bindings that the loop never assigns.
function unchangedLoopRead(x: string | null, again: boolean): void {
  if (x !== null) {
    let count: number = 0;
    while (again) {
      const text: string = x;
      count += 1;
    }
  }
}

// The for condition is rechecked after its increment, just like a while guard.
function guardedIncrementRead(x: string | null): void {
  if (x !== null) {
    for (; x !== null; x = null) {
      const text: string = x;
    }
  }
}
