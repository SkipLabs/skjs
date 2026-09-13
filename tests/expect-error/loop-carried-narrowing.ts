// FIXME: the next iteration can read null under the pre-loop string narrowing.
function staleLoopRead(x: string | null, again: boolean): void {
  if (x !== null) {
    while (again) {
      const text: string = x;
      x = null;
    }
  }
}

// The increment is part of the back edge, even when the body continues.
function staleIncrementRead(x: string | null, again: boolean): void {
  if (x !== null) {
    for (; again; x = null) {
      // FIXME: the increment invalidates this read on the next iteration.
      const text: string = x;
      continue;
    }
  }
}

function staleForOfRead(x: string | null, values: number[]): void {
  if (x !== null) {
    for (const value of values) {
      // FIXME: a fresh iteration variable does not stabilize an outer binding.
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
