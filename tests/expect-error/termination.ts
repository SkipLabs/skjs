// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function breaksInSwitch(b: boolean): number {
  switch (b) {
    case true:
      break;
    default:
      break;
  }
}

// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function breakInLoop(): number {
  while (true) {
    break;
  }
}

function throwInForIncr(): void {
  throw new Error("boom");
}

// `continue` inside a `for` loop executes the increment expression before the
// next iteration. When the increment can throw, the `for` loop can exit via
// that exception, which runs an enclosing `finally` (and can therefore break an
// enclosing `while (true)` and fall through an `if` branch).
// Pre-fix: `For` chained `incr` before `continueToFallthrough()`, so a
// `continue`-only body skipped `incr`'s `mayThrow` and made the outer `while`
// appear non-terminating.
function forContinueIncrThrowsFallsThroughFunction(): number {
  while (true) {
    try {
      for (let i = 0; true; throwInForIncr()) {
        continue;
      }
    } finally {
      break;
    }
  }
}

function forContinueIncrThrowsInIfBranch(x: string | number): string {
  if (typeof x === "number") {
    while (true) {
      try {
        for (let i = 0; true; throwInForIncr()) {
          continue;
        }
      } finally {
        break;
      }
    }
  }
  return x;
}

// `await` can throw if the awaited promise rejects, so a `while (true)` loop
// containing `await` can exit exceptionally into an enclosing `finally`.
async function awaitThrowsInIfBranch(
  x: string | number,
  p: Promise<void>,
): Promise<string> {
  if (typeof x === "number") {
    while (true) {
      try {
        while (true) {
          await p;
        }
      } finally {
        break;
      }
    }
  }
  return x;
}

// Array/call spread invokes `[Symbol.iterator]` and `.next()`, which can throw.
function spreadThrowsInIfBranch(
  x: string | number,
  iter: Iterable<number>,
): string {
  if (typeof x === "number") {
    while (true) {
      try {
        while (true) {
          const _a = [...iter];
        }
      } finally {
        break;
      }
    }
  }
  return x;
}

// Positive: a `for` loop whose body always returns never reaches the increment,
// so a throwing increment does not make the loop throw or fall through.
function forBodyAlwaysReturnsNeverRunsIncr(): number {
  for (let i = 0; true; throwInForIncr()) {
    return 1;
  }
}

// Positive: a `for` loop whose body continues with a non-throwing increment
// still loops forever and does not fall through.
function forContinuePureIncrLoopsForever(): number {
  for (let i = 0; true; i++) {
    continue;
  }
}

// Positive: an `if` whose `then` branch cannot fall through because of a
// genuinely infinite loop narrows the surviving `else` path.
function ifInfiniteLoopNarrowsAfter(x: string | number): string {
  if (typeof x === "number") {
    while (true) {
      // no break, no throw
    }
  }
  return x;
}

// Positive: a bare block executes unconditionally when it falls through, so
// writes, narrowings, and definite assignments inside it survive after the
// block (matching `tsc`).
// Pre-fix: `Block` called `popScope` (merge with pre-block state) on
// fallthrough instead of `popScopeReplace`.
function bareBlockDefiniteAssignment(): string {
  let x: string;
  {
    x = "ok";
  }
  // @skjs-expect-error Variable 'x' is used before being assigned
  return x;
}

function bareBlockReassignment(): string {
  let x: string | number = 1;
  {
    x = "ok";
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

function bareBlockReturnGuardNarrows(x: string | number): string {
  {
    if (typeof x === "number") {
      return "num";
    }
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// Negative: a conditional write inside a bare block still keeps the untouched
// pre-block type.
function bareBlockConditionalWriteKeepsPreState(cond: boolean): string {
  let x: string | number = 1;
  {
    if (cond) {
      x = "ok";
    }
  }
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return x;
}
