// Unreachable code detection (TS7027) and exhaustive if/else-if termination.

const B = "b";

// Exhaustive if / else-if chain without a trailing return:
// `if (x === "b")`'s empty else branch narrows `x` to `never`, so the chain
// does not fall through and no dummy fallback return is needed.
function exhaustiveLiteralNoFallback(x: "a" | "b"): string {
  if (x === "a") {
    return "first";
  } else if (x === "b") {
    return "second";
  }
}

// Same with a hoisted constant:
function exhaustiveConstantNoFallback(x: "a" | "b"): string {
  if (x === "a") {
    return "first";
    // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  } else if (x === B) {
    return "second";
  }
}

// Same with a tagged union discriminant field:
type TaggedAB = { kind: "a"; n: number } | { kind: "b"; s: string };
function exhaustiveFieldNoFallback(x: TaggedAB): string {
  if (x.kind === "a") {
    return "first";
  } else if (x.kind === "b") {
    return "second";
  }
}

// Trailing statement after an exhaustive if / else-if chain reports TS7027:
function exhaustiveWithUnreachableFallback(x: "a" | "b"): string {
  if (x === "a") {
    return "first";
    // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  } else if (x === B) {
    return "second";
  }
  // @skjs-expect-error Unreachable code detected
  return "";
}

// Direct unreachable statements after return / throw / exhaustive if-else:
function unreachableAfterReturn(): number {
  return 1;
  // @skjs-expect-error Unreachable code detected
  return 2;
}

function unreachableAfterThrow(): number {
  throw new Error("boom");
  // @skjs-expect-error Unreachable code detected
  return 1;
}

function unreachableAfterBothBranchesReturn(cond: boolean): number {
  if (cond) {
    return 1;
  } else {
    return 2;
  }
  // @skjs-expect-error Unreachable code detected
  return 3;
}

// Non-exhaustive chain must NOT treat the end as unreachable:
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function nonExhaustiveStillErrors(x: "a" | "b" | "c"): string {
  if (x === "a") {
    return "first";
  } else if (x === "b") {
    return "second";
  }
}

// Non-exhaustive chain with a fallback return: the fallback IS reachable.
function nonExhaustiveWithFallback(x: "a" | "b" | "c"): string {
  if (x === "a") {
    return "first";
  } else if (x === "b") {
    return "second";
  }
  return "third";
}

// Parameter already typed `never` at entry: a condition on `never` must not
// falsely treat branches as newly-contradicted beyond normal narrowing.
function alreadyNeverParam(x: never): string {
  if (x === x) {
    return "a";
  }
  return "b";
}

// Multiple statements in an unreachable tail report TS7027 once (on the first),
// while still type-checking subsequent unreachable statements.
function unreachableTailReportsOnce(): number {
  return 1;
  // @skjs-expect-error Unreachable code detected
  const a = 2;
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const b: string = a;
  return a;
}

// An assignment inside a branch that happens to narrow a local to `never` mid-body
// must NOT retroactively treat the branch entry as unreachable.
function branchNarrowingInsideBodyStillReachesAfter(cond: boolean): number {
  let x: number | string = 1;
  if (cond) {
    if (typeof x === "boolean") {
      const n: never = x;
    }
    x = 2;
  } else {
    return 0;
  }
  // Reachable: `cond === true` falls through.
  return x;
}
