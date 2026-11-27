// Unreachable code detection (TS7027) and exhaustive if/else-if termination.
//
// Pre-fix pins: currently SKJS neither detects that an `if` branch narrowed
// to `never` is unreachable (so exhaustive `if`/`else if` chains without a
// trailing `else` still require a dummy fallback return), nor reports TS7027
// on statements following a non-falling-through statement.

const B = "b";

// Exhaustive if / else-if chain without a trailing return:
// Currently rejected with TS2366 because `if (x === "b")`'s empty else branch
// is not recognized as unreachable even though `x` narrows to `never` there.
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function exhaustiveLiteralNoFallback(x: "a" | "b"): string {
  if (x === "a") {
    return "first";
  } else if (x === "b") {
    return "second";
  }
}

// Same with a hoisted constant:
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
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
// @skjs-expect-error Not all code paths return a value, and the return type does not include 'undefined'
function exhaustiveFieldNoFallback(x: TaggedAB): string {
  if (x.kind === "a") {
    return "first";
  } else if (x.kind === "b") {
    return "second";
  }
}

// Trailing statement after an exhaustive if / else-if chain:
// Currently accepted silently; with unreachable-code detection enabled, the
// trailing `return ""` is unreachable (TS7027).
function exhaustiveWithUnreachableFallback(x: "a" | "b"): string {
  if (x === "a") {
    return "first";
    // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  } else if (x === B) {
    return "second";
  }
  return "";
}

// Direct unreachable statements after return / throw / exhaustive if-else:
function unreachableAfterReturn(): number {
  return 1;
  return 2;
}

function unreachableAfterThrow(): number {
  throw new Error("boom");
  return 1;
}

function unreachableAfterBothBranchesReturn(cond: boolean): number {
  if (cond) {
    return 1;
  } else {
    return 2;
  }
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
