// With `allowUnreachableCode: true`, unreachable statements do not report
// TS7027, while exhaustive if/else-if termination still applies and unreachable
// statements are still type-checked.

const B = "b";

function exhaustiveWithFallback(x: "a" | "b"): string {
  if (x === "a") {
    return "first";
    // @skjs-expect-warning This comparison is always true because the operands always hold the same single value
  } else if (x === B) {
    return "second";
  }
  return "";
}

function unreachableStillTypeChecked(): number {
  return 1;
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return "not a number";
}
