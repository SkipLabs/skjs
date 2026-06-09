// For a parameter typed `T extends number | string`, a `typeof x === "number"`
// test narrows x, but the narrowing does not propagate to a second argument y
// of the same type T. So y - x is rejected because y remains of type T.
function adHocEq<T extends number | string>(x: T, y: T): boolean {
  if (typeof x === "number") {
    // @skjs-expect-error This operator requires a numeric operand
    return y - x === 0;
  } else {
    return x === y;
  }
}
