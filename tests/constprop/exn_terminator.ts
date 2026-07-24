// Exceptional flow out of a non-throw terminator: the `return mightThrow()` in
// the try body is a RETURN terminator whose embedded call may throw. When it
// throws, control reaches the catch handler with the pre-terminator environment
// intact — `x` was bound to 5 before the try and the throwing call does not
// touch it, so the handler must see `x = 5`.

function mightThrow(b: boolean): number {
  if (b) {
    throw new Error("boom");
  }
  return 1;
}

function f(b: boolean): number {
  const x = 5;
  try {
    return mightThrow(b);
  } catch (e) {
    return x;
  }
}

const _ = f(true);
