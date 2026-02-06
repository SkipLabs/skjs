function constrainedId<T extends { a: number } | { b: number }>(x: T): T {
  return x;
}

function validConstraintCalls(): void {
  constrainedId({ a: 1 });
  constrainedId({ b: 2 });
  constrainedId({ a: 1, b: 2 });
}

function invalidConstraintCalls(): void {
  // @skjs-expect-error Invalid call
  constrainedId({});
  // @skjs-expect-error Invalid call
  constrainedId({ c: 1 });
  // @skjs-expect-error Invalid call
  constrainedId({ a: "x" });
}
