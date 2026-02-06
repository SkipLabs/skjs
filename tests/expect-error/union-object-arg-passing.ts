function acceptsUnionObject(x: { a: number } | { b: number }): void {
  console.log(x);
}

function freshLiteralArgsAreAccepted(): void {
  acceptsUnionObject({ a: 1 });
  acceptsUnionObject({ b: 2 });
  acceptsUnionObject({ a: 1, b: 2 });
}

function matchingWideVariablesAreAccepted(): void {
  let xa: { a: number } = { a: 1 };
  let xb: { b: number } = { b: 2 };
  acceptsUnionObject(xa);
  acceptsUnionObject(xb);
}

function missingOrWrongFieldsAreRejected(): void {
  // @skjs-expect-error Invalid call
  acceptsUnionObject({});
  // @skjs-expect-error Invalid call
  acceptsUnionObject({ a: "x" });
  // @skjs-expect-error Invalid call
  acceptsUnionObject({ b: "x" });
}

function nonFreshNarrowMutableVariableIsRejected(): void {
  const one: 1 = 1;
  let narrow: { a: 1 } = { a: one };
  // @skjs-expect-error Invalid call
  acceptsUnionObject(narrow);
}

function mutateNested(x: { inner: { v: number } }): void {
  x.inner.v = 2;
}

function freshNestedLiteralIsAccepted(): void {
  mutateNested({ inner: { v: 1 } });
}

function nonFreshNestedAliasIsRejected(): void {
  const one: 1 = 1;
  let inner: { v: 1 } = { v: one };
  // @skjs-expect-error Invalid call
  mutateNested({ inner });
}
