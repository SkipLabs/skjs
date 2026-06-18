// A mutable object-literal field is checked invariantly. A function-valued
// field whose arrow body is a literal is inferred with a literal return type
// (e.g. () => 'hello'), which is not equal to a non-literal declared field type
// (e.g. () => string), so the assignment is rejected. (Object- and
// primitive-valued fields widen in this position; function-valued fields do
// not.)

function stringField(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { fn: () => string } = { fn: () => "hello" };
}

function numberField(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { fn: () => number } = { fn: () => 1 };
}

function booleanField(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { fn: () => boolean } = { fn: () => true };
}

// The rejection also reaches function fields nested inside object fields.
function nestedField(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { o: { fn: () => string } } = { o: { fn: () => "hello" } };
}

// ... an object literal flowing into a parameter ...
function takesField(p: { fn: () => number }): void {}
function passesField(): void {
  // @skjs-expect-error Argument is not assignable to the parameter's type
  takesField({ fn: () => 1 });
}

// ... and into a declared return type.
function returnsField(): { fn: () => string } {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return { fn: () => "hello" };
}

// A literal field type is preserved exactly when requested.
function literalFieldOk(): void {
  const x: { fn: () => "hello" } = { fn: () => "hello" };
}

// A literal that is not a subtype of the declared literal field type is
// rejected: the inferred 'world' is not 'hello'.
function literalFieldMismatch(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { fn: () => "hello" } = { fn: () => "world" };
}

// A genuinely wrong return type is rejected.
function wrongReturnType(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { fn: () => number } = { fn: () => "hello" };
}
