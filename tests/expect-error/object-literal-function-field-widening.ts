// A function-valued object-literal field whose body is a literal widens to a
// non-literal declared field type, even though a mutable field is checked
// invariantly. The arrow's literal return type (e.g. () => 'hello') is routed
// through a growable field type variable, like object- and primitive-valued
// fields, so it can grow to the declared () => string.

function stringField(): void {
  const x: { fn: () => string } = { fn: () => "hello" };
}

function numberField(): void {
  const x: { fn: () => number } = { fn: () => 1 };
}

function booleanField(): void {
  const x: { fn: () => boolean } = { fn: () => true };
}

// Widening also reaches function fields nested inside object fields.
function nestedField(): void {
  const x: { o: { fn: () => string } } = { o: { fn: () => "hello" } };
}

// ... an object literal flowing into a parameter ...
function takesField(p: { fn: () => number }): void {}
function passesField(): void {
  takesField({ fn: () => 1 });
}

// ... and into a declared return type.
function returnsField(): { fn: () => string } {
  return { fn: () => "hello" };
}

// A literal field type is preserved exactly when requested.
function literalFieldOk(): void {
  const x: { fn: () => "hello" } = { fn: () => "hello" };
}

// A literal that is not a subtype of the declared literal field type is still
// rejected: widening only grows up to the declared type, never past it.
function literalFieldMismatch(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { fn: () => "hello" } = { fn: () => "world" };
}

// A genuinely wrong return type is still rejected.
function wrongReturnType(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const x: { fn: () => number } = { fn: () => "hello" };
}
