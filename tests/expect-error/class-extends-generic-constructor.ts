// Regression test: inherited constructor from a generic parent class.
// The type-checker must resolve the parent's type parameters when the
// child class does not declare its own constructor.

class StringArray extends Array<string> {}

function testInheritedConstructor(): StringArray {
  return new StringArray();
}

class NumberArray extends Array<number> {}

function testInheritedConstructorNumber(): NumberArray {
  return new NumberArray();
}

class ValueBox<T> {
  value: T;

  // @skjs-expect-error Cannot find type 'T'
  constructor(value: T) {
    this.value = value;
  }
}

class NumberValueBox extends ValueBox<number> {}

function isNumberValueBox(value: unknown): boolean {
  return value instanceof NumberValueBox;
}
