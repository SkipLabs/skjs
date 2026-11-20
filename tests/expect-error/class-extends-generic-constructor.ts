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

  constructor(value: T) {
    this.value = value;
  }
}

class NumberValueBox extends ValueBox<number> {}

function isNumberValueBox(value: unknown): boolean {
  return value instanceof NumberValueBox;
}

function constructThroughValue(): NumberValueBox {
  const C = NumberValueBox;
  return new C(1);
}

function rejectWrongInheritedArgument(): void {
  const C = NumberValueBox;
  // @ts-expect-error Argument is not assignable to the parameter's type
  const value = new C("x");
}

class NestedValueBox<T> extends ValueBox<T[]> {}

function constructGenericThroughValue(): number[] {
  const C = NestedValueBox;
  return new C<number>([1]).value;
}
