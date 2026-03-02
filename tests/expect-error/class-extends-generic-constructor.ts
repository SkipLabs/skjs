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
