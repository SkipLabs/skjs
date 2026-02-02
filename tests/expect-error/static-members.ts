// Test static readonly field with number type (should work after implementation)
class StaticReadonlyNumber {
  // @skjs-expect-error static fields are forbidden
  static readonly num: number = 42;
}

// Test static readonly field with string type (should work after implementation)
class StaticReadonlyString {
  // @skjs-expect-error static fields are forbidden
  static readonly str: string = "hello";
}

// Test static readonly field with boolean type (should work after implementation)
class StaticReadonlyBoolean {
  // @skjs-expect-error static fields are forbidden
  static readonly bool: boolean = true;
}

// Test static readonly field with bigint type (should work after implementation)
class StaticReadonlyBigint {
  // @skjs-expect-error static fields are forbidden
  static readonly bigintVal: bigint = 123n;
}

// Test static readonly field with symbol type (should work after implementation)
class StaticReadonlySymbol {
  // @skjs-expect-error static fields are forbidden
  // @skjs-expect-error Type symbol not found
  static readonly sym: symbol = Symbol.for("test");
}

// Test static field without readonly modifier (should error: must be readonly)
class StaticWithoutReadonly {
  // @skjs-expect-error static fields are forbidden
  static num: number = 42;
}

// Test static readonly without initialization (should error: missing definition)
class StaticReadonlyNoInit {
  // @skjs-expect-error static fields are forbidden
  // @skjs-expect-error Uninitialized field
  static readonly num: number;
}

// Test static readonly without type annotation (should error: missing type annotation)
class StaticReadonlyNoType {
  // @skjs-expect-error static fields are forbidden
  // @skjs-expect-error Type annotation expected
  static readonly num = 42;
}

// Test accessing static fields
class AccessStaticFields {
  // @skjs-expect-error static fields are forbidden
  static readonly value: number = 100;
}

function testAccess(): void {
  const x: number = AccessStaticFields.value;
}
