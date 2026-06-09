// Test static readonly field with number type
class StaticReadonlyNumber {
  static readonly num: number = 42;
}

// Test static readonly field with string type
class StaticReadonlyString {
  static readonly str: string = "hello";
}

// Test static readonly field with boolean type
class StaticReadonlyBoolean {
  static readonly bool: boolean = true;
}

// Test static readonly field with bigint type
class StaticReadonlyBigint {
  static readonly bigintVal: bigint = 123n;
}

// Test static readonly field with symbol type
class StaticReadonlySymbol {
  static readonly sym: symbol = Symbol.for("test");
}

// Test static field without readonly modifier (should error: must be readonly)
class StaticWithoutReadonly {
  // @skjs-expect-error A static field must be marked 'readonly'
  static num: number = 42;
}

// Test static readonly without initialization (should error: missing definition)
class StaticReadonlyNoInit {
  // @skjs-expect-error Missing definition
  static readonly num: number;
}

// Test static readonly without type annotation (infers from literal)
class StaticReadonlyNoType {
  static readonly num = 42;
}

// Test static readonly with optional modifier (should error: static fields cannot be optional)
class StaticReadonlyOptional {
  // @skjs-expect-error A static field cannot be optional
  static readonly optField?: number = 42;
}

// Test accessing static fields
class AccessStaticFields {
  static readonly value: number = 100;
}

function testAccess(): void {
  const x: number = AccessStaticFields.value;
}
