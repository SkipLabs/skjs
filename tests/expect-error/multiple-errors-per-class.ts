// Test multiple type errors within a single class

class MultipleErrors {
  // Type mismatch in field
  // @skjs-expect-error Type of field initializer is not assignable to the field's declared type
  field1: number = "hello";

  // Type mismatch in another field
  // @skjs-expect-error Type of field initializer is not assignable to the field's declared type
  field2: string = 42;

  // Type mismatch in method return
  method(): number {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return "not a number";
  }

  // Type mismatch in another method return
  method2(): string {
    // @skjs-expect-error Type of returned value is not assignable to the function's return type
    return 123;
  }
}

// Test multiple errors across different classes
class AnotherClassWithErrors {
  // @skjs-expect-error Type of field initializer is not assignable to the field's declared type
  x: boolean = 5;

  // @skjs-expect-error Type of field initializer is not assignable to the field's declared type
  y: number = false;
}
