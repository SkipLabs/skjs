// Test multiple type errors within a single class

class MultipleErrors {
  // Type mismatch in field
  // @ts-expect-error Invalid assignment
  field1: number = "hello";

  // Type mismatch in another field
  // @ts-expect-error Invalid assignment
  field2: string = 42;

  // Type mismatch in method return
  method(): number {
    // @ts-expect-error Invalid return type
    return "not a number";
  }

  // Type mismatch in another method return
  method2(): string {
    // @ts-expect-error Invalid return type
    return 123;
  }
}

// Test multiple errors across different classes
class AnotherClassWithErrors {
  // @ts-expect-error Invalid assignment
  x: boolean = 5;

  // @ts-expect-error Invalid assignment
  y: number = false;
}
