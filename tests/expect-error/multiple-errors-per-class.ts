// Test that multiple errors per class are now reported

class MultipleErrors {
  // Error 1: Type mismatch in field
  // @ts-expect-error Invalid assignment
  field1: number = "hello";

  // Error 2: Type mismatch in another field
  // @ts-expect-error Invalid assignment
  field2: string = 42;

  // Error 3: Type mismatch in method
  method(): number {
    // @ts-expect-error Invalid return type
    return "not a number";
  }

  // Error 4: Another type mismatch in different method
  method2(): string {
    // @ts-expect-error Invalid return type
    return 123;
  }
}

// Test that errors in different classes are also reported
class AnotherClassWithErrors {
  // @ts-expect-error Invalid assignment
  x: boolean = 5;

  // @ts-expect-error Invalid assignment
  y: number = false;
}
