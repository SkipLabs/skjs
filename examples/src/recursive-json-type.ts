// Test recursive type with generic constraints

// Recursive JSON type definition
type Json = { [key: string]: Json } | number | string;

// Generic function with constraint that extends recursive type
function foo<T extends Json>(x: T): void {}

// Usage with object that satisfies the constraint
// @skjs-expect-error Argument is not assignable to the parameter's type
foo<{ x: number; y: string }>({ x: 0, y: "" });

// Additional test cases
function testJsonUsage(): void {
  // Basic JSON values
  let num: Json = 42;
  let str: Json = "hello";

  // Nested object
  let nested: Json = {
    name: "test",
    value: 123,
    nested: {
      inner: "value",
    },
  };

  // Using with generic function
  foo<number>(42);
  foo<string>("hello");
  // @skjs-expect-error Argument is not assignable to the parameter's type
  foo<{ name: string; age: number }>({ name: "John", age: 30 });
}

// Readonly version

type roJson = { readonly [key: string]: roJson } | number | string;

function rofoo<T extends roJson>(x: T): void {}

rofoo<{ x: number; y: string }>({ x: 0, y: "" });

function testroJsonUsage(): void {
  let num: roJson = 42;
  let str: roJson = "hello";

  let nested: roJson = {
    name: "test",
    value: 123,
    nested: {
      inner: "value",
    },
  };

  rofoo<number>(42);
  rofoo<string>("hello");
  rofoo<{ name: string; age: number }>({ name: "John", age: 30 });
}
