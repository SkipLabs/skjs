// Test recursive type with generic constraints, mirroring the SkipRuntime
// `Json` type (`@skipruntime/core`): a readonly, nullable JSON tree.

// Recursive JSON type definition, matching SkipRuntime's `Json`/`JsonObject`.
type Json = boolean | number | string | readonly (Json | null)[] | JsonObject;

type JsonObject = { readonly [key: string]: Json | null };

// Generic function with constraint that extends the recursive type
function foo<T extends Json>(x: T): void {}

// Each primitive member of the union satisfies the constraint.
foo<boolean>(true);
foo<number>(42);
foo<string>("hello");

// A readonly array of nullable Json satisfies the array member.
foo<readonly (Json | null)[]>([1, "two", null]);

// An object type without an index signature is not a subtype of one: an absent
// key would read as undefined, which is not in the value type `Json | null`, so
// skjs soundly rejects it. tsc accepts it (unsound without
// noUncheckedIndexedAccess).
// @skjs-expect-error Type argument does not satisfy the constraint
foo<{ x: number; y: string }>({ x: 0, y: "" });

// Additional test cases
function testJsonUsage(): void {
  // Basic JSON values
  let bool: Json = true;
  let num: Json = 42;
  let str: Json = "hello";

  // Array of nullable Json
  let arr: Json = [1, "two", null];

  // Nested object
  let nested: Json = {
    name: "test",
    value: 123,
    nested: {
      inner: "value",
    },
  };

  // Using with generic function
  foo<boolean>(true);
  foo<number>(42);
  foo<string>("hello");
  // @skjs-expect-error Type argument does not satisfy the constraint
  foo<{ name: string; age: number }>({ name: "John", age: 30 });
}
