// Test: Generic class with recursive union type constraint.
//
// When a class has type parameter `V extends U` where U is a union type,
// instantiating with a type that matches any branch of U should succeed.

import { Json } from "@skipruntime/core";

class Wrapper<V extends Json> {
  items: Array<V>;
  constructor(items: Array<V>) {
    this.items = items;
  }
}

// string satisfies Json (matches the first branch of the union).
function testString(items: Array<string>): Wrapper<string> {
  return new Wrapper<string>(items);
}

// number satisfies Json.
function testNumber(items: Array<number>): Wrapper<number> {
  return new Wrapper<number>(items);
}

function testExtendsJson<T extends Json>(x: T): Json {
  return x;
}

// A specific object type is a subtype of Json.
function callTestObject(): Json {
  return testExtendsJson({ name: "hello", value: 42 });
}

// A specific array type is a subtype of Json.
function callTestArray(): Json {
  return testExtendsJson([1, 2, 3]);
}

// A readonly array type is also a subtype of Json.
function callTestReadonlyArray(): Json {
  const arr: ReadonlyArray<number> = [1, 2, 3];
  return testExtendsJson(arr);
}
