// Test: Generic class with recursive union type constraint.
//
// When a class has type parameter `V extends U` where U is a union type,
// instantiating with a type that matches any branch of U should succeed.

type Json = string | number | boolean | null | Json[] | { [key: string]: Json };

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
