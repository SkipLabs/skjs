// Test 1: Literal type widening through call context
function takesStringFn(f: () => string): string {
  return f();
}
function testLiteralWidening(): string {
  return takesStringFn(() => "hello");
}

// Test 2: Generic return type inference
function identity<T>(f: () => T): T {
  return f();
}
function testGenericReturn(): string {
  return identity(() => "hello");
}

// Test 3: Union return narrowed by context
function takesNarrow(f: () => number): number {
  return f();
}
function testUnionReturn(x: boolean): number {
  return takesNarrow(() => (x ? 1 : 2));
}

// Test 4: Callback in generic position
function mapArr<T, U>(arr: Array<T>, f: (x: T) => U): Array<U> {
  return arr.map(f);
}
function testMapCallback(): Array<number> {
  return mapArr([1, 2, 3], (x: number) => x + 1);
}

// Test 5: Nested callbacks
function compose<A, B, C>(f: (a: A) => B, g: (b: B) => C): (a: A) => C {
  return (a: A) => g(f(a));
}
function testCompose(): (a: number) => string {
  return compose(
    (x: number) => x + 1,
    (y: number) => String(y),
  );
}

// Test 6: Object literal return
function takesObjFn(f: () => { x: number }): { x: number } {
  return f();
}
function testObjReturn(): { x: number } {
  return takesObjFn(() => ({ x: 42 }));
}
