// `Array.isArray(a)` narrowing. SKJS currently intersects object-union branches
// with a mutable `Array`, so a value that could be a readonly array at runtime
// unsoundly gains `push`/`pop`. A genuine ReadonlyArray and a tuple are already
// kept non-pushable. tsc unsoundly narrows all of these to `any[]`.

function plainMutable(a: number[]): void {
  if (Array.isArray(a)) {
    a.push(1);
  }
}

function mutableUnion(a: number[] | number): void {
  if (Array.isArray(a)) {
    a.push(1);
  }
}

function mutableTuple(a: [number, string]): void {
  if (Array.isArray(a)) {
    // @skjs-expect-error This index key is not assignable to the index signature: expected number, got string
    a.push(1);
  }
}

function readonlyLengthUnion(a: number[] | { readonly length: number }): void {
  if (Array.isArray(a)) {
    // FIXME (issue #709): unsound — `a` may be the non-array branch (a readonly
    // array satisfies `{ readonly length }`), so push must be rejected; SKJS
    // currently accepts it.
    a.push(1);
  }
}

function readonlyArray(a: ReadonlyArray<number>): void {
  if (Array.isArray(a)) {
    // @skjs-expect-error This index key is not assignable to the index signature: expected number, got string
    a.push(1);
  }
}

// A plain object type can be inhabited by a readonly array carrying extra
// properties: `roWithProps` is a readonly array that also satisfies
// `{ a: string; b: number }`, so `attack(roWithProps)` flows it into `x`.
declare const roWithProps: ReadonlyArray<number> & { a: string; b: number };

function attack(x: number[] | { a: string; b: number }): void {
  if (Array.isArray(x)) {
    // FIXME (issue #709): unsound — `x` may be `roWithProps`, a readonly array,
    // so push must be rejected; SKJS currently accepts it.
    x.push(1);
  }
}

function runAttack(): void {
  attack(roWithProps);
}
