// `Array.isArray(a)` narrows `a` by intersecting with `ReadonlyArray<unknown>`.
// A genuinely mutable array stays mutable (its writable index survives the
// intersection), but a readonly array, a tuple, or a non-array object — which a
// readonly array can inhabit by carrying extra properties — gets a readonly
// index and cannot be mutated. tsc unsoundly narrows to `any[]` and accepts the
// mutations below.

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

// A mutable tuple has fixed-shape positional fields, not a mutable number
// index, so it is not a provably mutable (variable-length) array: it narrows
// to ReadonlyArray and push is rejected (a tuple's length is fixed). tsc
// unsoundly allows push.
function mutableTuple(a: [number, string]): void {
  if (Array.isArray(a)) {
    // @skjs-expect-error This index key is not assignable to the index signature: expected number, got string
    a.push(1);
  }
}

function readonlyLengthUnion(a: number[] | { readonly length: number }): void {
  if (Array.isArray(a)) {
    // `a` narrows to `number[] | readonly unknown[]`: the non-array branch is
    // not provably a mutable array, so push is rejected. tsc unsoundly
    // narrows to any[] and accepts.
    // @skjs-expect-error Property 'push' exists on some but not all members of the union type, so it may be absent
    a.push(1);
  }
}

function readonlyArray(a: ReadonlyArray<number>): void {
  if (Array.isArray(a)) {
    // tsc unsoundly narrows ReadonlyArray to any[] and accepts; SKJS keeps it
    // readonly and rejects.
    // @skjs-expect-error This index key is not assignable to the index signature: expected number, got string
    a.push(1);
  }
}

// Attack: a plain object type can be inhabited by a readonly array that carries
// extra properties, so `Array.isArray` on an object-union branch must not yield
// a mutable array. Here `roWithProps` is a readonly array that also satisfies
// `{ a: string; b: number }`, so `attack(roWithProps)` flows it into `x`, and
// `x.push` would mutate a readonly array — it must be rejected.
declare const roWithProps: ReadonlyArray<number> & { a: string; b: number };

function attack(x: number[] | { a: string; b: number }): void {
  if (Array.isArray(x)) {
    // @skjs-expect-error Property 'push' exists on some but not all members of the union type, so it may be absent
    x.push(1);
  }
}

function runAttack(): void {
  attack(roWithProps);
}
