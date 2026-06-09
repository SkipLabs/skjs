// Tuples are subtypes of `Iterable<U>` (where U is the union of element types),
// inherited via the synthesized `SKJS_TupleN` → `SKJS_Tuple<U>` /
// `SKJS_ReadonlyTuple<U>` → `ReadonlyArray<U>` → `Iterable<U>` chain.

// Homogeneous tuple: `[number, number]` <: `Iterable<number>`.
function homogeneousTupleAsIterable(): void {
  const t: [number, number] = [1, 2];
  const it: Iterable<number> = t;
  void it;
}

// Heterogeneous tuple: element type is the union of positions.
function heterogeneousTupleAsIterable(): void {
  const t: [number, string, boolean] = [1, "a", true];
  const it: Iterable<number | string | boolean> = t;
  void it;
}

// Wrong element type: `[number, number]` is NOT `Iterable<string>`.
function wrongElementType(): void {
  const t: [number, number] = [1, 2];
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const it: Iterable<string> = t;
  void it;
}

// Generic function expecting `Iterable<T>` accepts a tuple, inferring T as the
// element union.
function takesIterable<T>(x: Iterable<T>): void {
  void x;
}
function tupleAcceptedByGenericIterable(): void {
  const t: [number, string] = [1, "a"];
  takesIterable<number | string>(t);
}

// `for...of` works on a tuple via the inherited iterator. The loop variable
// is typed as the element union.
function forOfOverTuple(): number {
  const t: [number, string] = [1, "a"];
  let acc: number = 0;
  for (const x of t) {
    if (typeof x === "number") acc = acc + x;
  }
  return acc;
}
