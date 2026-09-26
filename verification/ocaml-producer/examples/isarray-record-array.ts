// A record or dictionary type is of objects meeting the realm's array
// invariant: one owning an array's store is a dense array holding
// `Array.prototype` and owning no key it provides. So where `Array.isArray`
// holds, a record arm is `readonly unknown[]`, and an array arm keeps its
// own type.
type Foo = { a: string; b: number };

export function elements(x: number[] | Foo): readonly unknown[] {
  if (Array.isArray(x)) return x;
  return [];
}

export function length(x: number[] | Foo): number {
  if (Array.isArray(x)) {
    return x.length;
  }
  return 0;
}

export function dictionary(
  x: { [k: string]: number } | string,
): readonly unknown[] {
  if (typeof x === "string") return [];
  if (!Array.isArray(x)) return [];
  return x;
}
