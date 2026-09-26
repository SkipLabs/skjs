// A record or dictionary type is of objects meeting the realm's array
// invariant: one owning an array's store holds `Array.prototype` and owns
// no key it provides. Array.isArray does not establish density. These safe
// returns remain a completeness gap while source readonly unknown[] means
// dense; the length operation needs no density guarantee.
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
