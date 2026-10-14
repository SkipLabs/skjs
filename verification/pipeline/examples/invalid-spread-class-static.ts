// A class value's copy holds its static fields, which a construct signature
// does not state: a class with a static `a` holding a string overwrites the
// field written before it.
export function overStatic(k: new () => object): { a: number } {
  return { a: 1, ...k };
}
