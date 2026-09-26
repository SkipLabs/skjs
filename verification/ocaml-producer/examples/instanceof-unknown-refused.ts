// `x instanceof Point` does not narrow `unknown` to `Point`: that an object
// whose prototype chain holds Point's prototype has Point's fields is a fact
// about every allocation of the program, which no type of a value states.
class Point {
  x: number = 0;
}
export function px(p: unknown): number {
  if (p instanceof Point) {
    return p.x;
  }
  return 0;
}
