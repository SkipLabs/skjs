// The contents of a cell are stated only as primitive values: that a `let`
// without an initializer holding an object was assigned on every path is
// not stated.
type Point = { x: number; y: number };

export function pick(b: boolean): Point {
  let p: Point;
  if (b) {
    p = { x: 1, y: 2 };
  } else {
    p = { x: 0, y: 0 };
  }
  return p;
}
