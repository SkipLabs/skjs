// A static initializer constructing its own class runs the class's code
// before the class value, which is allocated holding the static fields,
// exists: outside the fragment.
class Point {
  x: number;
  constructor(x: number) {
    this.x = x;
  }
  static readonly origin: Point = new Point(0);
}

export function use(): number {
  return Point.origin.x;
}
