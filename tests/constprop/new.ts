// `new` resolves the constructor interprocedurally: its formals are bound to
// the actual arguments, so the constructor body is analyzed with `a = 3` and
// `b = 4`. The value of the `new` expression itself is the constructed object,
// which is not a tracked primitive, so it is `top`.

class Point {
  x: number;
  y: number;
  constructor(a: number, b: number) {
    this.x = a;
    this.y = b;
  }
}

function main(): number {
  const p = new Point(3, 4);
  return 0;
}
