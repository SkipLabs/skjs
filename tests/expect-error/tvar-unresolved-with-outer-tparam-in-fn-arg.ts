type U_tu = boolean | string;

interface C_tu<V> {
  f<V2 extends U_tu>(x: (v: V) => V2): C_tu<V2>;
  g(other: C_tu<V>): C_tu<V>;
}

function testTvarUnresolved(c: C_tu<string>): C_tu<boolean> {
  const a = c.f((_: string): boolean => true);
  const b = c.f((_: string): boolean => true);
  return a.g(b);
}
