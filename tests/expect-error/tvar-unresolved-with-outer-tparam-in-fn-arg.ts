// Known issue: when a method's bounded type parameter V2 appears in a
// function argument that also references the outer type parameter V
// (e.g. (v: V) => V2), V2 is not resolved to the concrete inferred type.
// Two calls to such a method produce C<'0> and C<'2> with different
// unresolved tvars, so passing one to the other's method fails.

type U_tu = boolean | string;

interface C_tu<V> {
  f<V2 extends U_tu>(x: (v: V) => V2): C_tu<V2>;
  g(other: C_tu<V>): C_tu<V>;
}

function testTvarUnresolved(c: C_tu<string>): C_tu<boolean> {
  const a = c.f((_: string): boolean => true);
  const b = c.f((_: string): boolean => true);
  const r = a.g(b);
  return r;
}
