// Regression test: a type variable inferred from a generic call should not
// be widened to its bound when passed to another generic function with an
// extends constraint.  Previously the constraint check isSub('0, U) had
// side-effects that widened '0 from "hello" to boolean | string.

type U_tw = boolean | string;

function id_tw<X>(x: X): X {
  return x;
}
function check_tw<Y extends U_tw>(x: Y): Y {
  return x;
}

function testTvarWidening(): string {
  const a = id_tw("hello");
  const b = check_tw(a);
  return b;
}
