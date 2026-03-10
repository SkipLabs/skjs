// Known issue (false positive): SKJS rejects this program, but tsc accepts it.
//
// A type variable inferred from a generic call (a = id_tw("hello") => '0,
// solved to "hello") is widened to its bound when passed to a second generic
// function whose type parameter has an `extends` constraint
// (check_tw<Y extends U_tw>). Inside growTVars, the constraint check
// isSub('0, U_tw) grows '0 from "hello" to boolean | string by union, and that
// side-effect leaks into the grow, so b is typed boolean | string and the
// return is reported as not assignable to string.
//
// PR #520 fixed the analogous bug in the pre-refactor three-site subtyping code
// by always restoring the subst after the constraint check. That does not port
// to the refactored single-site growTVars: there the constraint check's
// side-effects also commit object/array-literal form against the bound, which
// growUncovered relies on, so an unconditional restore regresses those cases
// (e.g. tests/expect-error/generic-class-union-constraint.ts). A correct fix
// must suppress only the value-tvar widening. See #520 and #528.

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
  // FIXME: remove this annotation once the widening is fixed; tsc accepts this.
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return b;
}
