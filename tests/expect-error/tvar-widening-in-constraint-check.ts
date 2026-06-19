// Regression test: SKJS accepts this program, matching tsc.
//
// A type variable inferred from a generic call (a = id_tw("hello") => '0,
// solved to "hello") must not be widened to its bound when passed to a second
// generic function whose type parameter has an `extends` constraint
// (check_tw<Y extends U_tw>). The constraint check in growTVars is speculative
// w.r.t. the candidate: it decides isSub('0, U_tw) but does not keep the seal of
// '0, so b stays "hello" and the return is assignable to string. The check still
// commits deferred literal form (object fields, array shape), so object/array
// arguments against a constraint are unaffected. See #520.

import { Json } from "@skipruntime/core";

type U_tw = boolean | string;

function id_tw<X>(x: X): X {
  return x;
}
function check_tw<Y extends U_tw>(x: Y): Y {
  return x;
}
function checkJson_tw<Y extends Json>(x: Y): Y {
  return x;
}

function testTvarWidening(): string {
  const a = id_tw("hello");
  const b = check_tw(a);
  return b;
}

function testObjectFieldTvarWidening(): string {
  const a = id_tw("hello");
  const b = checkJson_tw({ x: a });
  return b.x;
}
