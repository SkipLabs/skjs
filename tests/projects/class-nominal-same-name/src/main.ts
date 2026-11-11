// Two classes with the same name in different modules are different classes.
import { Pt as PtA } from "./a.js";
import { Pt as PtB } from "./b.js";

function crossModule(a: PtA): PtB {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return a;
}

// No value is an instance of two unrelated classes, so an instance of one is
// not an instance of their intersection.
function intoIntersection(a: PtA): PtA & PtB {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return a;
}

function sameClass(a: PtA): PtA {
  return a;
}
