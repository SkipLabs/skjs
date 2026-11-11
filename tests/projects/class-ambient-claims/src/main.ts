import { Amb } from "./lib.js";

// An array carrying the members inhabits the structural Amb, so the
// Array.isArray branch is reachable and must not narrow to never.
function arrayIntoAmbient(xs: number[] & { a: number }): string {
  const c: Amb = xs;
  if (Array.isArray(c)) {
    const n: never = c;
    return n;
  }
  return "";
}

// Same for a function carrying the members and typeof "function".
function functionIntoAmbient(g: (() => void) & { a: number }): string {
  const o: { a: number } = g;
  const c: Amb = o;
  if (typeof c === "function") {
    const n: never = c;
    return n;
  }
  return "";
}
