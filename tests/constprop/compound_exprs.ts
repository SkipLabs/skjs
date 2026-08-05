// Calls nested inside expression forms that have no tracked constant value
// (array/object/template literals, `typeof`, indexing, property access) must
// still be resolved interprocedurally: the enclosing expression is `top`, but
// walking into it is what registers the callsite and analyzes the callee.
//
// Each helper below is reachable *only* from such a position, so each one's
// entry state and return value show that the sub-expression was walked.

function inArray(): number {
  return 1;
}

function inTemplate(): number {
  return 2;
}

function inTypeof(): number {
  return 3;
}

function inIndex(): number {
  return 0;
}

function indexed(n: number): number[] {
  return [n];
}

function inObject(): number {
  return 4;
}

function inDot(): number[] {
  return [5];
}

function main(): number {
  const a = [inArray()];
  const s = `${inTemplate()}`;
  const t = typeof inTypeof();
  const g = indexed(6)[inIndex()] ?? 0;
  const o = { f: inObject() };
  const d = inDot().length;
  return a.length + s.length + t.length + g + o.f + d;
}

// Module top-level code is the entrypoint; it invokes main.
const _ = main();
