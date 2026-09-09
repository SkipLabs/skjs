"use strict";
// Display-side mirror of SourceTypes.lean. The pipeline regression compares the
// entire table with Lean's output; these labels are never verification evidence.
const primitiveLabels = [0, 1, 2, 75];
const primitiveTypes = Array.from({ length: 16 }, (_, mask) =>
  primitiveLabels.filter((_, bit) => mask & (1 << bit)),
);
const argumentsInOrder = [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
const ref = (A) => [{ refs: { first: A, rest: [] } }];
const refPair = (A, B) => [{ refs: { first: A, rest: [B] } }];
const arrow = (D, R) => [{ arrs: { arrows: [[D, R]] } }];
const old = [
  ["nul"],
  [{ boolLit: { value: true } }],
  [{ boolLit: { value: false } }],
  ...primitiveTypes.slice(0, 8).map(ref),
  ...argumentsInOrder
    .slice(0, 8)
    .flatMap((d) =>
      primitiveTypes.slice(0, 8).map((r) => arrow(primitiveTypes[d], r)),
    ),
];
const existing = new Set(old.map(JSON.stringify));
const compounds = [
  ...primitiveTypes.map(ref),
  ...argumentsInOrder.flatMap((d) =>
    primitiveTypes.map((r) => arrow(primitiveTypes[d], r)),
  ),
  // Last, so every label already in use keeps its index.
  ...primitiveTypes.flatMap((a) => primitiveTypes.map((b) => refPair(a, b))),
];
const types = [
  ...old,
  ["undef"],
  ...compounds.filter((c) => !existing.has(JSON.stringify(c))),
];
const name = "stateful-source-532-v2";
const primitiveNames = new Map([
  [0, "null"],
  [1, "true"],
  [2, "false"],
  [75, "undefined"],
]);
function typeText(A) {
  return A.map(labelText).join(" | ") || "never";
}
function labelText(i) {
  if (primitiveNames.has(i)) return primitiveNames.get(i);
  const c = types[i]?.[0];
  if (c?.refs)
    return [c.refs.first, ...c.refs.rest]
      .map((operand) => `Ref<${typeText(operand)}>`)
      .join(" & ");
  if (c?.arrs) {
    const [D, R] = c.arrs.arrows[0];
    return `(${typeText(D)} => ${typeText(R)})`;
  }
  throw Error("invalid source type label");
}
module.exports = { name, types, primitiveLabels, typeText };
