// `typeof x` of a binding without an annotation is the type TypeScript
// infers for it, which no declaration states.
const origin = { x: 0 };
export function copy(p: typeof origin): number {
  return p.x;
}
