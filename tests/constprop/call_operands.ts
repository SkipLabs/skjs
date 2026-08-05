// Calls in the operand positions of another call: the arguments, and the
// callee expression itself. Arguments are resolved by `call`, which evaluates
// them to bind the callee's formals (`inNewArg` below flows into `Box`'s `v`).
// A callee expression is bound to no formal, so it is walked by `evalExpr`.
//
// Two known limitations are pinned here rather than fixed:
//
//   - `inCalleeExpr` is `unreachable`: it is only ever referenced as a value
//     (returned by `makeFn` and called indirectly), and `resolveCallees` matches
//     callees syntactically by name, so a function passed around as a value is
//     never resolved. `makeFn` itself is analyzed, since it heads a callsite.
//   - `inOpaqueArg` sits in the argument of an opaque call (`console.log`),
//     which never reaches `call`. It is nonetheless analyzed today, because
//     `resolveCallees` falls back to every callee of the enclosing function when
//     it cannot match one — a fallback that happens to include it.

function inOpaqueArg(): number {
  return 1;
}

function inCalleeExpr(): number {
  return 2;
}

function makeFn(): () => number {
  return inCalleeExpr;
}

function inNewArg(): number {
  return 3;
}

class Box {
  v: number;
  constructor(v: number) {
    this.v = v;
  }
}

function main(): number {
  const a = makeFn()();
  const b = new Box(inNewArg());
  console.log(inOpaqueArg());
  return a + b.v;
}

// Module top-level code is the entrypoint; it invokes main.
const _ = main();
