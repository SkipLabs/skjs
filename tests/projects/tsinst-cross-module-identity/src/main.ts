// Regression pins for #758 and #759:
// - Distinct generic types sharing the same name and arity across modules
//   must never be conflated during subtyping (including when type arguments
//   are open/bound inference variables or recursive TSInst mentions).
// - Same-declaration generic references across modules (imported, aliased,
//   or global Promise<T>) must remain compatible and handle recursive types.

import { makeBoxA, makeCellA, makeNode } from "./a.js";
import type { Box as BoxA, Node } from "./a.js";
import { takeBoxB, takeCellB } from "./b.js";
import type { Box as BoxB } from "./b.js";
import type { SharedNode } from "./reexport.js";

// Direct comparison of two distinct same-named generic interfaces.
function distinctGenericDirect(x: BoxA<number>): BoxB<number> {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// Inference-variable argument (`Box<tvar> <: Box<number>`) across two distinct
// same-named generic declarations — the exact shape targeted by #758.
function distinctGenericThroughTVar(): number {
  const n: number = 1;
  const box = makeBoxA(n);
  // @ts-expect-error Argument is not assignable to the parameter's type
  return takeBoxB(box);
}

// Recursive self-reference (`box.self()` returns `Box<tvar>` as a TSInst).
function distinctGenericRecursiveMethod(): number {
  const n: number = 1;
  const box = makeBoxA(n);
  const s = box.self();
  // @ts-expect-error Argument is not assignable to the parameter's type
  return takeBoxB(s);
}

// Same-named generic classes across modules with an inferred type argument
// (`Cell<tvar> <: Cell<number>`).
function distinctGenericClassThroughTVar(): number {
  const n: number = 1;
  const cell = makeCellA(n);
  // @ts-expect-error Argument is not assignable to the parameter's type
  return takeCellB(cell);
}

// Cross-module same-declaration generic references (imported + re-exported alias)
// with both concrete and inferred type arguments must be accepted.
function sameDeclarationCrossModule(x: SharedNode<number>): Node<number> {
  return x;
}

function sameDeclarationInferred(): SharedNode<number> {
  const n: number = 1;
  return makeNode(n);
}

function sameDeclarationMismatch(x: SharedNode<string>): Node<number> {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return x;
}

// Builtin cross-file generic (`Promise<T>` referenced from stub and user code).
function crossFilePromiseInferred(): Promise<number> {
  return Promise.resolve(42);
}

function crossFilePromiseMismatch(): Promise<string> {
  // @ts-expect-error Type of returned value is not assignable to the function's return type
  return Promise.resolve(42);
}
