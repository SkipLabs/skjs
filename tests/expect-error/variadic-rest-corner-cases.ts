// Corner cases for unified rest-argument handling.
//
// Also valid TypeScript (no top-level lets; all value-level code is inside a function):
//   npx -p typescript tsc --noEmit --strict variadic-rest-corner-cases.ts

// Use `object` (not `{}`) so primitives like `boolean` are rejected.
// In TypeScript, `{}` accepts all non-nullish values, including primitives.
type VariadicDepSafe = string | number | object;

// ------------------------------------------------------------
// 1) Empty-rest inference: T should infer to [] when called with no args
// ------------------------------------------------------------
declare function emptyInfer<T extends readonly unknown[]>(...args: T): T;

// ------------------------------------------------------------
// 2) Tuple-rest exact arity: (...args: [A,B]) requires exactly two args
// ------------------------------------------------------------
declare function tupleRestExact(...args: [string, number]): void;

// ------------------------------------------------------------
// 3) Generic tuple-rest inference from fixed args
// ------------------------------------------------------------
declare function inferTuple<Params extends readonly VariadicDepSafe[]>(
  ...args: Params
): Params;

// ------------------------------------------------------------
// 6) Spread array followed by positional arg: ambiguous positions
// ------------------------------------------------------------
declare function twoArgs(a: string, b: number): void;
declare function threeArgs(a: string, b: number, c: number): void;

// ------------------------------------------------------------
// 7) Motivating pattern: mapper depends on Params inferred from rest args
// ------------------------------------------------------------
interface Collection {
  map<Params extends readonly VariadicDepSafe[]>(
    mapper: new (...params: Params) => { process(): void },
    ...params: Params
  ): void;
}

declare const variadicColl: Collection;

interface PrefixedCollection {
  mapWithPrefix<Params extends readonly VariadicDepSafe[]>(
    prefix: string,
    mapper: new (prefix: string, ...params: Params) => { process(): void },
    ...params: Params
  ): void;
}

declare const prefixedColl: PrefixedCollection;

class One {
  constructor(_p: string) {}
  process(): void {}
}

class Zero {
  constructor() {}
  process(): void {}
}

class Two {
  constructor(_p1: string, _p2: number) {}
  process(): void {}
}

class PrefixOne {
  constructor(_prefix: string, _p1: string) {}
  process(): void {}
}

class PrefixTwo {
  constructor(_prefix: string, _p1: string, _p2: number) {}
  process(): void {}
}

// 0) Optional params before tuple-rest in function subtyping
// Positions must be preserved: (x: string, y?: number, ...args: [boolean]) => void
// means position 0=string, 1=number(optional), 2=boolean.
// A candidate with boolean at position 1 must be rejected.
type OptTupleRestExpected = (x: string, y?: number, ...args: [boolean]) => void;
type OptTupleRestCandidate = (x: string, z: boolean, y?: number) => void;
declare function takesOptTupleRest(cb: OptTupleRestExpected): void;
declare const optTupleRestCandidate: OptTupleRestCandidate;

function testOptionalBeforeTupleRest(): void {
  // @ts-expect-error Invalid call
  takesOptTupleRest(optTupleRestCandidate);
}

// 1) Empty-rest inference
// Assert behavior without relying on user-facing empty tuple annotation syntax.
function testEmptyRestInference(): void {
  const empty0 = emptyInfer();
  const empty0_as_ro_unknown_array: readonly unknown[] = empty0;
}

// 2) Tuple-rest exact arity
function testTupleRestExactArity(): void {
  tupleRestExact("a", 1);
  // @ts-expect-error Invalid call
  tupleRestExact("a");
  // Extra args allowed (consistent with no-rest functions)
  tupleRestExact("a", 1, 2);

  // Unknown-length array spread into concrete tuple rest
  const arr: (string | number)[] = ["a", 1];
  // @ts-expect-error Invalid call. Tuple rest parameters require exact arguments
  tupleRestExact(...arr);
}

// 3) Generic tuple-rest inference from fixed args
function testGenericTupleRestInference(): void {
  const t1 = inferTuple("a", 1);
  // TODO(variadic,readonly-tuples): add readonly back once readonly tuples are supported.
  const t1_as_tuple: [string, number] = t1;

  // Constraint enforcement (DepSafe)
  // @ts-expect-error Invalid call. Inferred rest arguments [boolean] do not satisfy the constraint
  inferTuple(true);
}

// 4) Inference from tuple spread: keeps tuple shape
function testTupleSpreadInference(): void {
  const tup: [string, number] = ["x", 42];
  const t2 = inferTuple(...tup);
  // TODO(variadic,readonly-tuples): add readonly back once readonly tuples are supported.
  const t2_as_tuple: [string, number] = t2;

  // Also works with readonly tuple
  // TODO(variadic,readonly-tuples): add readonly back once readonly tuples are supported.
  const rtup: [string, number] = ["y", 99];
  const t3 = inferTuple(...rtup);
  // TODO(variadic,readonly-tuples): add readonly back once readonly tuples are supported.
  const t3_as_tuple: [string, number] = t3;
}

// 5) Inference from array spread: degrades to array type, not tuple
function testArraySpreadInference(): void {
  const arrS: string[] = ["a", "b"];
  const a1 = inferTuple(...arrS);
  // Both fail: resolving the type variable intersects the binding with the constraint,
  // producing element type string & VariadicDepSafe instead of simplifying to string.
  // @skjs-expect-error Invalid annotation
  const a1_as_tuple: [string, string] = a1;
  // @skjs-expect-error Invalid annotation
  const a1_as_array: readonly string[] = a1;
}

// 6) Spread array followed by positional arg: ambiguous positions
function testSpreadArrayFollowedByPositional(): void {
  const depArr: VariadicDepSafe[] = ["a", 1];
  // @ts-expect-error Invalid call
  twoArgs(...depArr, 2);
}

// 6b) Tuple spread followed by positional arg: keeps positional shape
function testTupleSpreadFollowedByPositional(): void {
  const depTuple: [string, number] = ["a", 1];
  threeArgs(...depTuple, 2);
}

// 7) Motivating API
function testMotivatingAPI(): void {
  variadicColl.map(Zero);
  variadicColl.map(One, "hello");
  variadicColl.map(Two, "hello", 42);
  // @ts-expect-error Invalid call
  variadicColl.map(Two, "hello");
  // @ts-expect-error Invalid call. Inferred rest arguments [boolean] do not satisfy the constraint
  variadicColl.map(One, true);

  // Tuple spread into the rest args should preserve shape
  const args2: [string, number] = ["z", 7];
  variadicColl.map(Two, ...args2);

  const argsArr: VariadicDepSafe[] = ["z", 7];
  // @skjs-expect-error Invalid call
  variadicColl.map(Two, ...argsArr);

  // Mixed fixed + tuple-rest constructor pattern
  prefixedColl.mapWithPrefix("tag", PrefixOne, "hello");
  prefixedColl.mapWithPrefix("tag", PrefixTwo, "hello", 42);
  // @ts-expect-error Invalid call
  prefixedColl.mapWithPrefix("tag", PrefixTwo, "hello");
  // @ts-expect-error Invalid call. Inferred rest arguments [boolean] do not satisfy the constraint
  prefixedColl.mapWithPrefix("tag", PrefixOne, true);
}

// ------------------------------------------------------------
// 8) Type alias expanding to tuple used as spread param
// ------------------------------------------------------------
type MyPair = [string, number];
declare function takePair(...args: MyPair): void;

function testTypeAliasTupleSpread(): void {
  takePair("hello", 42);

  // @ts-expect-error Invalid argument
  takePair(42, "hello");
}

// ------------------------------------------------------------
// 9) Generic tuple constraint in function subtyping
// ------------------------------------------------------------
declare const genericTupleConstraintSrc: <U extends [string, number]>(
  a: string,
  b: number,
) => void;

function testGenericTupleConstraint(): void {
  const tgt: <T extends [string, number]>(...args: T) => void =
    genericTupleConstraintSrc;
}
