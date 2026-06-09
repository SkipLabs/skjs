// Generic type inference too narrow: type variable sealed by usage,
// preventing wider types later.
//
// One test per TVarOrigin variant. For each origin we show either:
// - a negative test (sealed TVar blocks a wider type), or
// - a positive test (TVar stays open, no error).

interface Container<T> {
  push(arg: T): void;
  append(other: Container<T>): void;
  get(): T;
}

// --- FromGenericInst: new Container() ---
// takeContainer seals T=number, then push("hello") fails.
declare function takeContainer(b: Container<number>): void;

function fromGenericInst(): void {
  const c = new Container();
  c.push(1);
  takeContainer(c);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  c.push("hello");
}

// --- FromGenericCall: makeContainer(1) ---
// takeContainer seals T=number, then push("hello") fails.
declare function makeContainer<T>(x: T): Container<T>;

function fromGenericCall(): void {
  const c = makeContainer(1);
  takeContainer(c);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  c.push("hello");
}

// --- FromEmptyArray: [] ---
// Annotation + push seals element type, then push("hello") fails.
declare function takeNumberArray(arr: number[]): void;

function fromEmptyArray(): void {
  const arr: number[] = [];
  arr.push(1);
  takeNumberArray(arr);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  arr.push("hello");
}

// --- FromArrayLiteral: [1, 2, 3] ---
// takeNumberArray commits and seals element type, then push("hello") fails.
function fromArrayLiteral(): void {
  const arr = [1, 2, 3];
  takeNumberArray(arr);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  arr.push("hello");
}

// --- FromNullLiteral: null ---
// Direct null doesn't seal (T stays open and grows).
function fromNullLiteralDirect(): Container<number | null> {
  const c = new Container();
  c.push(null);
  c.push(1);
  return c;
}

// Via local variable: bound TVar seals T=null, push(1) fails.
function fromNullLiteralLocal(): void {
  const c = new Container();
  let n = null;
  c.push(n);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type number
  // @skjs-expect-error-line3 is not assignable to type null
  // @skjs-expect-error-line4 Consider adding explicit type arguments, e.g., <null | number>
  c.push(1);
}

// --- FromUndefinedLiteral: undefined ---
// Direct undefined doesn't seal (T stays open and grows).
function fromUndefinedLiteralDirect(): Container<string | undefined> {
  const c = new Container();
  c.push(undefined);
  c.push("hello");
  return c;
}

// Via local variable: bound TVar seals T=undefined, push("hello") fails.
function fromUndefinedLiteralLocal(): void {
  const c = new Container();
  let u = undefined;
  c.push(u);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type string
  // @skjs-expect-error-line3 is not assignable to type undefined
  // @skjs-expect-error-line4 Consider adding explicit type arguments, e.g., <string | undefined>
  c.push("hello");
}

// --- FromLambdaReturn: () => { return 42; } ---
// takeFnReturningNumber seals return type, then takeFnReturningString fails.
declare function takeFnReturningNumber(f: () => number): void;
declare function takeFnReturningString(f: () => string): void;

function fromLambdaReturn(): void {
  const f = () => {
    return 42;
  };
  takeFnReturningNumber(f);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  takeFnReturningString(f);
}

// --- FromAsyncReturn: async () => { return 42; } ---
// return 42 seals Promise's inner type, then takePromiseString fails.
declare function takePromiseString(p: Promise<string>): void;

function fromAsyncReturn(): void {
  const f = async () => {
    return 42;
  };
  const p = f();
  // @skjs-expect-error Argument is not assignable to the parameter's type
  takePromiseString(p);
}

// --- FromObjectField: { x: 1 } ---
// takeContainerObj seals Container's T, then push({ x: "hello" }) fails.
declare function takeContainerObj(c: Container<{ x: number }>): void;

function fromObjectField(): void {
  const c = new Container();
  c.push({ x: 1 });
  takeContainerObj(c);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  // @skjs-expect-error-line2 Type 'hello'
  // @skjs-expect-error-line3 is not assignable to type number
  // @skjs-expect-error-line4 Type 'hello'
  // @skjs-expect-error-line5 is not assignable to type number
  // @skjs-expect-error-line6 Consider adding a type annotation, e.g., number | 'hello'
  // @skjs-expect-error-line7 Consider adding explicit type arguments, e.g., <{ x: number } | { x: 'hello' } | { x: number }>
  c.push({ x: "hello" });
}

// --- FromArrayElement: [{ x: 1 }, { x: 2 }] ---
// takeObjArray seals Array's element type, then push({ x: "hello" }) fails.
declare function takeObjArray(arr: Array<{ x: number }>): void;

function fromArrayElement(): void {
  const arr = [{ x: 1 }, { x: 2 }];
  takeObjArray(arr);
  // @skjs-expect-error Argument is not assignable to the parameter's type
  arr.push({ x: "hello" });
}

// --- FromSyntheticIndex: object literal with incompatible index signature ---
interface StringMap {
  [key: string]: string;
}

function fromSyntheticIndex(): void {
  // @skjs-expect-error Type of value is not assignable to the variable's type annotation
  const obj: StringMap = { a: 1 };
}

// --- FromUntypedVar: untyped variable declaration (parse error in SKJS) ---
function fromUntypedVar(): void {
  // @skjs-expect-error Was expecting a type or a value
  let x;
  x = 42;
}
