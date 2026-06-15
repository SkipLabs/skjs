// The right-hand side of `instanceof` must be a value that is constructable or
// callable (a class, function, or other Function-like value); otherwise the
// expression throws a TypeError at runtime and tsc reports TS2359.

class C {
  a: number = 1;
}

function instanceofClass(x: unknown): boolean {
  return x instanceof C;
}

declare function fn(): void;

function instanceofFunction(x: unknown): boolean {
  return x instanceof fn;
}

declare const Alias: typeof C;

function instanceofClassAlias(x: unknown): boolean {
  return x instanceof Alias;
}

declare const Ctor: { new (): { a: number } };

function instanceofConstructSignature(x: unknown): boolean {
  return x instanceof Ctor;
}

function instanceofExpression(x: unknown, cond: boolean): boolean {
  return x instanceof (cond ? C : C);
}

declare const n: number;

function instanceofNumber(x: unknown): boolean {
  // @ts-expect-error The right-hand side of an 'instanceof' expression must be either of type 'any', a class, function, or other type assignable to the 'Function' interface type, or an object type with a 'Symbol.hasInstance' method.
  return x instanceof n;
}

declare const o: { a: number };

function instanceofPlainObject(x: unknown): boolean {
  // @ts-expect-error The right-hand side of an 'instanceof' expression must be either of type 'any', a class, function, or other type assignable to the 'Function' interface type, or an object type with a 'Symbol.hasInstance' method.
  return x instanceof o;
}

interface Merged {
  a: number;
}
declare const Merged: number;

function instanceofNonConstructableMerge(x: unknown): boolean {
  // @ts-expect-error The right-hand side of an 'instanceof' expression must be either of type 'any', a class, function, or other type assignable to the 'Function' interface type, or an object type with a 'Symbol.hasInstance' method.
  return x instanceof Merged;
}
