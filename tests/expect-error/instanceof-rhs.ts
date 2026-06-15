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
  // @skjs-expect-error Cannot find type 'fn'
  return x instanceof fn;
}

declare const Alias: typeof C;

function instanceofClassAlias(x: unknown): boolean {
  // @skjs-expect-error Cannot find type 'Alias'
  return x instanceof Alias;
}

declare const Ctor: { new (): { a: number } };

function instanceofConstructSignature(x: unknown): boolean {
  // @skjs-expect-error Cannot find type 'Ctor'
  return x instanceof Ctor;
}

function instanceofExpression(x: unknown, cond: boolean): boolean {
  // @skjs-expect-error The 'instanceof' operator is not supported by SKJS
  return x instanceof (cond ? C : C);
}

declare const n: number;

function instanceofNumber(x: unknown): boolean {
  // @skjs-expect-error Cannot find type 'n'
  return x instanceof n;
}

declare const o: { a: number };

function instanceofPlainObject(x: unknown): boolean {
  // @skjs-expect-error Cannot find type 'o'
  return x instanceof o;
}

interface Merged {
  a: number;
}
declare const Merged: number;

function instanceofNonConstructableMerge(x: unknown): boolean {
  // FIXME: tsc rejects with TS2359; SKJS accepts instanceof on an interface
  // merged with a non-constructable value (issue #697)
  return x instanceof Merged;
}
