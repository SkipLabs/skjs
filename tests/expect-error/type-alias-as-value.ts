// A type alias is type-only: it has no value binding, so using its name as a
// value is rejected (tsc TS2693). The name exists, so "Cannot find name" is the
// wrong diagnostic.

type Alias = { a: number };

function valueRead(): void {
  // @ts-expect-error 'Alias' only refers to a type, but is being used as a value here
  const x = Alias;
  const _y = x;
}

function newAlias(): Alias {
  // @ts-expect-error 'Alias' only refers to a type, but is being used as a value here
  return new Alias();
}

function instanceofAlias(u: unknown): boolean {
  // @ts-expect-error 'Alias' only refers to a type, but is being used as a value here
  return u instanceof Alias;
}

// @ts-expect-error 'Alias' only refers to a type, but is being used as a value here
function typeofAlias(v: typeof Alias): void {
  const _x = v;
}

// A name merged with a value declaration resolves the value, so value uses of
// the name are legal.
type Merged = { a: number };
declare const Merged: { b: number };

function mergedValueRead(): number {
  return Merged.b;
}

function mergedTypeof(v: typeof Merged): number {
  return v.b;
}
