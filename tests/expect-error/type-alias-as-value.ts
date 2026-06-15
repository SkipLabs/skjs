// A type alias is type-only: it has no value binding, so using its name as a
// value is rejected (tsc TS2693). The name exists, so "Cannot find name" is the
// wrong diagnostic.

type Alias = { a: number };

function valueRead(): void {
  // FIXME: tsc rejects with TS2693; SKJS reports "Cannot find name" (issue #699)
  // @skjs-expect-error Cannot find name
  const x = Alias;
  const _y = x;
}

function newAlias(): Alias {
  // FIXME: tsc rejects with TS2693; SKJS reports "Cannot find name" (issue #699)
  // @skjs-expect-error Cannot find name
  return new Alias();
}

function instanceofAlias(u: unknown): boolean {
  // FIXME: tsc rejects with TS2693; SKJS reports "Cannot find name" (issue #699)
  // @skjs-expect-error Cannot find name
  return u instanceof Alias;
}

// FIXME: tsc rejects with TS2693; SKJS reports "Cannot find name" (issue #699)
// @skjs-expect-error Cannot find name 'Alias'
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
