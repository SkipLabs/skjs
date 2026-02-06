class InstanceReadonlyVsMutable {
  readonly ro: number = 1;
  mut: number = 2;
}

function writeInstanceFields(x: InstanceReadonlyVsMutable): void {
  // @skjs-expect-error Invalid assignment
  x.ro = 3;
  x.mut = 4;
}

class StaticReadonlyField {
  static readonly value: number = 42;
}

function writeStaticReadonlyField(): void {
  // @skjs-expect-error Invalid assignment
  StaticReadonlyField.value = 0;
}

function mutableIndexWriteStillAllowed(obj: { [k: string]: number }): void {
  obj["x"] = 1;
  obj.y = 2;
}

function unionSharedFieldWriteRejected(u: { a: number } | { a: string }): void {
  // @skjs-expect-error Invalid assignment
  u.a = 1;
}

function unionSharedFieldWriteAllowedWhenEqual(
  u: { a: number } | { a: number },
): void {
  u.a = 1;
}

function unionDisjointFieldWriteRejected(u: { a: number } | { b: number }): void {
  // @skjs-expect-error Invalid assignment
  u.a = 1;
}

function intersectionSameFieldWriteAllowed(x: { a: number } & { a: number }): void {
  x.a = 1;
}

function readOnlyView(v: { readonly x: number | string }): number | string {
  return v.x;
}

function mutableNarrowPassedToReadonlyWide(): number | string {
  const one: 1 = 1;
  const m: { x: 1 } = { x: one };
  return readOnlyView(m);
}

function writeWide(v: { x: number | string }): void {
  v.x = "s";
}

function mutableNarrowPassedToWritableWideCurrentBehavior(): void {
  const one: 1 = 1;
  const m: { x: 1 } = { x: one };
  // @skjs-expect-error
  writeWide(m);
}
