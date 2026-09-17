function literalRead(seed: number): number | undefined {
  const values = [seed];
  return values[0];
}
function tupleFirst(source: [number, string]): number {
  return source[0];
}
function unionTuple(source: [number] | [number, string]): number {
  return source[0];
}
function indexed(items: number[], i: number): number | undefined {
  return items[i];
}
function lengthOf(items: number[]): number {
  return items.length;
}
function writeElem(items: number[]): number | undefined {
  items[1] = 5;
  return items[1];
}
function readonlyArr(items: readonly number[]): number | undefined {
  return items[0];
}
function declaredPrefix(source: [number, string]): string {
  const [count, label] = source;
  return count === 0 ? "" : label;
}
function inferredDefault(source: number[]): number {
  const [first = 0] = source;
  return first;
}
function assignedPrefix(source: [number, number]): number {
  let a = 0;
  let b = 0;
  [a, b] = source;
  return a + b;
}
function assignedDefault(values: number[]): number {
  let value = 1;
  [value = 0] = values;
  return value;
}

function readonlyCovariant(items: number[]): readonly (number | string)[] {
  return items;
}
function readonlyTupleCovariant(items: [number]): readonly [number | string] {
  return items;
}
function freshPattern(seed: number): number {
  const [value = 0] = [seed];
  return value;
}
function negativeKey(items: number[]): number | undefined {
  return items[0 - 1];
}
function fractionalKey(items: number[]): number | undefined {
  return items[0.5];
}
function aliasGrowth(items: number[]): number {
  const alias = items;
  items[3] = 1;
  return alias.length;
}
