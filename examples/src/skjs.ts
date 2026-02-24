export function array<T>(...elts: T[]): Array<T> {
  // @skjs-expect-error Invalid return type
  return elts;
}

export function arrayRO<T>(...elts: T[]): ReadonlyArray<T> {
  return elts;
}

export function map<K, V>(...elts: Array<[K, V]>): Map<K, V> {
  return new Map(elts);
}
