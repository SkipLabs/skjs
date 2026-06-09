export function array<T>(...elts: T[]): Array<T> {
  // @skjs-expect-error Type of returned value is not assignable to the function's return type
  return elts;
}

export function arrayRO<T>(...elts: T[]): ReadonlyArray<T> {
  return elts;
}

export function map<K, V>(...elts: Array<[K, V]>): Map<K, V> {
  return new Map(elts);
}
