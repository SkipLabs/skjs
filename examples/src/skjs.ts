export function array<T>(...elts: T[]): Array<T> {
  return elts;
}

export function map<K, V>(...elts: Array<[K, V]>): Map<K, V> {
  return new Map(elts);
}
