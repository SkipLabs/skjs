function reversedBound(flag: boolean): boolean {
  const pick = <U, T extends U>(first: U, second: T): U => second;
  return pick(true, flag);
}
