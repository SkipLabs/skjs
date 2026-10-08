export function back<T extends number>(value: Awaited<T>): T {
  return value;
}
