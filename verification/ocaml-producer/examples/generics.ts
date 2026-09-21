function identity<T>(value: T): T {
  const saved: T = value;
  return saved;
}
function bounded<T extends boolean>(value: T): boolean {
  return value;
}
