function id<T>(x: T): T {
  return x;
}
function infer(): boolean {
  const y = id(true);
  return y;
}
