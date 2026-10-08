declare function wrap<T>(value: T): Promise<Awaited<T>>;
type Box = { n: number };

export function openNative(value: Promise<Box>): Promise<Box> {
  return wrap<Promise<Box>>(value);
}
