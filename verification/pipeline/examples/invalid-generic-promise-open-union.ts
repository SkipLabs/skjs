declare function wrap<T>(value: T): Promise<Awaited<T>>;
type Box = { n: number };

export function openUnion(value: number | Box): Promise<number | Box> {
  return wrap<number | Box>(value);
}
