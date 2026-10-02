import type { Json } from "@skipruntime/core";

// A writable Json-element view must not widen the contract of an aliased array.
export function aliasWrite(items: boolean[]): boolean | undefined {
  const view: Json[] = items;
  view[0] = "changed";
  return items[0];
}
