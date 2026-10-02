import type { Json } from "@skipruntime/core";

export function invalidBound(): Json {
  const accept = <T extends Json>(value: T): Json => value;
  return accept((): boolean => true);
}
