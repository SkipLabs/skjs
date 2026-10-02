// sum.ts's collections: an interface extending the runtime's index signature
// type, its named collections read and merged.
import type { EagerCollection, NamedEagerCollections } from "@skipruntime/core";
interface Collections extends NamedEagerCollections {
  readonly input1: EagerCollection<string, number>;
  readonly input2: EagerCollection<string, number>;
}
export function merged(cs: Collections): EagerCollection<string, number> {
  return cs.input1.merge(cs.input2);
}
