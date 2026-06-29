// Constructing an InputDefinition with an initial-data array argument.
//
// The runtime's InputDefinition takes `constructor(initial: Entry<K, V>[] = [])`,
// and skipper-generated services emit `new InputDefinition<K, V>([...])` to seed
// a service's inputs. The argument (and the no-arg form, since the parameter has
// a default) must type-check.

import { InputDefinition } from "@skipruntime/core";

export function makeInputs(): InputDefinition<string, number>[] {
  // @skjs-expect-error This constructor expects no arguments
  const empty = new InputDefinition<string, number>([]);
  // @skjs-expect-error This constructor expects no arguments
  const seeded = new InputDefinition<string, number>([["a", [1, 2]]]);
  const none = new InputDefinition<string, number>();
  return [empty, seeded, none];
}
