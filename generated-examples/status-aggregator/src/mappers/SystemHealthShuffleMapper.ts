import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Component_skip_id_,
  ComponentStored,
  Component,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each component entry, emit one output pair whose key is the literal zero and whose value is the entry's value unchanged. The original Component.id is dropped: this collection feeds GetSystemHealthResource which aggregates per-status counts across all components and never needs to identify any individual source Component row. This shuffles ALL components under the single literal-zero key.
export class SystemHealthShuffleMapper implements Mapper<
  Component_skip_id_,
  ComponentStored,
  0,
  ComponentStored
> {
  mapEntry(
    key: Component_skip_id_,
    values: Values<ComponentStored>,
    context: Context,
  ): Iterable<[0, ComponentStored]> {
    // > body
    const emits: [0, ComponentStored][] = [];
    for (const value of values.toArray()) {
      emits.push([0, value]);
    }
    return emits;
    // < body
  }
}
