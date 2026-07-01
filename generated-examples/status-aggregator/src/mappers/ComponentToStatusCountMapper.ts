import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Component_skip_id_,
  Component_skip_value_,
  ComponentStatusKey,
  ComponentStatusCount,
  Component,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each component entry, emit one output pair whose key is sourced from the entry's value's status field (the literal string 'HEALTHY', 'DEGRADED', or 'UNHEALTHY') and whose value is the literal one. The original Component.id is dropped: this mapper aggregates per status bucket and the source component identifier is not needed downstream — the consuming SumReducer sums the literal 1s into per-status counts and never needs to identify the individual Component row that contributed each 1.
export class ComponentToStatusCountMapper implements Mapper<
  Component_skip_id_,
  Component_skip_value_,
  ComponentStatusKey,
  ComponentStatusCount
> {
  mapEntry(
    key: Component_skip_id_,
    values: Values<Component_skip_value_>,
    context: Context,
  ): Iterable<[ComponentStatusKey, ComponentStatusCount]> {
    // > body
    const emits: [ComponentStatusKey, ComponentStatusCount][] = [];
    for (const value of values.toArray()) {
      emits.push([value.status, 1]);
    }
    return emits;
    // < body
  }
}
