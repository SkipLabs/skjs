import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  AvailabilityWindowKey,
  AvailabilityWindowStored,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each availability window entry, emit the entry unchanged when the entry's key's resourceId field equals the resourceId param. Otherwise emit nothing.
export class FilterAvailabilityByResourceMapper implements Mapper<
  AvailabilityWindowKey,
  AvailabilityWindowStored,
  AvailabilityWindowKey,
  AvailabilityWindowStored
> {
  constructor(private resourceId: string) {}

  mapEntry(
    key: AvailabilityWindowKey,
    values: Values<AvailabilityWindowStored>,
    context: Context,
  ): Iterable<[AvailabilityWindowKey, AvailabilityWindowStored]> {
    // > body
    if (key.resourceId !== this.resourceId) return [];
    const emits: [AvailabilityWindowKey, AvailabilityWindowStored][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
