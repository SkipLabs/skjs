import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { ApiKey_skip_id_, UsageEvent, ApiKey } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the key: when the entry's key does not equal the keyId param, emit nothing. Otherwise iterate the values associated with the key and for each value in the values list, emit one output under the entry's key paired with the value unchanged. (The input collection accumulates all usage events for the same keyId under one key — the upstream UsageEventByKeyIdMapper re-keys events from their natural PK to keyId, so many events typically share the same key; singleton-only access would raise a non-unique-value error on any keyId with two or more usage events.)
export class FilterUsageEventsByKeyIdMapper implements Mapper<
  ApiKey_skip_id_,
  UsageEvent,
  ApiKey_skip_id_,
  UsageEvent
> {
  constructor(private keyId: string) {}

  mapEntry(
    key: ApiKey_skip_id_,
    values: Values<UsageEvent>,
    context: Context,
  ): Iterable<[ApiKey_skip_id_, UsageEvent]> {
    // > body
    if (key !== this.keyId) return [];
    const emits: [ApiKey_skip_id_, UsageEvent][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
