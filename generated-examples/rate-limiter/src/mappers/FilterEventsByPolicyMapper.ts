import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Policy_skip_id_, ConsumptionEvent, Policy } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the policyId key: when the entry's key does not equal the policyId param, emit nothing. Otherwise iterate the values associated with the key and for each value in the values list, emit one output pair whose key is the entry's key and whose value is the value unchanged. (The upstream ConsumptionEventByPolicyMapper re-keys events from event-id to policyId, accumulating many ConsumptionEvent values under one policyId key — singleton-only access would raise a non-unique-value error on any policy with two or more events.)
export class FilterEventsByPolicyMapper implements Mapper<
  Policy_skip_id_,
  ConsumptionEvent,
  Policy_skip_id_,
  ConsumptionEvent
> {
  constructor(private policyId: string) {}

  mapEntry(
    key: Policy_skip_id_,
    values: Values<ConsumptionEvent>,
    context: Context,
  ): Iterable<[Policy_skip_id_, ConsumptionEvent]> {
    // > body
    if (key !== this.policyId) return [];
    const emits: [Policy_skip_id_, ConsumptionEvent][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
