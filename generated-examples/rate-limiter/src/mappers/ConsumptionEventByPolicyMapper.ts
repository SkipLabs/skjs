import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ConsumptionEvent_skip_id_,
  ConsumptionEvent_skip_value_,
  Policy_skip_id_,
  ConsumptionEvent,
  Policy,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each consumption event entry, emit one output pair whose key is sourced from the entry's value's policyId field, and whose value is a ConsumptionEvent record whose id is sourced from the entry's key, whose policyId is sourced from the entry's value's policyId field, and whose key, cost, occurredAtMs fields are sourced from the corresponding fields of the entry's value.
export class ConsumptionEventByPolicyMapper implements Mapper<
  ConsumptionEvent_skip_id_,
  ConsumptionEvent_skip_value_,
  Policy_skip_id_,
  ConsumptionEvent
> {
  mapEntry(
    key: ConsumptionEvent_skip_id_,
    values: Values<ConsumptionEvent_skip_value_>,
    context: Context,
  ): Iterable<[Policy_skip_id_, ConsumptionEvent]> {
    // > body
    const emits: [Policy_skip_id_, ConsumptionEvent][] = [];
    for (const value of values.toArray()) {
      const event: ConsumptionEvent = {
        id: key,
        policyId: value.policyId,
        key: value.key,
        cost: value.cost,
        occurredAtMs: value.occurredAtMs,
      };
      emits.push([value.policyId, event]);
    }
    return emits;
    // < body
  }
}
