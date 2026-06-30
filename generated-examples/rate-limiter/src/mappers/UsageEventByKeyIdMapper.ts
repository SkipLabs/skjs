import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  UsageEvent_skip_id_,
  UsageEvent_skip_value_,
  ApiKey_skip_id_,
  UsageEvent,
  ApiKey,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each usage event entry, emit one output pair whose key is sourced from the entry's value at the keyId field (a foreign key to ApiKey.id, hence typed as ApiKey_skip_id_), paired with a new value listing every required field of UsageEvent explicitly: id sourced from the entry's key, keyId sourced from the entry's value at the keyId field, policyId sourced from the entry's value at the policyId field, ownerId sourced from the entry's value at the ownerId field, route sourced from the entry's value at the route field, allowed sourced from the entry's value at the allowed field, cost sourced from the entry's value at the cost field, remainingAfter sourced from the entry's value at the remainingAfter field, and checkedAt sourced from the entry's value at the checkedAt field. This re-injects the original usage event id (the input PK) on the value side so the listUsageEventsForApiKey response can include it.
export class UsageEventByKeyIdMapper implements Mapper<
  UsageEvent_skip_id_,
  UsageEvent_skip_value_,
  ApiKey_skip_id_,
  UsageEvent
> {
  mapEntry(
    key: UsageEvent_skip_id_,
    values: Values<UsageEvent_skip_value_>,
    context: Context,
  ): Iterable<[ApiKey_skip_id_, UsageEvent]> {
    // > body
    const emits: [ApiKey_skip_id_, UsageEvent][] = [];
    for (const value of values.toArray()) {
      const event: UsageEvent = {
        id: key,
        keyId: value.keyId,
        policyId: value.policyId,
        ownerId: value.ownerId,
        allowed: value.allowed,
        cost: value.cost,
        remainingAfter: value.remainingAfter,
        checkedAt: value.checkedAt,
        ...(value.route !== undefined && { route: value.route }),
      };
      emits.push([value.keyId, event]);
    }
    return emits;
    // < body
  }
}
