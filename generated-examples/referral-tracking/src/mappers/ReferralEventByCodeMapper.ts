import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReferralEvent_skip_id_,
  ReferralEvent_skip_value_,
  ReferralCode_skip_id_,
  ReferralEvent,
  ReferralCode,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each referral event entry, emit one output pair whose key is sourced from the entry's referralCodeId field (which is the primary key of the ReferralCode entity), paired with the entry's value unchanged. The original entry id (key component) is dropped because the consumer (stats reducer) only needs the per-code grouping and the event's kind/referredUserId fields which remain on the value.
export class ReferralEventByCodeMapper implements Mapper<
  ReferralEvent_skip_id_,
  ReferralEvent_skip_value_,
  ReferralCode_skip_id_,
  ReferralEvent_skip_value_
> {
  mapEntry(
    key: ReferralEvent_skip_id_,
    values: Values<ReferralEvent_skip_value_>,
    context: Context,
  ): Iterable<[ReferralCode_skip_id_, ReferralEvent_skip_value_]> {
    // > body
    const emits: [ReferralCode_skip_id_, ReferralEvent_skip_value_][] = [];
    for (const value of values.toArray()) {
      emits.push([value.referralCodeId, value]);
    }
    return emits;
    // < body
  }
}
