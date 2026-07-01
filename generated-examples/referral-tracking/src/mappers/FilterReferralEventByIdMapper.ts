import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReferralEvent_skip_id_,
  ReferralEvent_skip_value_,
  ReferralEvent,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each referral event entry, emit the entry unchanged when the entry's key equals the referralEventId param. Otherwise emit nothing.
export class FilterReferralEventByIdMapper implements Mapper<
  ReferralEvent_skip_id_,
  ReferralEvent_skip_value_,
  ReferralEvent_skip_id_,
  ReferralEvent_skip_value_
> {
  constructor(private referralEventId: string) {}

  mapEntry(
    key: ReferralEvent_skip_id_,
    values: Values<ReferralEvent_skip_value_>,
    context: Context,
  ): Iterable<[ReferralEvent_skip_id_, ReferralEvent_skip_value_]> {
    // > body
    const emits: [ReferralEvent_skip_id_, ReferralEvent_skip_value_][] = [];
    if (key === this.referralEventId) {
      for (const value of values.toArray()) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
