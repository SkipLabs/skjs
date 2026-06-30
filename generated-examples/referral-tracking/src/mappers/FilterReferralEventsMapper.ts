import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReferralEvent_skip_id_,
  ReferralEvent_skip_value_,
  ReferralEvent,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each referral event entry, emit the entry unchanged when ALL of these hold: (the referralCodeId param is absent OR the entry's referralCodeId field equals the referralCodeId param) AND (the referrerUserId param is absent OR the entry's referrerUserId field equals the referrerUserId param) AND (the referredUserId param is absent OR the entry's referredUserId field equals the referredUserId param) AND (the kind param is absent OR the entry's kind field equals the kind param). Otherwise emit nothing.
export class FilterReferralEventsMapper implements Mapper<
  ReferralEvent_skip_id_,
  ReferralEvent_skip_value_,
  ReferralEvent_skip_id_,
  ReferralEvent_skip_value_
> {
  constructor(
    private referralCodeId: string | null,
    private referrerUserId: string | null,
    private referredUserId: string | null,
    private kind: string | null,
  ) {}

  mapEntry(
    key: ReferralEvent_skip_id_,
    values: Values<ReferralEvent_skip_value_>,
    context: Context,
  ): Iterable<[ReferralEvent_skip_id_, ReferralEvent_skip_value_]> {
    // > body
    const emits: [ReferralEvent_skip_id_, ReferralEvent_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (
        this.referralCodeId !== null &&
        value.referralCodeId !== this.referralCodeId
      )
        continue;
      if (
        this.referrerUserId !== null &&
        value.referrerUserId !== this.referrerUserId
      )
        continue;
      if (
        this.referredUserId !== null &&
        value.referredUserId !== this.referredUserId
      )
        continue;
      if (this.kind !== null && value.kind !== this.kind) continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
