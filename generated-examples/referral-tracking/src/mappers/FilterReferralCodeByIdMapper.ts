import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReferralCode_skip_id_,
  ReferralCode_skip_value_,
  ReferralCode,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each referral code entry, emit the entry unchanged when the entry's key equals the referralCodeId param. Otherwise emit nothing.
export class FilterReferralCodeByIdMapper implements Mapper<
  ReferralCode_skip_id_,
  ReferralCode_skip_value_,
  ReferralCode_skip_id_,
  ReferralCode_skip_value_
> {
  constructor(private referralCodeId: string) {}

  mapEntry(
    key: ReferralCode_skip_id_,
    values: Values<ReferralCode_skip_value_>,
    context: Context,
  ): Iterable<[ReferralCode_skip_id_, ReferralCode_skip_value_]> {
    // > body
    const emits: [ReferralCode_skip_id_, ReferralCode_skip_value_][] = [];
    if (key === this.referralCodeId) {
      for (const value of values.toArray()) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
