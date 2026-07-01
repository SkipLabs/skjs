import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Referral_skip_id_,
  Referral_skip_value_,
  ReferralCode_skip_id_,
  RedemptionCount,
  Referral,
  ReferralCode,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each referral entry, emit one output pair whose key is sourced from the entry's value's referralCodeId field and whose value is the literal one. The original Referral.id (from the entry's key) is dropped: this collection feeds a per-code count reducer (SumNumberReducer) that aggregates the literal ones into redemptionCountByCode, and individual referral row identities are not needed downstream.
export class ReferralCountByCodeMapper implements Mapper<
  Referral_skip_id_,
  Referral_skip_value_,
  ReferralCode_skip_id_,
  RedemptionCount
> {
  mapEntry(
    key: Referral_skip_id_,
    values: Values<Referral_skip_value_>,
    context: Context,
  ): Iterable<[ReferralCode_skip_id_, RedemptionCount]> {
    // > body
    const emits: [ReferralCode_skip_id_, RedemptionCount][] = [];
    for (const value of values.toArray()) {
      emits.push([value.referralCodeId, 1]);
    }
    return emits;
    // < body
  }
}
