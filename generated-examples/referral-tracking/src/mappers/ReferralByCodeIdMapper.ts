import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Referral_skip_id_,
  Referral_skip_value_,
  ReferralCode_skip_id_,
  Referral,
  ReferralCode,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each referral entry, emit one output pair whose key is sourced from the entry's value's referralCodeId field, and whose value lists every required field of Referral explicitly: id sourced from the entry's key (the original Referral.id); referralCodeId sourced from the entry's value's referralCodeId field; referrerUserId sourced from the entry's value's referrerUserId field; referredUserId sourced from the entry's value's referredUserId field; status sourced from the entry's value's status field; createdAt sourced from the entry's value's createdAt field; confirmedAt is optional and present when the entry's value's confirmedAt field is present, sourced from that field, absent otherwise; rejectedAt is optional and present when the entry's value's rejectedAt field is present, sourced from that field, absent otherwise; rejectionReason is optional and present when the entry's value's rejectionReason field is present, sourced from that field, absent otherwise. The original Referral.id from the entry's key is preserved inside the value's id field so downstream consumers reading value.id have access to it.
export class ReferralByCodeIdMapper implements Mapper<
  Referral_skip_id_,
  Referral_skip_value_,
  ReferralCode_skip_id_,
  Referral
> {
  mapEntry(
    key: Referral_skip_id_,
    values: Values<Referral_skip_value_>,
    context: Context,
  ): Iterable<[ReferralCode_skip_id_, Referral]> {
    // > body
    const emits: [ReferralCode_skip_id_, Referral][] = [];
    for (const value of values.toArray()) {
      const referral: Referral = {
        id: key,
        referralCodeId: value.referralCodeId,
        referrerUserId: value.referrerUserId,
        referredUserId: value.referredUserId,
        status: value.status,
        createdAt: value.createdAt,
        ...(value.confirmedAt !== undefined && {
          confirmedAt: value.confirmedAt,
        }),
        ...(value.rejectedAt !== undefined && { rejectedAt: value.rejectedAt }),
        ...(value.rejectionReason !== undefined && {
          rejectionReason: value.rejectionReason,
        }),
      };
      emits.push([value.referralCodeId, referral]);
    }
    return emits;
    // < body
  }
}
