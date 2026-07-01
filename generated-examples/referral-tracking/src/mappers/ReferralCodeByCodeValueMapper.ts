import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReferralCode_skip_id_,
  ReferralCode_skip_value_,
  ReferralCodeValueKey,
  ReferralCode,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each referral code entry, emit one output pair whose key is sourced from the entry's code field (an opaque alphanumeric string acting as an alternate identifier for the ReferralCode entity), paired with a value listing every required field of ReferralCode: id sourced from the entry's key (re-injected so the consumer can recover the referral code id); ownerId, code, status, createdAt sourced from the entry's value; note present when the entry's value has a note field, sourced from there; expiresAt present when the entry's value has an expiresAt field, sourced from there.
export class ReferralCodeByCodeValueMapper implements Mapper<
  ReferralCode_skip_id_,
  ReferralCode_skip_value_,
  ReferralCodeValueKey,
  ReferralCode
> {
  mapEntry(
    key: ReferralCode_skip_id_,
    values: Values<ReferralCode_skip_value_>,
    context: Context,
  ): Iterable<[ReferralCodeValueKey, ReferralCode]> {
    // > body
    const emits: [ReferralCodeValueKey, ReferralCode][] = [];
    for (const value of values.toArray()) {
      const out: ReferralCode = {
        id: key,
        ownerId: value.ownerId,
        code: value.code,
        status: value.status,
        createdAt: value.createdAt,
        ...(value.note !== undefined && { note: value.note }),
        ...(value.expiresAt !== undefined && { expiresAt: value.expiresAt }),
      };
      emits.push([value.code, out]);
    }
    return emits;
    // < body
  }
}
