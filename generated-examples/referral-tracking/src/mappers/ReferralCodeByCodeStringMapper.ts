import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReferralCode_skip_id_,
  ReferralCodeStored,
  ReferralCodeString,
  ReferralCodeStoredWithId,
  ReferralCode,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each referral code entry, emit one output pair whose key is sourced from the entry's value's code field (the human-shareable code string), and whose value lists every required field of ReferralCodeStoredWithId explicitly: id sourced from the entry's key (the original ReferralCode.id); code sourced from the entry's value's code field; ownerId sourced from the entry's value's ownerId field; status sourced from the entry's value's status field; createdAt sourced from the entry's value's createdAt field; note is optional and present when the entry's value's note field is present, sourced from the entry's value's note field, absent otherwise. The original id (from the entry's key) is preserved on the value's id field so consumers (e.g. createReferral) can resolve a presented code string to the ReferralCode's id.
export class ReferralCodeByCodeStringMapper implements Mapper<
  ReferralCode_skip_id_,
  ReferralCodeStored,
  ReferralCodeString,
  ReferralCodeStoredWithId
> {
  mapEntry(
    key: ReferralCode_skip_id_,
    values: Values<ReferralCodeStored>,
    context: Context,
  ): Iterable<[ReferralCodeString, ReferralCodeStoredWithId]> {
    // > body
    const emits: [ReferralCodeString, ReferralCodeStoredWithId][] = [];
    for (const value of values.toArray()) {
      const out: ReferralCodeStoredWithId = {
        id: key,
        code: value.code,
        ownerId: value.ownerId,
        status: value.status,
        createdAt: value.createdAt,
        ...(value.note !== undefined && { note: value.note }),
      };
      emits.push([value.code, out]);
    }
    return emits;
    // < body
  }
}
