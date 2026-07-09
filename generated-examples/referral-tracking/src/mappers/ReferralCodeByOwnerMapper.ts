import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReferralCode_skip_id_,
  ReferralCodeStored,
  User_skip_id_,
  ReferralCode,
  RedemptionCount,
  User,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each referral code entry, consult redemptionCountByCode for the values indexed by the entry's key; if the consultation yields no values, use zero as the count, otherwise use the first value. Emit one output pair whose key is sourced from the entry's value's ownerId field, and whose value lists every required field of ReferralCode explicitly: id sourced from the entry's key (the original ReferralCode.id); code sourced from the entry's value's code field; ownerId sourced from the entry's value's ownerId field; status sourced from the entry's value's status field; createdAt sourced from the entry's value's createdAt field; redemptionCount sourced from the resolved count; note is optional and present when the entry's value's note field is present, sourced from the entry's value's note field, absent otherwise. The original ReferralCode.id from the entry's key is preserved inside the value's id field so downstream consumers reconstructing full ReferralCode entities have access to it via the value.
export class ReferralCodeByOwnerMapper implements Mapper<
  ReferralCode_skip_id_,
  ReferralCodeStored,
  User_skip_id_,
  ReferralCode
> {
  constructor(
    private redemptionCountByCode: EagerCollection<
      ReferralCode_skip_id_,
      RedemptionCount
    >,
  ) {}

  mapEntry(
    key: ReferralCode_skip_id_,
    values: Values<ReferralCodeStored>,
    context: Context,
  ): Iterable<[User_skip_id_, ReferralCode]> {
    // > body
    const emits: [User_skip_id_, ReferralCode][] = [];
    for (const value of values.toArray()) {
      const counts = this.redemptionCountByCode.getArray(key);
      const redemptionCount = counts.length === 0 ? 0 : (counts[0] ?? 0);
      const out: ReferralCode = {
        id: key,
        code: value.code,
        ownerId: value.ownerId,
        status: value.status,
        createdAt: value.createdAt,
        redemptionCount,
        ...(value.note !== undefined && { note: value.note }),
      };
      emits.push([value.ownerId, out]);
    }
    return emits;
    // < body
  }
}
