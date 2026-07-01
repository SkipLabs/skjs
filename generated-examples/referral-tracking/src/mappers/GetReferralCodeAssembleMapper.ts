import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReferralCode_skip_id_,
  ReferralCodeStored,
  ReferralCode_skip_value_,
  RedemptionCount,
  ReferralCode,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each referral code entry, consult redemptionCountByCode for the values indexed by the entry's key; if the consultation yields no values, use zero as the count, otherwise use the first value. Emit one output pair whose key is the entry's key unchanged and whose value lists every required field of ReferralCode_skip_value_ explicitly: code sourced from the entry's value's code field; ownerId sourced from the entry's value's ownerId field; status sourced from the entry's value's status field; createdAt sourced from the entry's value's createdAt field; redemptionCount sourced from the resolved count; note is optional and present when the entry's value's note field is present, sourced from the entry's value's note field, absent otherwise.
export class GetReferralCodeAssembleMapper implements Mapper<
  ReferralCode_skip_id_,
  ReferralCodeStored,
  ReferralCode_skip_id_,
  ReferralCode_skip_value_
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
  ): Iterable<[ReferralCode_skip_id_, ReferralCode_skip_value_]> {
    // > body
    const countValues = this.redemptionCountByCode.getArray(key);
    const redemptionCount =
      countValues.length === 0 ? 0 : (countValues[0] ?? 0);

    const emits: [ReferralCode_skip_id_, ReferralCode_skip_value_][] = [];
    for (const value of values.toArray()) {
      const out: ReferralCode_skip_value_ = {
        code: value.code,
        ownerId: value.ownerId,
        status: value.status,
        createdAt: value.createdAt,
        redemptionCount,
        ...(value.note !== undefined && { note: value.note }),
      };
      emits.push([key, out]);
    }
    return emits;
    // < body
  }
}
