import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  User_skip_id_,
  ReferralCode,
  ReferralCode_skip_id_,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry (keyed by owner userId), emit one output pair per value whose key is sourced from the value's id field (the original referral code id) and whose value is the value unchanged, when ALL of the following hold: (the entry's key equals the userId param) AND (the status param is absent OR the value's status field equals the status param). Otherwise emit nothing for that value.
export class FilterReferralCodesByOwnerAndStatusMapper implements Mapper<
  User_skip_id_,
  ReferralCode,
  ReferralCode_skip_id_,
  ReferralCode
> {
  constructor(
    private userId: string,
    private status: string | null,
  ) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<ReferralCode>,
    context: Context,
  ): Iterable<[ReferralCode_skip_id_, ReferralCode]> {
    // > body
    const emits: [ReferralCode_skip_id_, ReferralCode][] = [];
    if (key !== this.userId) return emits;
    for (const value of values.toArray()) {
      if (this.status !== null && value.status !== this.status) continue;
      emits.push([value.id, value]);
    }
    return emits;
    // < body
  }
}
