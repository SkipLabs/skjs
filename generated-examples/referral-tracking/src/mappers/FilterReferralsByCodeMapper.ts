import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReferralCode_skip_id_,
  Referral,
  Referral_skip_id_,
  ReferralCode,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry (keyed by referralCodeId), emit one output pair per value whose key is sourced from the value's id field (the original referral id) and whose value is the value unchanged, when ALL of the following hold: (the entry's key equals the referralCodeId param) AND (the status param is absent OR the value's status field equals the status param) AND (the since param is absent OR the value's createdAt field is greater-than-or-equal to the since param, compared as ISO-8601 date-time strings) AND (the until param is absent OR the value's createdAt field is strictly less than the until param, compared as ISO-8601 date-time strings). Otherwise emit nothing for that value.
export class FilterReferralsByCodeMapper implements Mapper<
  ReferralCode_skip_id_,
  Referral,
  Referral_skip_id_,
  Referral
> {
  constructor(
    private referralCodeId: string,
    private status: string | null,
    private since: string | null,
    private until: string | null,
  ) {}

  mapEntry(
    key: ReferralCode_skip_id_,
    values: Values<Referral>,
    context: Context,
  ): Iterable<[Referral_skip_id_, Referral]> {
    // > body
    const emits: [Referral_skip_id_, Referral][] = [];
    if (key !== this.referralCodeId) return emits;
    for (const value of values.toArray()) {
      if (this.status !== null && value.status !== this.status) continue;
      if (this.since !== null && !(value.createdAt >= this.since)) continue;
      if (this.until !== null && !(value.createdAt < this.until)) continue;
      emits.push([value.id, value]);
    }
    return emits;
    // < body
  }
}
