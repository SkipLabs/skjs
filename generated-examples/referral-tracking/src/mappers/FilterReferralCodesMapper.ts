import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  ReferralCode_skip_id_,
  ReferralCode_skip_value_,
  ReferralCode,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each referral code entry, emit the entry unchanged when ALL of these hold: (the ownerId param is absent OR the entry's ownerId field equals the ownerId param) AND (the code param is absent OR the entry's code field equals the code param) AND (the status param is absent OR the entry's status field equals the status param). Otherwise emit nothing.
export class FilterReferralCodesMapper implements Mapper<
  ReferralCode_skip_id_,
  ReferralCode_skip_value_,
  ReferralCode_skip_id_,
  ReferralCode_skip_value_
> {
  constructor(
    private ownerId: string | null,
    private code: string | null,
    private status: string | null,
  ) {}

  mapEntry(
    key: ReferralCode_skip_id_,
    values: Values<ReferralCode_skip_value_>,
    context: Context,
  ): Iterable<[ReferralCode_skip_id_, ReferralCode_skip_value_]> {
    // > body
    const emits: [ReferralCode_skip_id_, ReferralCode_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.ownerId !== null && value.ownerId !== this.ownerId) continue;
      if (this.code !== null && value.code !== this.code) continue;
      if (this.status !== null && value.status !== this.status) continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
