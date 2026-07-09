import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Referral_skip_id_,
  Referral_skip_value_,
  Referral,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each referral entry, emit the entry unchanged when ALL of the following hold: (role param is the literal 'referrer' AND the entry's value's referrerUserId field equals the userId param) OR (role param is the literal 'referred' AND the entry's value's referredUserId field equals the userId param) OR (role param is absent AND (the entry's value's referrerUserId field equals the userId param OR the entry's value's referredUserId field equals the userId param)); AND (the status param is absent OR the entry's value's status field equals the status param). Otherwise emit nothing.
export class FilterMyReferralsMapper implements Mapper<
  Referral_skip_id_,
  Referral_skip_value_,
  Referral_skip_id_,
  Referral_skip_value_
> {
  constructor(
    private userId: string,
    private role: string | null,
    private status: string | null,
  ) {}

  mapEntry(
    key: Referral_skip_id_,
    values: Values<Referral_skip_value_>,
    context: Context,
  ): Iterable<[Referral_skip_id_, Referral_skip_value_]> {
    // > body
    const role = this.role;
    const status = this.status;
    const emits: [Referral_skip_id_, Referral_skip_value_][] = [];
    for (const value of values.toArray()) {
      let roleMatch = false;
      if (role === "referrer") {
        roleMatch = value.referrerUserId === this.userId;
      } else if (role === "referred") {
        roleMatch = value.referredUserId === this.userId;
      } else if (role === null) {
        roleMatch =
          value.referrerUserId === this.userId ||
          value.referredUserId === this.userId;
      }
      if (!roleMatch) continue;
      if (status !== null && value.status !== status) continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
