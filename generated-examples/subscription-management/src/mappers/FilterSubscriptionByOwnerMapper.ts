import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  Subscription,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each subscription entry, emit the entry unchanged when ALL of the following hold: (the entry's value ownerId field equals the userId param) AND (the status param is absent OR the entry's value status field equals the status param) AND (the dueBefore param is absent OR the entry's value nextRenewalDate field is lexicographically less-than-or-equal to the dueBefore param — both are ISO date strings of format YYYY-MM-DD which compare correctly lexicographically). Otherwise emit nothing.
export class FilterSubscriptionByOwnerMapper implements Mapper<
  Subscription_skip_id_,
  Subscription_skip_value_,
  Subscription_skip_id_,
  Subscription_skip_value_
> {
  constructor(
    private userId: string,
    private status: string | null,
    private dueBefore: string | null,
  ) {}

  mapEntry(
    key: Subscription_skip_id_,
    values: Values<Subscription_skip_value_>,
    context: Context,
  ): Iterable<[Subscription_skip_id_, Subscription_skip_value_]> {
    // > body
    const emits: [Subscription_skip_id_, Subscription_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (value.ownerId !== this.userId) continue;
      if (this.status !== null && value.status !== this.status) continue;
      if (this.dueBefore !== null && !(value.nextRenewalDate <= this.dueBefore))
        continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
