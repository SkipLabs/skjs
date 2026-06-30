import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  Subscription,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each subscription entry, emit the entry unchanged when the entry's key equals the subscriptionId param AND the entry's value ownerId field equals the userId param. Otherwise emit nothing.
export class GetSubscriptionByOwnerMapper implements Mapper<
  Subscription_skip_id_,
  Subscription_skip_value_,
  Subscription_skip_id_,
  Subscription_skip_value_
> {
  constructor(
    private subscriptionId: string,
    private userId: string,
  ) {}

  mapEntry(
    key: Subscription_skip_id_,
    values: Values<Subscription_skip_value_>,
    context: Context,
  ): Iterable<[Subscription_skip_id_, Subscription_skip_value_]> {
    // > body
    const emits: [Subscription_skip_id_, Subscription_skip_value_][] = [];
    if (key !== this.subscriptionId) return emits;
    for (const value of values.toArray()) {
      if (value.ownerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
