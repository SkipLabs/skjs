import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  Subscription,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each subscription entry, emit the entry unchanged when the entry's value's ownerId field equals the userId param AND (the status param is absent OR the entry's value's status field equals the status param). Otherwise emit nothing.
export class FilterSubscriptionByOwnerAndStatusMapper implements Mapper<
  Subscription_skip_id_,
  Subscription_skip_value_,
  Subscription_skip_id_,
  Subscription_skip_value_
> {
  constructor(
    private userId: string,
    private status: string | null,
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
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
