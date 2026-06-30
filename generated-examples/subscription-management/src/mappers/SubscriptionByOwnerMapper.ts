import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  User_skip_id_,
  Subscription,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each subscription entry, emit one output pair whose key is sourced from the entry's value ownerId field (which is the User primary key — JWT sub claim of the owner), paired with a new value listing every required field of Subscription explicitly: id is sourced from the entry's key (= the original Subscription.id, preserved on the value side); ownerId, name, costCents, currency, billingCycle, nextRenewalDate, status, createdAt, updatedAt are sourced from the entry's value; optional fields provider, category, notes, cancelledAt are sourced from the entry's value when present and omitted otherwise. The original Subscription.id is preserved in the value as the id field — downstream consumers iterating per-owner subscriptions can recover each subscription's id from the value.
export class SubscriptionByOwnerMapper implements Mapper<
  Subscription_skip_id_,
  Subscription_skip_value_,
  User_skip_id_,
  Subscription
> {
  mapEntry(
    key: Subscription_skip_id_,
    values: Values<Subscription_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, Subscription]> {
    // > body
    const emits: [User_skip_id_, Subscription][] = [];
    for (const value of values.toArray()) {
      const sub: Subscription = {
        id: key,
        ownerId: value.ownerId,
        name: value.name,
        costCents: value.costCents,
        currency: value.currency,
        billingCycle: value.billingCycle,
        nextRenewalDate: value.nextRenewalDate,
        status: value.status,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        ...(value.provider !== undefined && { provider: value.provider }),
        ...(value.category !== undefined && { category: value.category }),
        ...(value.notes !== undefined && { notes: value.notes }),
        ...(value.cancelledAt !== undefined && {
          cancelledAt: value.cancelledAt,
        }),
      };
      emits.push([value.ownerId, sub]);
    }
    return emits;
    // < body
  }
}
