import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  User_skip_id_,
  Subscription,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each subscription entry, emit one output pair whose key is sourced from the entry's value's ownerId field (which is the primary key of the User entity), paired with a new value listing every required field of Subscription explicitly — the id sourced from the entry's key, and ownerId, name, amount, currency, billingCycle, startDate, nextRenewalAt, status, createdAt, updatedAt (plus optional vendor, category, notes when present) sourced from the entry's value. This re-key indexes subscriptions by their owner for owner-scoped listings and spending aggregation while re-injecting the subscription id on the value side so downstream consumers (spending summary tie-break by lexicographically greater id; cascade-delete needing per-subscription ids) can recover it.
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
    for (const value of values) {
      const sub: Subscription = {
        id: key,
        ownerId: value.ownerId,
        name: value.name,
        amount: value.amount,
        currency: value.currency,
        billingCycle: value.billingCycle,
        startDate: value.startDate,
        nextRenewalAt: value.nextRenewalAt,
        status: value.status,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        ...(value.vendor !== undefined && { vendor: value.vendor }),
        ...(value.category !== undefined && { category: value.category }),
        ...(value.notes !== undefined && { notes: value.notes }),
      };
      emits.push([value.ownerId, sub]);
    }
    return emits;
    // < body
  }
}
