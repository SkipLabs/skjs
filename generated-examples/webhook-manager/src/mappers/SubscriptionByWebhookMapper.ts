import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  Webhook_skip_id_,
  Subscription,
  Webhook,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each subscription entry, emit one output pair whose key is sourced from the input key's webhookId component, paired with a new value listing every required field of Subscription explicitly: webhookId sourced from the input key's webhookId component, eventType sourced from the input key's eventType component, and createdAt sourced from the entry's value's createdAt field.
export class SubscriptionByWebhookMapper implements Mapper<
  Subscription_skip_id_,
  Subscription_skip_value_,
  Webhook_skip_id_,
  Subscription
> {
  mapEntry(
    key: Subscription_skip_id_,
    values: Values<Subscription_skip_value_>,
    context: Context,
  ): Iterable<[Webhook_skip_id_, Subscription]> {
    // > body
    const emits: [Webhook_skip_id_, Subscription][] = [];
    for (const value of values.toArray()) {
      const subscription: Subscription = {
        webhookId: key.webhookId,
        eventType: key.eventType,
        createdAt: value.createdAt,
      };
      emits.push([key.webhookId, subscription]);
    }
    return emits;
    // < body
  }
}
