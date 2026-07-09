import { SubscriptionByWebhookMapper } from "../mappers/SubscriptionByWebhookMapper.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  Webhook_skip_id_,
  Subscription,
  Webhook,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListSubscriptionsForWebhookResourceInputs extends SharedCollections {
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
}

export class ListSubscriptionsForWebhookResource implements Resource<ListSubscriptionsForWebhookResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListSubscriptionsForWebhookResourceInputs,
    _context: Context,
  ): EagerCollection<Webhook_skip_id_, Subscription> {
    const subscriptionsByWebhook = inputs.subscriptions.map(
      SubscriptionByWebhookMapper,
    );
    return subscriptionsByWebhook;
  }
}
