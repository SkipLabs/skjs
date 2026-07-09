import type {
  Delivery_skip_id_,
  Delivery,
  Delivery_skip_value_,
  Subscription_skip_id_,
  Subscription,
  Subscription_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  Webhook_skip_id_,
  Webhook,
  WebhookStored,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly deliveries: EagerCollection<Delivery_skip_id_, Delivery_skip_value_>;
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
  readonly webhooks: EagerCollection<Webhook_skip_id_, WebhookStored>;
}

export interface GraphCollections extends SharedCollections {
  readonly deliveries: EagerCollection<Delivery_skip_id_, Delivery_skip_value_>;
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
  readonly webhooks: EagerCollection<Webhook_skip_id_, WebhookStored>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_deliveries = inputs.deliveries;
  const output_subscriptions = inputs.subscriptions;
  const output_users = inputs.users;
  const output_webhooks = inputs.webhooks;
  return {
    deliveries: output_deliveries,
    subscriptions: output_subscriptions,
    users: output_users,
    webhooks: output_webhooks,
  };
}
