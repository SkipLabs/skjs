import type {
  PaymentEvent_skip_id_,
  PaymentEvent,
  PaymentEvent_skip_value_,
  Subscription_skip_id_,
  Subscription,
  Subscription_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly paymentEvents: EagerCollection<
    PaymentEvent_skip_id_,
    PaymentEvent_skip_value_
  >;
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly paymentEvents: EagerCollection<
    PaymentEvent_skip_id_,
    PaymentEvent_skip_value_
  >;
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_paymentEvents = inputs.paymentEvents;
  const output_subscriptions = inputs.subscriptions;
  const output_users = inputs.users;
  return {
    paymentEvents: output_paymentEvents,
    subscriptions: output_subscriptions,
    users: output_users,
  };
}
