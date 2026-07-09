import type {
  Payment_skip_id_,
  Payment,
  Payment_skip_value_,
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
  readonly payments: EagerCollection<Payment_skip_id_, Payment_skip_value_>;
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly payments: EagerCollection<Payment_skip_id_, Payment_skip_value_>;
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
  const output_payments = inputs.payments;
  const output_subscriptions = inputs.subscriptions;
  const output_users = inputs.users;
  return {
    payments: output_payments,
    subscriptions: output_subscriptions,
    users: output_users,
  };
}
