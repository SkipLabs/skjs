import { SubscriptionByOwnerMapper } from "../mappers/SubscriptionByOwnerMapper.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  User_skip_id_,
  Subscription,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface SubscriptionsByOwnerResourceInputs extends SharedCollections {
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
}

export class SubscriptionsByOwnerResource implements Resource<SubscriptionsByOwnerResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: SubscriptionsByOwnerResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Subscription> {
    const subscriptionsByOwner = inputs.subscriptions.map(
      SubscriptionByOwnerMapper,
    );
    return subscriptionsByOwner;
  }
}
