import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  Subscription,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetSubscriptionStoredResourceInputs extends SharedCollections {
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
}

export class GetSubscriptionStoredResource implements Resource<GetSubscriptionStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetSubscriptionStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Subscription_skip_id_, Subscription_skip_value_> {
    return inputs.subscriptions;
  }
}
