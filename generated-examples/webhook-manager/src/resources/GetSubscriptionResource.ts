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
  Json,
} from "@skipruntime/core";

export interface GetSubscriptionResourceInputs extends SharedCollections {
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
}

export class GetSubscriptionResource implements Resource<GetSubscriptionResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetSubscriptionResourceInputs,
    _context: Context,
  ): EagerCollection<Subscription_skip_id_, Subscription_skip_value_> {
    return inputs.subscriptions;
  }
}
