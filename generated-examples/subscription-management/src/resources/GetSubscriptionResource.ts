import { GetSubscriptionByOwnerMapper } from "../mappers/GetSubscriptionByOwnerMapper.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  GetSubscriptionParams,
  Subscription,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetSubscriptionResourceInputs extends SharedCollections {
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
}

export class GetSubscriptionResource implements Resource<GetSubscriptionResourceInputs> {
  private readonly subscriptionId: string;
  private readonly userId: string;

  constructor(params: GetSubscriptionParams) {
    this.subscriptionId = params.subscriptionId;
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetSubscriptionResourceInputs,
    _context: Context,
  ): EagerCollection<Subscription_skip_id_, Subscription_skip_value_> {
    return inputs.subscriptions.map(
      GetSubscriptionByOwnerMapper,
      this.subscriptionId,
      this.userId,
    );
  }
}
