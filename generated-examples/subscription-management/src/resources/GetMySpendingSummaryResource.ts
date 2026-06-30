import { SpendingSummaryMapper } from "../mappers/SpendingSummaryMapper.js";
import { SubscriptionByOwnerMapper } from "../mappers/SubscriptionByOwnerMapper.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  User_skip_id_,
  User_skip_value_,
  SpendingSummary,
  GetSpendingSummaryParams,
  Subscription,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetMySpendingSummaryResourceInputs extends SharedCollections {
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export class GetMySpendingSummaryResource implements Resource<GetMySpendingSummaryResourceInputs> {
  private readonly userId: string;

  constructor(params: GetSpendingSummaryParams) {
    this.userId = params.userId;
  }

  instantiate(
    inputs: GetMySpendingSummaryResourceInputs,
    _context: Context,
  ): EagerCollection<0, SpendingSummary> {
    const subscriptionsByOwner = inputs.subscriptions.map(
      SubscriptionByOwnerMapper,
    );
    return inputs.users.map(
      SpendingSummaryMapper,
      this.userId,
      subscriptionsByOwner,
    );
  }
}
