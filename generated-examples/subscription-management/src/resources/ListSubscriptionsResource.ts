import { FilterSubscriptionByOwnerAndStatusMapper } from "../mappers/FilterSubscriptionByOwnerAndStatusMapper.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
  SubscriptionStatus,
  ListSubscriptionsParams,
  Subscription,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListSubscriptionsResourceInputs extends SharedCollections {
  readonly subscriptions: EagerCollection<
    Subscription_skip_id_,
    Subscription_skip_value_
  >;
}

export class ListSubscriptionsResource implements Resource<ListSubscriptionsResourceInputs> {
  private readonly status: SubscriptionStatus | null;
  private readonly userId: string;

  constructor(params: ListSubscriptionsParams) {
    this.status = params.status ?? null;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListSubscriptionsResourceInputs,
    _context: Context,
  ): EagerCollection<Subscription_skip_id_, Subscription_skip_value_> {
    return inputs.subscriptions.map(
      FilterSubscriptionByOwnerAndStatusMapper,
      this.userId,
      this.status,
    );
  }
}
