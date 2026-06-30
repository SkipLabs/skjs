import { FilterSubscriptionByOwnerMapper } from "../mappers/FilterSubscriptionByOwnerMapper.js";
import type {
  Subscription_skip_id_,
  Subscription_skip_value_,
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
  private readonly dueBefore: string | null;
  private readonly status: string | null;
  private readonly userId: string;

  constructor(params: ListSubscriptionsParams) {
    this.dueBefore = params.dueBefore ?? null;
    this.status = params.status ?? null;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListSubscriptionsResourceInputs,
    _context: Context,
  ): EagerCollection<Subscription_skip_id_, Subscription_skip_value_> {
    return inputs.subscriptions.map(
      FilterSubscriptionByOwnerMapper,
      this.userId,
      this.status,
      this.dueBefore,
    );
  }
}
