import { PaymentByOwnerSubMapper } from "../mappers/PaymentByOwnerSubMapper.js";
import type {
  PaymentEvent_skip_id_,
  PaymentEvent_skip_value_,
  ListPaymentsByOwnerSubParams,
  PaymentEvent,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListSubscriptionPaymentsResourceInputs extends SharedCollections {
  readonly paymentEvents: EagerCollection<
    PaymentEvent_skip_id_,
    PaymentEvent_skip_value_
  >;
}

export class ListSubscriptionPaymentsResource implements Resource<ListSubscriptionPaymentsResourceInputs> {
  private readonly subscriptionId: string;
  private readonly userId: string;

  constructor(params: ListPaymentsByOwnerSubParams) {
    this.subscriptionId = params.subscriptionId;
    this.userId = params.userId;
  }

  instantiate(
    inputs: ListSubscriptionPaymentsResourceInputs,
    _context: Context,
  ): EagerCollection<PaymentEvent_skip_id_, PaymentEvent_skip_value_> {
    return inputs.paymentEvents.map(
      PaymentByOwnerSubMapper,
      this.subscriptionId,
      this.userId,
    );
  }
}
