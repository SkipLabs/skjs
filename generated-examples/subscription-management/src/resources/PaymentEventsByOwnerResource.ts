import { PaymentByOwnerMapper } from "../mappers/PaymentByOwnerMapper.js";
import type {
  PaymentEvent_skip_id_,
  PaymentEvent_skip_value_,
  User_skip_id_,
  PaymentEvent,
  User,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface PaymentEventsByOwnerResourceInputs extends SharedCollections {
  readonly paymentEvents: EagerCollection<
    PaymentEvent_skip_id_,
    PaymentEvent_skip_value_
  >;
}

export class PaymentEventsByOwnerResource implements Resource<PaymentEventsByOwnerResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: PaymentEventsByOwnerResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, PaymentEvent> {
    const paymentsByOwner = inputs.paymentEvents.map(PaymentByOwnerMapper);
    return paymentsByOwner;
  }
}
