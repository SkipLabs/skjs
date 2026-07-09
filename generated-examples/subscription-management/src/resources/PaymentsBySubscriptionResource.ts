import { PaymentBySubscriptionMapper } from "../mappers/PaymentBySubscriptionMapper.js";
import type {
  Payment_skip_id_,
  Payment_skip_value_,
  Subscription_skip_id_,
  Payment,
  Subscription,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface PaymentsBySubscriptionResourceInputs extends SharedCollections {
  readonly payments: EagerCollection<Payment_skip_id_, Payment_skip_value_>;
}

export class PaymentsBySubscriptionResource implements Resource<PaymentsBySubscriptionResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: PaymentsBySubscriptionResourceInputs,
    _context: Context,
  ): EagerCollection<Subscription_skip_id_, Payment> {
    const bySubscription = inputs.payments.map(PaymentBySubscriptionMapper);
    return bySubscription;
  }
}
