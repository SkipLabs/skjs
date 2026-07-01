import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Payment_skip_id_,
  Payment_skip_value_,
  Subscription_skip_id_,
  Payment,
  Subscription,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each payment entry, emit one output pair whose key is sourced from the entry's value's subscriptionId field (which is the primary key of the Subscription entity), paired with a new value listing every required field of Payment explicitly — the id sourced from the entry's key, and subscriptionId, ownerId, amount, currency, paidAt, createdAt (plus optional note when present) sourced from the entry's value. This re-key indexes payments by their parent subscription while re-injecting the payment id on the value side so listSubscriptionPayments can return Payment.id in its response and deleteSubscriptionPayment can identify each payment.
export class PaymentBySubscriptionMapper implements Mapper<
  Payment_skip_id_,
  Payment_skip_value_,
  Subscription_skip_id_,
  Payment
> {
  mapEntry(
    key: Payment_skip_id_,
    values: Values<Payment_skip_value_>,
    context: Context,
  ): Iterable<[Subscription_skip_id_, Payment]> {
    // > body
    const emits: [Subscription_skip_id_, Payment][] = [];
    for (const value of values.toArray()) {
      const payment: Payment = {
        id: key,
        subscriptionId: value.subscriptionId,
        ownerId: value.ownerId,
        amount: value.amount,
        currency: value.currency,
        paidAt: value.paidAt,
        createdAt: value.createdAt,
        ...(value.note !== undefined && { note: value.note }),
      };
      emits.push([value.subscriptionId, payment]);
    }
    return emits;
    // < body
  }
}
