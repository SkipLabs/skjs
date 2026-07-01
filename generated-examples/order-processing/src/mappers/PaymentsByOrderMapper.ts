import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Payment_skip_id_,
  Payment_skip_value_,
  Order_skip_id_,
  PaymentForOrder,
  Payment,
  Order,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each payment entry, emit a new key sourced from the entry's value's orderId field. The new value lists every required field of PaymentForOrder explicitly: id is sourced from the entry's key (the original payment id); orderId is sourced from the entry's value's orderId field; amountCents is sourced from the entry's value's amountCents field; currency is sourced from the entry's value's currency field; paymentMethod is sourced from the entry's value's paymentMethod field; createdAt is sourced from the entry's value's createdAt field. The optional paymentReference is sourced from the entry's value's paymentReference field when present.
export class PaymentsByOrderMapper implements Mapper<
  Payment_skip_id_,
  Payment_skip_value_,
  Order_skip_id_,
  PaymentForOrder
> {
  mapEntry(
    key: Payment_skip_id_,
    values: Values<Payment_skip_value_>,
    context: Context,
  ): Iterable<[Order_skip_id_, PaymentForOrder]> {
    // > body
    const emits: [Order_skip_id_, PaymentForOrder][] = [];
    for (const value of values.toArray()) {
      const payment: PaymentForOrder = {
        id: key,
        orderId: value.orderId,
        amountCents: value.amountCents,
        currency: value.currency,
        paymentMethod: value.paymentMethod,
        createdAt: value.createdAt,
        ...(value.paymentReference !== undefined && {
          paymentReference: value.paymentReference,
        }),
      };
      emits.push([value.orderId, payment]);
    }
    return emits;
    // < body
  }
}
