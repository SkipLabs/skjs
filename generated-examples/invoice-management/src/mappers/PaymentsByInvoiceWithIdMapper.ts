import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  PaymentKey,
  PaymentStored,
  Invoice_skip_id_,
  Payment,
  Invoice,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each payment entry, emit one output pair whose key is sourced from the entry's key's invoiceId field, and whose value lists every required field of Payment explicitly: id sourced from the entry's key's id field (re-injected because the new output key drops it); invoiceId sourced from the entry's key's invoiceId field; amount sourced from the entry's value's amount field; paidAt sourced from the entry's value's paidAt field. Optional fields: method (present when the entry's value's method field is present, sourced from the entry's value's method field; absent otherwise); reference (present when the entry's value's reference field is present, sourced from the entry's value's reference field; absent otherwise).
export class PaymentsByInvoiceWithIdMapper implements Mapper<
  PaymentKey,
  PaymentStored,
  Invoice_skip_id_,
  Payment
> {
  mapEntry(
    key: PaymentKey,
    values: Values<PaymentStored>,
    context: Context,
  ): Iterable<[Invoice_skip_id_, Payment]> {
    // > body
    const emits: [Invoice_skip_id_, Payment][] = [];
    for (const value of values.toArray()) {
      const payment: Payment = {
        id: key.id,
        invoiceId: key.invoiceId,
        amount: value.amount,
        paidAt: value.paidAt,
        ...(value.method !== undefined && { method: value.method }),
        ...(value.reference !== undefined && { reference: value.reference }),
      };
      emits.push([key.invoiceId, payment]);
    }
    return emits;
    // < body
  }
}
