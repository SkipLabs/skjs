import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  PaymentKey,
  PaymentStored,
  Invoice_skip_id_,
  InvoiceAmount,
  Invoice,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each payment entry, emit one output pair whose key is sourced from the entry's key's invoiceId field and whose value is sourced from the entry's value's amount field. The original payment id from the entry's key is dropped because the downstream consumer (per-invoice sum) does not need it.
export class PaymentAmountByInvoiceMapper implements Mapper<
  PaymentKey,
  PaymentStored,
  Invoice_skip_id_,
  InvoiceAmount
> {
  mapEntry(
    key: PaymentKey,
    values: Values<PaymentStored>,
    context: Context,
  ): Iterable<[Invoice_skip_id_, InvoiceAmount]> {
    // > body
    const emits: [Invoice_skip_id_, InvoiceAmount][] = [];
    for (const value of values.toArray()) {
      emits.push([key.invoiceId, value.amount]);
    }
    return emits;
    // < body
  }
}
