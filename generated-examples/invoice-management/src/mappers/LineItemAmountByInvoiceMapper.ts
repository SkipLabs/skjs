import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  LineItemKey,
  LineItemStored,
  Invoice_skip_id_,
  InvoiceAmount,
  Invoice,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each line item entry, emit one output pair whose key is sourced from the entry's key's invoiceId field and whose value is the entry's value's quantity field multiplied by the entry's value's unitPrice field. The original line item id from the entry's key is dropped because the downstream consumer (per-invoice sum) does not need it — the reduction sums numeric contributions per invoice.
export class LineItemAmountByInvoiceMapper implements Mapper<
  LineItemKey,
  LineItemStored,
  Invoice_skip_id_,
  InvoiceAmount
> {
  mapEntry(
    key: LineItemKey,
    values: Values<LineItemStored>,
    context: Context,
  ): Iterable<[Invoice_skip_id_, InvoiceAmount]> {
    // > body
    const emits: [Invoice_skip_id_, InvoiceAmount][] = [];
    for (const value of values.toArray()) {
      emits.push([key.invoiceId, value.quantity * value.unitPrice]);
    }
    return emits;
    // < body
  }
}
