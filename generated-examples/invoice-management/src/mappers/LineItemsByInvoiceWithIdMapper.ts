import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  LineItemKey,
  LineItemStored,
  Invoice_skip_id_,
  LineItem,
  Invoice,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each line item entry, emit one output pair whose key is sourced from the entry's key's invoiceId field, and whose value lists every required field of LineItem explicitly: id sourced from the entry's key's id field (re-injected because the new output key drops it); invoiceId sourced from the entry's key's invoiceId field; description sourced from the entry's value's description field; quantity sourced from the entry's value's quantity field; unitPrice sourced from the entry's value's unitPrice field; lineTotal (readOnly, always present) computed as the entry's value's quantity multiplied by the entry's value's unitPrice, then rounded to 2 decimals using half-away-from-zero rounding (i.e. multiply by 100, apply Math.round-style rounding where 0.5 rounds away from zero, divide by 100).
export class LineItemsByInvoiceWithIdMapper implements Mapper<
  LineItemKey,
  LineItemStored,
  Invoice_skip_id_,
  LineItem
> {
  mapEntry(
    key: LineItemKey,
    values: Values<LineItemStored>,
    context: Context,
  ): Iterable<[Invoice_skip_id_, LineItem]> {
    // > body
    const emits: [Invoice_skip_id_, LineItem][] = [];
    for (const value of values.toArray()) {
      const raw = value.quantity * value.unitPrice;
      const scaled = raw * 100;
      const rounded =
        scaled >= 0 ? Math.floor(scaled + 0.5) : -Math.floor(-scaled + 0.5);
      const lineTotal = rounded / 100;
      const item: LineItem = {
        id: key.id,
        invoiceId: key.invoiceId,
        description: value.description,
        quantity: value.quantity,
        unitPrice: value.unitPrice,
        lineTotal,
      };
      emits.push([key.invoiceId, item]);
    }
    return emits;
    // < body
  }
}
