import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { LineItem_skip_id_, LineItemStored, LineItem } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each line item entry, emit one output pair whose key is the entry's key (the LineItem's primary key), and whose value is a LineItem record listing every required field: id sourced from the entry's key; ownerId sourced from the entry's value's ownerId field; invoiceId sourced from the entry's value's invoiceId field; description sourced from the entry's value's description field; quantity sourced from the entry's value's quantity field; unitPrice sourced from the entry's value's unitPrice field; lineTotal computed as the entry's value's quantity field multiplied by the entry's value's unitPrice field; createdAt sourced from the entry's value's createdAt field.
export class AssembleLineItemMapper implements Mapper<
  LineItem_skip_id_,
  LineItemStored,
  LineItem_skip_id_,
  LineItem
> {
  mapEntry(
    key: LineItem_skip_id_,
    values: Values<LineItemStored>,
    context: Context,
  ): Iterable<[LineItem_skip_id_, LineItem]> {
    // > body
    const emits: [LineItem_skip_id_, LineItem][] = [];
    for (const value of values.toArray()) {
      const lineItem: LineItem = {
        id: key,
        ownerId: value.ownerId,
        invoiceId: value.invoiceId,
        description: value.description,
        quantity: value.quantity,
        unitPrice: value.unitPrice,
        lineTotal: value.quantity * value.unitPrice,
        createdAt: value.createdAt,
      };
      emits.push([key, lineItem]);
    }
    return emits;
    // < body
  }
}
