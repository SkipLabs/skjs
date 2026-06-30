import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  OrderLineItemKey,
  OrderLineItemStored,
  Order_skip_id_,
  OrderLineItemForOrder,
  Order,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each line item entry, emit a new key sourced from the entry's key's orderId field. The new value lists every required field of OrderLineItemForOrder explicitly: orderId is sourced from the entry's key's orderId field; lineNumber is sourced from the entry's key's lineNumber field; productId is sourced from the entry's value's productId field; productName is sourced from the entry's value's productName field; quantity is sourced from the entry's value's quantity field; unitPriceCents is sourced from the entry's value's unitPriceCents field.
export class LineItemsByOrderMapper implements Mapper<
  OrderLineItemKey,
  OrderLineItemStored,
  Order_skip_id_,
  OrderLineItemForOrder
> {
  mapEntry(
    key: OrderLineItemKey,
    values: Values<OrderLineItemStored>,
    context: Context,
  ): Iterable<[Order_skip_id_, OrderLineItemForOrder]> {
    // > body
    const emits: [Order_skip_id_, OrderLineItemForOrder][] = [];
    for (const value of values.toArray()) {
      emits.push([
        key.orderId,
        {
          orderId: key.orderId,
          lineNumber: key.lineNumber,
          productId: value.productId,
          productName: value.productName,
          quantity: value.quantity,
          unitPriceCents: value.unitPriceCents,
        },
      ]);
    }
    return emits;
    // < body
  }
}
