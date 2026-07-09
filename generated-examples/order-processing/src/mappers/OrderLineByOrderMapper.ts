import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  OrderLineKey,
  OrderLine_skip_value_,
  Order_skip_id_,
  OrderLineByOrderValue,
  OrderLine,
  Order,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each order line entry, emit one output pair whose key is sourced from the entry's key's orderId field, paired with a new value whose lineIndex field is sourced from the entry's key's lineIndex field, and whose productId, productName, unitPriceCents and quantity fields are sourced from the corresponding fields of the entry's value.
export class OrderLineByOrderMapper implements Mapper<
  OrderLineKey,
  OrderLine_skip_value_,
  Order_skip_id_,
  OrderLineByOrderValue
> {
  mapEntry(
    key: OrderLineKey,
    values: Values<OrderLine_skip_value_>,
    context: Context,
  ): Iterable<[Order_skip_id_, OrderLineByOrderValue]> {
    // > body
    const emits: [Order_skip_id_, OrderLineByOrderValue][] = [];
    for (const value of values.toArray()) {
      const out: OrderLineByOrderValue = {
        lineIndex: key.lineIndex,
        productId: value.productId,
        productName: value.productName,
        unitPriceCents: value.unitPriceCents,
        quantity: value.quantity,
      };
      emits.push([key.orderId, out]);
    }
    return emits;
    // < body
  }
}
