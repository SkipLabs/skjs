import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  OrderLineKey,
  OrderLine_skip_value_,
  OrderLine,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each order line entry, emit the entry unchanged when the entry's key's orderId field equals the orderId param. Otherwise emit nothing.
export class FilterOrderLinesByOrderMapper implements Mapper<
  OrderLineKey,
  OrderLine_skip_value_,
  OrderLineKey,
  OrderLine_skip_value_
> {
  constructor(private orderId: string) {}

  mapEntry(
    key: OrderLineKey,
    values: Values<OrderLine_skip_value_>,
    context: Context,
  ): Iterable<[OrderLineKey, OrderLine_skip_value_]> {
    // > body
    const emits: [OrderLineKey, OrderLine_skip_value_][] = [];
    if (key.orderId === this.orderId) {
      for (const value of values.toArray()) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
