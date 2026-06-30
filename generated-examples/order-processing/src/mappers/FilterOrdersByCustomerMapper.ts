import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Order_skip_id_, OrderStored, Order } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each order entry, emit the entry unchanged when the entry's customerId field equals the userId param. Otherwise emit nothing.
export class FilterOrdersByCustomerMapper implements Mapper<
  Order_skip_id_,
  OrderStored,
  Order_skip_id_,
  OrderStored
> {
  constructor(private userId: string) {}

  mapEntry(
    key: Order_skip_id_,
    values: Values<OrderStored>,
    context: Context,
  ): Iterable<[Order_skip_id_, OrderStored]> {
    // > body
    const emits: [Order_skip_id_, OrderStored][] = [];
    for (const value of values.toArray()) {
      if (value.customerId === this.userId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
