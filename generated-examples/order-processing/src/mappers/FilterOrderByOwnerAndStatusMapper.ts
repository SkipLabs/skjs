import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Order_skip_id_, OrderStored, Order } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each order entry, when the entry's userId field does not equal the userId param, emit nothing. Otherwise, when the status param is present and the entry's status field does not equal the status param, emit nothing. Otherwise emit the entry unchanged.
export class FilterOrderByOwnerAndStatusMapper implements Mapper<
  Order_skip_id_,
  OrderStored,
  Order_skip_id_,
  OrderStored
> {
  constructor(
    private userId: string,
    private status: string | null,
  ) {}

  mapEntry(
    key: Order_skip_id_,
    values: Values<OrderStored>,
    context: Context,
  ): Iterable<[Order_skip_id_, OrderStored]> {
    // > body
    const emits: [Order_skip_id_, OrderStored][] = [];
    for (const value of values.toArray()) {
      if (value.userId !== this.userId) continue;
      if (this.status !== null && value.status !== this.status) continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
