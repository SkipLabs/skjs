import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { Order_skip_id_, Order_skip_value_, Order } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each order entry, emit the entry unchanged when (the skuId param is absent OR the entry's skuId field equals the skuId param) AND (the status param is absent OR the entry's status field equals the status param). Emit nothing otherwise.
export class FilterOrderBySkuAndStatusMapper implements Mapper<
  Order_skip_id_,
  Order_skip_value_,
  Order_skip_id_,
  Order_skip_value_
> {
  constructor(
    private skuId: string | null,
    private status: string | null,
  ) {}

  mapEntry(
    key: Order_skip_id_,
    values: Values<Order_skip_value_>,
    context: Context,
  ): Iterable<[Order_skip_id_, Order_skip_value_]> {
    // > body
    const emits: [Order_skip_id_, Order_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.skuId !== null && value.skuId !== this.skuId) continue;
      if (this.status !== null && value.status !== this.status) continue;
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
