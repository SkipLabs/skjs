import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Order_skip_id_,
  Order_skip_value_,
  Sku_skip_id_,
  Order,
  Sku,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each order entry, emit one output pair whose key is sourced from the entry's skuId field, paired with the entry's value unchanged. The original order id from the entry's key is dropped because the consumer only needs to sum reserved quantities by sku — the order id is not needed downstream.
export class OrderBySkuMapper implements Mapper<
  Order_skip_id_,
  Order_skip_value_,
  Sku_skip_id_,
  Order_skip_value_
> {
  mapEntry(
    key: Order_skip_id_,
    values: Values<Order_skip_value_>,
    context: Context,
  ): Iterable<[Sku_skip_id_, Order_skip_value_]> {
    // > body
    const emits: [Sku_skip_id_, Order_skip_value_][] = [];
    for (const value of values.toArray()) {
      emits.push([value.skuId, value]);
    }
    return emits;
    // < body
  }
}
