import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Sku_skip_id_,
  Order_skip_value_,
  QuantityAccum,
  Sku,
  Order,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry (keyed by skuId), receive all Order values associated with that skuId. Filter the values to keep only those whose status field equals the literal 'PENDING' OR equals the literal 'ALLOCATED'. Emit one output pair whose key is the entry's key unchanged and whose value is the sum of the quantity field across the filtered values. When no values pass the filter, emit one output pair whose key is the entry's key unchanged and whose value is zero. When the entry has no values, this aggregation is not invoked (the entry does not exist); consumers consulting the resulting collection by a skuId with no orders receive nothing, and the api method defaults to zero at read time.
export class ReservedBySkuMapper implements Mapper<
  Sku_skip_id_,
  Order_skip_value_,
  Sku_skip_id_,
  QuantityAccum
> {
  mapEntry(
    key: Sku_skip_id_,
    values: Values<Order_skip_value_>,
    context: Context,
  ): Iterable<[Sku_skip_id_, QuantityAccum]> {
    // > body
    let sum = 0;
    for (const value of values.toArray()) {
      if (value.status === "PENDING" || value.status === "ALLOCATED") {
        sum += value.quantity;
      }
    }
    return [[key, sum]];
    // < body
  }
}
