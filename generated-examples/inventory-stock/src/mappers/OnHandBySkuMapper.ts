import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Sku_skip_id_,
  Receipt_skip_value_,
  QuantityAccum,
  Sku,
  Receipt,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry (keyed by skuId), receive all Receipt values associated with that skuId. Emit one output pair whose key is the entry's key unchanged and whose value is the sum of the quantity field across all of the entry's values. When the entry has no values, this aggregation is not invoked (the entry does not exist); consumers consulting the resulting collection by a skuId with no receipts receive nothing, and the api method defaults to zero at read time.
export class OnHandBySkuMapper implements Mapper<
  Sku_skip_id_,
  Receipt_skip_value_,
  Sku_skip_id_,
  QuantityAccum
> {
  mapEntry(
    key: Sku_skip_id_,
    values: Values<Receipt_skip_value_>,
    context: Context,
  ): Iterable<[Sku_skip_id_, QuantityAccum]> {
    // > body
    let total = 0;
    for (const value of values.toArray()) {
      total += value.quantity;
    }
    return [[key, total]];
    // < body
  }
}
