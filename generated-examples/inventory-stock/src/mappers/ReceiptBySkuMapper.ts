import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Receipt_skip_id_,
  Receipt_skip_value_,
  Sku_skip_id_,
  Receipt,
  Sku,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each receipt entry, emit one output pair whose key is sourced from the entry's skuId field, paired with the entry's value unchanged. The original receipt id from the entry's key is dropped because the consumer only needs to sum quantities by sku — the receipt id is not needed by the downstream reservation/onHand computation.
export class ReceiptBySkuMapper implements Mapper<
  Receipt_skip_id_,
  Receipt_skip_value_,
  Sku_skip_id_,
  Receipt_skip_value_
> {
  mapEntry(
    key: Receipt_skip_id_,
    values: Values<Receipt_skip_value_>,
    context: Context,
  ): Iterable<[Sku_skip_id_, Receipt_skip_value_]> {
    // > body
    const emits: [Sku_skip_id_, Receipt_skip_value_][] = [];
    for (const value of values.toArray()) {
      emits.push([value.skuId, value]);
    }
    return emits;
    // < body
  }
}
