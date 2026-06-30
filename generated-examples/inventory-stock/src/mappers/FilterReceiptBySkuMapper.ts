import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Receipt_skip_id_,
  Receipt_skip_value_,
  Receipt,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each receipt entry, when the skuId param is absent emit the entry unchanged. Otherwise, emit the entry unchanged when the entry's skuId field equals the skuId param; emit nothing otherwise.
export class FilterReceiptBySkuMapper implements Mapper<
  Receipt_skip_id_,
  Receipt_skip_value_,
  Receipt_skip_id_,
  Receipt_skip_value_
> {
  constructor(private skuId: string | null) {}

  mapEntry(
    key: Receipt_skip_id_,
    values: Values<Receipt_skip_value_>,
    context: Context,
  ): Iterable<[Receipt_skip_id_, Receipt_skip_value_]> {
    // > body
    const emits: [Receipt_skip_id_, Receipt_skip_value_][] = [];
    for (const value of values.toArray()) {
      if (this.skuId === null || value.skuId === this.skuId) {
        emits.push([key, value]);
      }
    }
    return emits;
    // < body
  }
}
