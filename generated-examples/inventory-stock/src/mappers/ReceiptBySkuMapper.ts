import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Receipt_skip_id_,
  Receipt_skip_value_,
  Sku_skip_id_,
  Receipt,
  Sku,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each receipt entry, emit one output pair whose key is sourced from the entry's value's skuId field. The output value lists every required field of Receipt explicitly: id sourced from the entry's key; ownerId sourced from the entry's value's ownerId field; skuId sourced from the entry's value's skuId field; quantity sourced from the entry's value's quantity field; status sourced from the entry's value's status field; createdAt sourced from the entry's value's createdAt field. Optional fields: note is present when the entry's value's note field is present, sourced from that field; absent otherwise. receivedAt is present when the entry's value's receivedAt field is present, sourced from that field; absent otherwise. The original receipt id from the entry's key is preserved as the id field of the output value so consumers can reconstruct full Receipt records.
export class ReceiptBySkuMapper implements Mapper<
  Receipt_skip_id_,
  Receipt_skip_value_,
  Sku_skip_id_,
  Receipt
> {
  mapEntry(
    key: Receipt_skip_id_,
    values: Values<Receipt_skip_value_>,
    context: Context,
  ): Iterable<[Sku_skip_id_, Receipt]> {
    // > body
    const emits: [Sku_skip_id_, Receipt][] = [];
    for (const value of values.toArray()) {
      const receipt: Receipt = {
        id: key,
        ownerId: value.ownerId,
        skuId: value.skuId,
        quantity: value.quantity,
        status: value.status,
        createdAt: value.createdAt,
        ...(value.note !== undefined && { note: value.note }),
        ...(value.receivedAt !== undefined && { receivedAt: value.receivedAt }),
      };
      emits.push([value.skuId, receipt]);
    }
    return emits;
    // < body
  }
}
