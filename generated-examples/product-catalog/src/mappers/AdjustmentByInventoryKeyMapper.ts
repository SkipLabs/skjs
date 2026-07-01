import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  InventoryAdjustment_skip_id_,
  InventoryAdjustment_skip_value_,
  InventoryItemKey,
  InventoryAdjustment,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each adjustment entry, emit one output pair whose key is a record with productId sourced from the entry's value's productId field and warehouseId sourced from the entry's value's warehouseId field, and whose value lists every required field of InventoryAdjustment explicitly: id sourced from the entry's key, productId sourced from the entry's value's productId field, warehouseId sourced from the entry's value's warehouseId field, delta sourced from the entry's value's delta field, resultingQuantity sourced from the entry's value's resultingQuantity field, reason sourced from the entry's value's reason field, actorUserId sourced from the entry's value's actorUserId field, occurredAt sourced from the entry's value's occurredAt field; the optional field note is present when the entry's value's note field is present, sourced from that field; absent otherwise. The original adjustment id from the input key is re-injected as the value's id so the downstream consumer can reconstruct the full InventoryAdjustment entity.
export class AdjustmentByInventoryKeyMapper implements Mapper<
  InventoryAdjustment_skip_id_,
  InventoryAdjustment_skip_value_,
  InventoryItemKey,
  InventoryAdjustment
> {
  mapEntry(
    key: InventoryAdjustment_skip_id_,
    values: Values<InventoryAdjustment_skip_value_>,
    context: Context,
  ): Iterable<[InventoryItemKey, InventoryAdjustment]> {
    // > body
    const emits: [InventoryItemKey, InventoryAdjustment][] = [];
    for (const value of values.toArray()) {
      const adjustment: InventoryAdjustment = {
        id: key,
        productId: value.productId,
        warehouseId: value.warehouseId,
        delta: value.delta,
        resultingQuantity: value.resultingQuantity,
        reason: value.reason,
        actorUserId: value.actorUserId,
        occurredAt: value.occurredAt,
        ...(value.note !== undefined && { note: value.note }),
      };
      emits.push([
        { productId: value.productId, warehouseId: value.warehouseId },
        adjustment,
      ]);
    }
    return emits;
    // < body
  }
}
