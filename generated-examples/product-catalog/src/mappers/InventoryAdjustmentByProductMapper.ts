import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  InventoryAdjustment_skip_id_,
  InventoryAdjustment_skip_value_,
  ProductIdKey,
  InventoryAdjustment,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each inventory adjustment entry, emit one output pair whose key is sourced from the entry's value at the productId field, paired with a new value listing every required field of InventoryAdjustment explicitly: id sourced from the entry's key, productId sourced from the entry's value at productId, delta sourced from the entry's value at delta, resultingStock sourced from the entry's value at resultingStock, reason sourced from the entry's value at reason, actorId sourced from the entry's value at actorId, createdAt sourced from the entry's value at createdAt.
export class InventoryAdjustmentByProductMapper implements Mapper<
  InventoryAdjustment_skip_id_,
  InventoryAdjustment_skip_value_,
  ProductIdKey,
  InventoryAdjustment
> {
  mapEntry(
    key: InventoryAdjustment_skip_id_,
    values: Values<InventoryAdjustment_skip_value_>,
    context: Context,
  ): Iterable<[ProductIdKey, InventoryAdjustment]> {
    // > body
    const emits: [ProductIdKey, InventoryAdjustment][] = [];
    for (const value of values.toArray()) {
      const adjustment: InventoryAdjustment = {
        id: key,
        productId: value.productId,
        delta: value.delta,
        resultingStock: value.resultingStock,
        actorId: value.actorId,
        createdAt: value.createdAt,
        ...(value.reason !== undefined && { reason: value.reason }),
      };
      emits.push([value.productId, adjustment]);
    }
    return emits;
    // < body
  }
}
