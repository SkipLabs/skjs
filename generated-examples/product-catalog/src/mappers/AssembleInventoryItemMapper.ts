import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  InventoryItem_skip_id_,
  InventoryItem_skip_value_,
  InventoryItem,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each inventory item entry, emit one output pair whose key is the entry's key unchanged and whose value lists every required field of InventoryItem explicitly: productId sourced from the entry's key's productId field, warehouseId sourced from the entry's key's warehouseId field, quantity sourced from the entry's value's quantity field, reorderThreshold sourced from the entry's value's reorderThreshold field, createdAt sourced from the entry's value's createdAt field, updatedAt sourced from the entry's value's updatedAt field.
export class AssembleInventoryItemMapper implements Mapper<
  InventoryItem_skip_id_,
  InventoryItem_skip_value_,
  InventoryItem_skip_id_,
  InventoryItem
> {
  mapEntry(
    key: InventoryItem_skip_id_,
    values: Values<InventoryItem_skip_value_>,
    context: Context,
  ): Iterable<[InventoryItem_skip_id_, InventoryItem]> {
    // > body
    const emits: [InventoryItem_skip_id_, InventoryItem][] = [];
    for (const value of values.toArray()) {
      const item: InventoryItem = {
        productId: key.productId,
        warehouseId: key.warehouseId,
        quantity: value.quantity,
        reorderThreshold: value.reorderThreshold,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
      };
      emits.push([key, item]);
    }
    return emits;
    // < body
  }
}
