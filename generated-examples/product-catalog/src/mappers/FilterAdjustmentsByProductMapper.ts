import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type { ProductIdKey, InventoryAdjustment } from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each entry under the productId key: when the entry's key does not equal the productId param, emit nothing. Otherwise iterate the values associated with the key and for each value in the values list, emit one output pair whose key is the entry's key (the productId) paired with the value unchanged. (The input collection accumulates all inventory adjustments for the same product under one key because the upstream InventoryAdjustmentByProductMapper re-keys from the adjustment's id to its productId; singleton-only access would raise on any product with two or more adjustments.)
export class FilterAdjustmentsByProductMapper implements Mapper<
  ProductIdKey,
  InventoryAdjustment,
  ProductIdKey,
  InventoryAdjustment
> {
  constructor(private productId: string) {}

  mapEntry(
    key: ProductIdKey,
    values: Values<InventoryAdjustment>,
    context: Context,
  ): Iterable<[ProductIdKey, InventoryAdjustment]> {
    // > body
    if (key !== this.productId) return [];
    const emits: [ProductIdKey, InventoryAdjustment][] = [];
    for (const value of values.toArray()) {
      emits.push([key, value]);
    }
    return emits;
    // < body
  }
}
