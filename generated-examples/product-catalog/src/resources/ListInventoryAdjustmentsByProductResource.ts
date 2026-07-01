import type { ProductIdKey, InventoryAdjustment } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListInventoryAdjustmentsByProductResourceInputs extends SharedCollections {
  readonly adjustmentsByProduct: EagerCollection<
    ProductIdKey,
    InventoryAdjustment
  >;
}

export class ListInventoryAdjustmentsByProductResource implements Resource<ListInventoryAdjustmentsByProductResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListInventoryAdjustmentsByProductResourceInputs,
    _context: Context,
  ): EagerCollection<ProductIdKey, InventoryAdjustment> {
    return inputs.adjustmentsByProduct;
  }
}
