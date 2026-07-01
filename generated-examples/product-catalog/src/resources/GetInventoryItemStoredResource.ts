import type {
  InventoryItem_skip_id_,
  InventoryItem_skip_value_,
  InventoryItem,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetInventoryItemStoredResourceInputs extends SharedCollections {
  readonly inventoryItems: EagerCollection<
    InventoryItem_skip_id_,
    InventoryItem_skip_value_
  >;
}

export class GetInventoryItemStoredResource implements Resource<GetInventoryItemStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetInventoryItemStoredResourceInputs,
    _context: Context,
  ): EagerCollection<InventoryItem_skip_id_, InventoryItem_skip_value_> {
    return inputs.inventoryItems;
  }
}
