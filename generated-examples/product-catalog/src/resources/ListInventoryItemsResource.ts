import { AssembleInventoryItemMapper } from "../mappers/AssembleInventoryItemMapper.js";
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

export interface ListInventoryItemsResourceInputs extends SharedCollections {
  readonly inventoryItems: EagerCollection<
    InventoryItem_skip_id_,
    InventoryItem_skip_value_
  >;
}

export class ListInventoryItemsResource implements Resource<ListInventoryItemsResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListInventoryItemsResourceInputs,
    _context: Context,
  ): EagerCollection<InventoryItem_skip_id_, InventoryItem> {
    return inputs.inventoryItems.map(AssembleInventoryItemMapper);
  }
}
