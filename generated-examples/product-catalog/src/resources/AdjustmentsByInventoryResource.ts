import { AdjustmentByInventoryKeyMapper } from "../mappers/AdjustmentByInventoryKeyMapper.js";
import type {
  InventoryAdjustment_skip_id_,
  InventoryAdjustment_skip_value_,
  InventoryItemKey,
  InventoryAdjustment,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface AdjustmentsByInventoryResourceInputs extends SharedCollections {
  readonly inventoryAdjustments: EagerCollection<
    InventoryAdjustment_skip_id_,
    InventoryAdjustment_skip_value_
  >;
}

export class AdjustmentsByInventoryResource implements Resource<AdjustmentsByInventoryResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: AdjustmentsByInventoryResourceInputs,
    _context: Context,
  ): EagerCollection<InventoryItemKey, InventoryAdjustment> {
    return inputs.inventoryAdjustments.map(AdjustmentByInventoryKeyMapper);
  }
}
