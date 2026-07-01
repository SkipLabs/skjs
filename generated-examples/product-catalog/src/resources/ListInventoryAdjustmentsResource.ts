import { FilterAdjustmentsByProductMapper } from "../mappers/FilterAdjustmentsByProductMapper.js";
import type {
  ProductIdKey,
  InventoryAdjustment,
  ListInventoryAdjustmentsParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListInventoryAdjustmentsResourceInputs extends SharedCollections {
  readonly adjustmentsByProduct: EagerCollection<
    ProductIdKey,
    InventoryAdjustment
  >;
}

export class ListInventoryAdjustmentsResource implements Resource<ListInventoryAdjustmentsResourceInputs> {
  private readonly productId: string;

  constructor(params: ListInventoryAdjustmentsParams) {
    this.productId = params.productId;
  }

  instantiate(
    inputs: ListInventoryAdjustmentsResourceInputs,
    _context: Context,
  ): EagerCollection<ProductIdKey, InventoryAdjustment> {
    return inputs.adjustmentsByProduct.map(
      FilterAdjustmentsByProductMapper,
      this.productId,
    );
  }
}
