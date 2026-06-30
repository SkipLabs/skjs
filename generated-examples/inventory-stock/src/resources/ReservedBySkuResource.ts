import type { Sku_skip_id_, QuantityAccum, Sku } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ReservedBySkuResourceInputs extends SharedCollections {
  readonly reservedBySku: EagerCollection<Sku_skip_id_, QuantityAccum>;
}

export class ReservedBySkuResource implements Resource<ReservedBySkuResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ReservedBySkuResourceInputs,
    _context: Context,
  ): EagerCollection<Sku_skip_id_, QuantityAccum> {
    return inputs.reservedBySku;
  }
}
