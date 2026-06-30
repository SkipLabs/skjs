import type { Sku_skip_id_, QuantityAccum, Sku } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface OnHandBySkuResourceInputs extends SharedCollections {
  readonly onHandBySku: EagerCollection<Sku_skip_id_, QuantityAccum>;
}

export class OnHandBySkuResource implements Resource<OnHandBySkuResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: OnHandBySkuResourceInputs,
    _context: Context,
  ): EagerCollection<Sku_skip_id_, QuantityAccum> {
    return inputs.onHandBySku;
  }
}
