import type {
  Sku_skip_id_,
  Receipt_skip_value_,
  Sku,
  Receipt,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ReceiptsBySkuResourceInputs extends SharedCollections {
  readonly receiptsBySku: EagerCollection<Sku_skip_id_, Receipt_skip_value_>;
}

export class ReceiptsBySkuResource implements Resource<ReceiptsBySkuResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ReceiptsBySkuResourceInputs,
    _context: Context,
  ): EagerCollection<Sku_skip_id_, Receipt_skip_value_> {
    return inputs.receiptsBySku;
  }
}
