import { ReceiptBySkuMapper } from "../mappers/ReceiptBySkuMapper.js";
import type {
  Receipt_skip_id_,
  Receipt_skip_value_,
  Sku_skip_id_,
  Receipt,
  Sku,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ReceiptsBySkuResourceInputs extends SharedCollections {
  readonly receipts: EagerCollection<Receipt_skip_id_, Receipt_skip_value_>;
}

export class ReceiptsBySkuResource implements Resource<ReceiptsBySkuResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ReceiptsBySkuResourceInputs,
    _context: Context,
  ): EagerCollection<Sku_skip_id_, Receipt> {
    return inputs.receipts.map(ReceiptBySkuMapper);
  }
}
