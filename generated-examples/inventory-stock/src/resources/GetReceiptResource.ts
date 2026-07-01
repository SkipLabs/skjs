import type {
  Receipt_skip_id_,
  Receipt_skip_value_,
  Receipt,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetReceiptResourceInputs extends SharedCollections {
  readonly receipts: EagerCollection<Receipt_skip_id_, Receipt_skip_value_>;
}

export class GetReceiptResource implements Resource<GetReceiptResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetReceiptResourceInputs,
    _context: Context,
  ): EagerCollection<Receipt_skip_id_, Receipt_skip_value_> {
    return inputs.receipts;
  }
}
