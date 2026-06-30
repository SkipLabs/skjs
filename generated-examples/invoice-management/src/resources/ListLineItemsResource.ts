import { LineItemByInvoiceMapper } from "../mappers/LineItemByInvoiceMapper.js";
import type {
  LineItem_skip_id_,
  LineItemStored,
  Invoice_skip_id_,
  LineItem,
  Invoice,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListLineItemsResourceInputs extends SharedCollections {
  readonly lineItems: EagerCollection<LineItem_skip_id_, LineItemStored>;
}

export class ListLineItemsResource implements Resource<ListLineItemsResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListLineItemsResourceInputs,
    _context: Context,
  ): EagerCollection<Invoice_skip_id_, LineItem> {
    return inputs.lineItems.map(LineItemByInvoiceMapper);
  }
}
