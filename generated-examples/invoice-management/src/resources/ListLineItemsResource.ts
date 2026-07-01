import type { Invoice_skip_id_, LineItem, Invoice } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListLineItemsResourceInputs extends SharedCollections {
  readonly lineItemsByInvoice: EagerCollection<Invoice_skip_id_, LineItem>;
}

export class ListLineItemsResource implements Resource<ListLineItemsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListLineItemsResourceInputs,
    _context: Context,
  ): EagerCollection<Invoice_skip_id_, LineItem> {
    return inputs.lineItemsByInvoice;
  }
}
