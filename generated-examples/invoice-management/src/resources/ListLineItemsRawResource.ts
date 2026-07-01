import type { LineItem_skip_id_, LineItemStored, LineItem } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListLineItemsRawResourceInputs extends SharedCollections {
  readonly lineItems: EagerCollection<LineItem_skip_id_, LineItemStored>;
}

export class ListLineItemsRawResource implements Resource<ListLineItemsRawResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListLineItemsRawResourceInputs,
    _context: Context,
  ): EagerCollection<LineItem_skip_id_, LineItemStored> {
    return inputs.lineItems;
  }
}
