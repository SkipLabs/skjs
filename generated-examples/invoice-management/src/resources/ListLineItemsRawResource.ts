import type { LineItemKey, LineItemStored } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListLineItemsRawResourceInputs extends SharedCollections {
  readonly lineItems: EagerCollection<LineItemKey, LineItemStored>;
}

export class ListLineItemsRawResource implements Resource<ListLineItemsRawResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListLineItemsRawResourceInputs,
    _context: Context,
  ): EagerCollection<LineItemKey, LineItemStored> {
    return inputs.lineItems;
  }
}
