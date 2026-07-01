import { AssembleLineItemMapper } from "../mappers/AssembleLineItemMapper.js";
import type { LineItem_skip_id_, LineItemStored, LineItem } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetLineItemResourceInputs extends SharedCollections {
  readonly lineItems: EagerCollection<LineItem_skip_id_, LineItemStored>;
}

export class GetLineItemResource implements Resource<GetLineItemResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetLineItemResourceInputs,
    _context: Context,
  ): EagerCollection<LineItem_skip_id_, LineItem> {
    return inputs.lineItems.map(AssembleLineItemMapper);
  }
}
