import type { Order_skip_id_, OrderLineItemForOrder, Order } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListLineItemsByOrderResourceInputs extends SharedCollections {
  readonly lineItemsByOrder: EagerCollection<
    Order_skip_id_,
    OrderLineItemForOrder
  >;
}

export class ListLineItemsByOrderResource implements Resource<ListLineItemsByOrderResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListLineItemsByOrderResourceInputs,
    _context: Context,
  ): EagerCollection<Order_skip_id_, OrderLineItemForOrder> {
    return inputs.lineItemsByOrder;
  }
}
