import type { Order_skip_id_, Order_skip_value_, Order } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetOrderResourceInputs extends SharedCollections {
  readonly orders: EagerCollection<Order_skip_id_, Order_skip_value_>;
}

export class GetOrderResource implements Resource<GetOrderResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetOrderResourceInputs,
    _context: Context,
  ): EagerCollection<Order_skip_id_, Order_skip_value_> {
    return inputs.orders;
  }
}
