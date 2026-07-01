import type { Sku_skip_id_, Order_skip_value_, Sku, Order } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface OrdersBySkuResourceInputs extends SharedCollections {
  readonly ordersBySku: EagerCollection<Sku_skip_id_, Order_skip_value_>;
}

export class OrdersBySkuResource implements Resource<OrdersBySkuResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: OrdersBySkuResourceInputs,
    _context: Context,
  ): EagerCollection<Sku_skip_id_, Order_skip_value_> {
    return inputs.ordersBySku;
  }
}
