import { OrderBySkuMapper } from "../mappers/OrderBySkuMapper.js";
import type {
  Order_skip_id_,
  Order_skip_value_,
  Sku_skip_id_,
  Order,
  Sku,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface OrdersBySkuResourceInputs extends SharedCollections {
  readonly orders: EagerCollection<Order_skip_id_, Order_skip_value_>;
}

export class OrdersBySkuResource implements Resource<OrdersBySkuResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: OrdersBySkuResourceInputs,
    _context: Context,
  ): EagerCollection<Sku_skip_id_, Order> {
    return inputs.orders.map(OrderBySkuMapper);
  }
}
