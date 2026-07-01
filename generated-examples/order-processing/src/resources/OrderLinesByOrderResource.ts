import { OrderLineByOrderMapper } from "../mappers/OrderLineByOrderMapper.js";
import type {
  OrderLineKey,
  OrderLine_skip_value_,
  Order_skip_id_,
  OrderLineByOrderValue,
  OrderLine,
  Order,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface OrderLinesByOrderResourceInputs extends SharedCollections {
  readonly orderLines: EagerCollection<OrderLineKey, OrderLine_skip_value_>;
}

export class OrderLinesByOrderResource implements Resource<OrderLinesByOrderResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: OrderLinesByOrderResourceInputs,
    _context: Context,
  ): EagerCollection<Order_skip_id_, OrderLineByOrderValue> {
    const linesByOrder = inputs.orderLines.map(OrderLineByOrderMapper);
    return linesByOrder;
  }
}
