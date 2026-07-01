import type {
  OrderLineKey,
  OrderLine_skip_value_,
  OrderLine,
  Order_skip_id_,
  Order,
  OrderStored,
  Product_skip_id_,
  Product,
  Product_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly orderLines: EagerCollection<OrderLineKey, OrderLine_skip_value_>;
  readonly orders: EagerCollection<Order_skip_id_, OrderStored>;
  readonly products: EagerCollection<Product_skip_id_, Product_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly orderLines: EagerCollection<OrderLineKey, OrderLine_skip_value_>;
  readonly orders: EagerCollection<Order_skip_id_, OrderStored>;
  readonly products: EagerCollection<Product_skip_id_, Product_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_orderLines = inputs.orderLines;
  const output_orders = inputs.orders;
  const output_products = inputs.products;
  const output_users = inputs.users;
  return {
    orderLines: output_orderLines,
    orders: output_orders,
    products: output_products,
    users: output_users,
  };
}
