import { LineItemsByOrderMapper } from "./mappers/LineItemsByOrderMapper.js";
import { PaymentsByOrderMapper } from "./mappers/PaymentsByOrderMapper.js";
import type {
  OrderLineItemKey,
  OrderLineItemStored,
  Order_skip_id_,
  Order,
  OrderStored,
  Payment_skip_id_,
  Payment,
  Payment_skip_value_,
  Product_skip_id_,
  Product,
  Product_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  OrderLineItemForOrder,
  PaymentForOrder,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly orderLineItems: EagerCollection<
    OrderLineItemKey,
    OrderLineItemStored
  >;
  readonly orders: EagerCollection<Order_skip_id_, OrderStored>;
  readonly payments: EagerCollection<Payment_skip_id_, Payment_skip_value_>;
  readonly products: EagerCollection<Product_skip_id_, Product_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly lineItemsByOrder: EagerCollection<
    Order_skip_id_,
    OrderLineItemForOrder
  >;
  readonly orders: EagerCollection<Order_skip_id_, OrderStored>;
  readonly paymentsByOrder: EagerCollection<Order_skip_id_, PaymentForOrder>;
  readonly products: EagerCollection<Product_skip_id_, Product_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const lineItemsByOrder = inputs.orderLineItems.map(LineItemsByOrderMapper);
  const output_lineItemsByOrder = lineItemsByOrder;
  const output_orders = inputs.orders;
  const paymentsByOrder = inputs.payments.map(PaymentsByOrderMapper);
  const output_paymentsByOrder = paymentsByOrder;
  const output_products = inputs.products;
  const output_users = inputs.users;
  return {
    lineItemsByOrder: output_lineItemsByOrder,
    orders: output_orders,
    paymentsByOrder: output_paymentsByOrder,
    products: output_products,
    users: output_users,
  };
}
