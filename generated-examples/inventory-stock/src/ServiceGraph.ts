import { OrderBySkuMapper } from "./mappers/OrderBySkuMapper.js";
import { ReceiptBySkuMapper } from "./mappers/ReceiptBySkuMapper.js";
import { SkuAvailabilityMapper } from "./mappers/SkuAvailabilityMapper.js";
import type {
  Order_skip_id_,
  Order,
  Order_skip_value_,
  Receipt_skip_id_,
  Receipt,
  Receipt_skip_value_,
  Sku_skip_id_,
  Sku,
  Sku_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  SkuAvailability,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly orders: EagerCollection<Order_skip_id_, Order_skip_value_>;
  readonly receipts: EagerCollection<Receipt_skip_id_, Receipt_skip_value_>;
  readonly skus: EagerCollection<Sku_skip_id_, Sku_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly orders: EagerCollection<Order_skip_id_, Order_skip_value_>;
  readonly receipts: EagerCollection<Receipt_skip_id_, Receipt_skip_value_>;
  readonly skuAvailability: EagerCollection<Sku_skip_id_, SkuAvailability>;
  readonly skus: EagerCollection<Sku_skip_id_, Sku_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const ordersBySku = inputs.orders.map(OrderBySkuMapper);
  const output_orders = inputs.orders;
  const output_receipts = inputs.receipts;
  const receiptsBySku = inputs.receipts.map(ReceiptBySkuMapper);
  const output_skuAvailability = inputs.skus.map(
    SkuAvailabilityMapper,
    receiptsBySku,
    ordersBySku,
  );
  const output_skus = inputs.skus;
  const output_users = inputs.users;
  return {
    orders: output_orders,
    receipts: output_receipts,
    skuAvailability: output_skuAvailability,
    skus: output_skus,
    users: output_users,
  };
}
