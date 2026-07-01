import { OnHandBySkuMapper } from "./mappers/OnHandBySkuMapper.js";
import { OrderBySkuMapper } from "./mappers/OrderBySkuMapper.js";
import { ReceiptBySkuMapper } from "./mappers/ReceiptBySkuMapper.js";
import { ReservedBySkuMapper } from "./mappers/ReservedBySkuMapper.js";
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
  QuantityAccum,
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
  readonly onHandBySku: EagerCollection<Sku_skip_id_, QuantityAccum>;
  readonly orders: EagerCollection<Order_skip_id_, Order_skip_value_>;
  readonly ordersBySku: EagerCollection<Sku_skip_id_, Order_skip_value_>;
  readonly receipts: EagerCollection<Receipt_skip_id_, Receipt_skip_value_>;
  readonly receiptsBySku: EagerCollection<Sku_skip_id_, Receipt_skip_value_>;
  readonly reservedBySku: EagerCollection<Sku_skip_id_, QuantityAccum>;
  readonly skus: EagerCollection<Sku_skip_id_, Sku_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const receiptsBySku = inputs.receipts.map(ReceiptBySkuMapper);
  const onHandBySku = receiptsBySku.map(OnHandBySkuMapper);
  const ordersBySku = inputs.orders.map(OrderBySkuMapper);
  const output_onHandBySku = onHandBySku;
  const output_orders = inputs.orders;
  const output_ordersBySku = ordersBySku;
  const output_receipts = inputs.receipts;
  const output_receiptsBySku = receiptsBySku;
  const reservedBySku = ordersBySku.map(ReservedBySkuMapper);
  const output_reservedBySku = reservedBySku;
  const output_skus = inputs.skus;
  const output_users = inputs.users;
  return {
    onHandBySku: output_onHandBySku,
    orders: output_orders,
    ordersBySku: output_ordersBySku,
    receipts: output_receipts,
    receiptsBySku: output_receiptsBySku,
    reservedBySku: output_reservedBySku,
    skus: output_skus,
    users: output_users,
  };
}
