import type {
  EagerCollection,
  Json,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable,
  DepSafe
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  ProductId,
  ProductValue,
  OrderId,
  OrderValue,
  ReceiptId,
  ReceiptValue,
  AvailabilityId,
  AvailabilityValue,
} from "./types.js";

export type StockChange = {
  quantity: number;
};

export type StockAccum = {
  total: number;
};

export type Inputs = {
  products: InputDefinition<ProductId, ProductValue>;
  orders: InputDefinition<OrderId, OrderValue>;
  receipts: InputDefinition<ReceiptId, ReceiptValue>;
};

export type InputCollections = {
  products: EagerCollection<ProductId, ProductValue>;
  orders: EagerCollection<OrderId, OrderValue>;
  receipts: EagerCollection<ReceiptId, ReceiptValue>;
};

export type GraphCollections = {
  products: EagerCollection<ProductId, ProductValue>;
  orders: EagerCollection<OrderId, OrderValue>;
  receipts: EagerCollection<ReceiptId, ReceiptValue>;
  orderTotals: EagerCollection<ProductId, StockAccum>;
  receiptTotals: EagerCollection<ProductId, StockAccum>;
  availability: EagerCollection<AvailabilityId, AvailabilityValue>;
};

export type Resources = {
  readonly "availability": ResourceClass<GraphCollections, {}>;
};

export class OrderToProductMapper implements Mapper<OrderId, OrderValue, ProductId, StockChange> {
  constructor() {
  }

  mapEntry(
    _key: OrderId,
    values: Values<OrderValue>,
    _context: Context
  ): Iterable<[ProductId, StockChange]> {
    const result: Array<[ProductId, StockChange]> = Array.of();
    for (const order of values) {
      result.push([order.productId, { quantity: order.quantity }]);
    }
    return result;
  }
}

export class ReceiptToProductMapper implements Mapper<ReceiptId, ReceiptValue, ProductId, StockChange> {
  constructor() {
  }

  mapEntry(
    _key: ReceiptId,
    values: Values<ReceiptValue>,
    _context: Context
  ): Iterable<[ProductId, StockChange]> {
    const result: Array<[ProductId, StockChange]> = Array.of();
    for (const receipt of values) {
      result.push([receipt.productId, { quantity: receipt.quantity }]);
    }
    return result;
  }
}

export class AvailabilityMapper implements Mapper<ProductId, ProductValue, AvailabilityId, AvailabilityValue> {
  private orderTotals: EagerCollection<ProductId, StockAccum>;
  private receiptTotals: EagerCollection<ProductId, StockAccum>;

  constructor(
    orderTotals: EagerCollection<ProductId, StockAccum> & DepSafe,
    receiptTotals: EagerCollection<ProductId, StockAccum> & DepSafe
  ) {
    this.orderTotals = orderTotals;
    this.receiptTotals = receiptTotals;
  }

  mapEntry(
    key: ProductId,
    values: Values<ProductValue>,
    _context: Context
  ): Iterable<[AvailabilityId, AvailabilityValue]> {
    const result: Array<[AvailabilityId, AvailabilityValue]> = Array.of();
    for (const product of values) {
      const orderTotalArr = this.orderTotals.getArray(key);
      const receiptTotalArr = this.receiptTotals.getArray(key);
      const orderEntry = orderTotalArr[0];
      const receiptEntry = receiptTotalArr[0];
      const totalOrdered = orderEntry !== undefined ? orderEntry.total : 0;
      const totalReceived = receiptEntry !== undefined ? receiptEntry.total : 0;
      const currentStock = product.initialStock - totalOrdered + totalReceived;
      result.push([key, {
        productId: key,
        productName: product.name,
        initialStock: product.initialStock,
        totalOrdered: totalOrdered,
        totalReceived: totalReceived,
        currentStock: currentStock
      }]);
    }
    return result;
  }
}

export class StockReducer implements Reducer<StockChange, StockAccum> {
  initial: Nullable<StockAccum> = null;

  constructor() {
  }

  add(accum: Nullable<StockAccum>, value: StockChange): StockAccum {
    if (accum === null) {
      return { total: value.quantity };
    }
    return { total: accum.total + value.quantity };
  }

  remove(accum: StockAccum, value: StockChange): Nullable<StockAccum> {
    const newTotal = accum.total - value.quantity;
    if (newTotal === 0) {
      return null;
    }
    return { total: newTotal };
  }
}

export class AvailabilityResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AvailabilityId, AvailabilityValue> {
    return cs.availability;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
                this.inputs = { products: new InputDefinition<ProductId, ProductValue>([]), orders: new InputDefinition<OrderId, OrderValue>([]), receipts: new InputDefinition<ReceiptId, ReceiptValue>([]) };
    this.resources = { "availability": AvailabilityResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const orderTotals = inputs.orders.map(OrderToProductMapper).reduce(StockReducer);
    const receiptTotals = inputs.receipts.map(ReceiptToProductMapper).reduce(StockReducer);
    const availability = inputs.products.map(AvailabilityMapper, orderTotals, receiptTotals);
    return {
      products: inputs.products,
      orders: inputs.orders,
      receipts: inputs.receipts,
      orderTotals: orderTotals,
      receiptTotals: receiptTotals,
      availability: availability
    };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
