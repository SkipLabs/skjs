import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Reducer,
  Values,
  Nullable,
  DepSafe
} from "@skipruntime/core";

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

type Inputs = {
  products: Entry<ProductId, ProductValue>[];
  orders: Entry<OrderId, OrderValue>[];
  receipts: Entry<ReceiptId, ReceiptValue>[];
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

type Resources = {
  "availability": new (params: Json) => Resource<GraphCollections>;
};

export class OrderToProductMapper implements Mapper<OrderId, OrderValue, ProductId, StockChange> {
  constructor() {
  }

  mapEntry(
    _key: OrderId,
    values: Values<OrderValue>,
    _context: Context
  ): Iterable<[ProductId, StockChange]> {
    const arr = values.toArray();
    const result: Array<[ProductId, StockChange]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const order = arr[i]!;
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
    const arr = values.toArray();
    const result: Array<[ProductId, StockChange]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const receipt = arr[i]!;
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
    const arr = values.toArray();
    const result: Array<[AvailabilityId, AvailabilityValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const product = arr[i]!;
      const orderTotalArr = this.orderTotals.getArray(key);
      const receiptTotalArr = this.receiptTotals.getArray(key);
      const totalOrdered = orderTotalArr.length > 0 ? orderTotalArr[0]!.total : 0;
      const totalReceived = receiptTotalArr.length > 0 ? receiptTotalArr[0]!.total : 0;
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
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<AvailabilityId, AvailabilityValue> {
    return cs.availability;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyProducts: Entry<ProductId, ProductValue>[] = Array.of();
    const emptyOrders: Entry<OrderId, OrderValue>[] = Array.of();
    const emptyReceipts: Entry<ReceiptId, ReceiptValue>[] = Array.of();
    this.initialData = { products: emptyProducts, orders: emptyOrders, receipts: emptyReceipts };
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

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
