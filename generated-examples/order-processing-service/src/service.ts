import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values,
  DepSafe
} from "@skipruntime/core";

import type {
  CustomerId,
  CustomerValue,
  ProductId,
  ProductValue,
  OrderId,
  OrderValue,
  OrderSummaryId,
  OrderSummaryValue,
} from "./types.js";


type Inputs = {
  customers: Entry<CustomerId, CustomerValue>[];
  products: Entry<ProductId, ProductValue>[];
  orders: Entry<OrderId, OrderValue>[];
};

export type InputCollections = {
  customers: EagerCollection<CustomerId, CustomerValue>;
  products: EagerCollection<ProductId, ProductValue>;
  orders: EagerCollection<OrderId, OrderValue>;
};

export type GraphCollections = {
  customers: EagerCollection<CustomerId, CustomerValue>;
  products: EagerCollection<ProductId, ProductValue>;
  orders: EagerCollection<OrderId, OrderValue>;
  orderSummaries: EagerCollection<OrderSummaryId, OrderSummaryValue>;
};

type Resources = {
  "customers": new (params: Json) => Resource<GraphCollections>;
  "products": new (params: Json) => Resource<GraphCollections>;
  "orders": new (params: Json) => Resource<GraphCollections>;
};

export class OrderSummaryMapper implements Mapper<OrderId, OrderValue, OrderSummaryId, OrderSummaryValue> {
  private customers: EagerCollection<CustomerId, CustomerValue>;

  constructor(customers: EagerCollection<CustomerId, CustomerValue>) {
    this.customers = customers;
  }

  mapEntry(
    key: OrderId,
    values: Values<OrderValue>,
    _context: Context
  ): Iterable<[OrderSummaryId, OrderSummaryValue]> {
    const result: Array<[OrderSummaryId, OrderSummaryValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const order: OrderValue & DepSafe = arr[i]!;
      const customerArr = this.customers.getArray(order.customerId);
      let customerName = "Unknown";
      if (customerArr.length > 0) {
        customerName = customerArr[0]!.name;
      }
      let itemCount = 0;
      let totalAmount = 0;
      const items = order.items;
      for (let j = 0; j < items.length; j++) {
        const item = items[j]!;
        itemCount = itemCount + item.quantity;
        totalAmount = totalAmount + (item.quantity * item.unitPrice);
      }
      const summary: OrderSummaryValue = {
        customerId: order.customerId,
        customerName: customerName,
        itemCount: itemCount,
        totalAmount: totalAmount,
        status: order.status,
        createdAt: order.createdAt
      };
      result.push([key, summary]);
    }
    return result;
  }
}

export class CustomersResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CustomerId, CustomerValue> {
    return cs.customers;
  }
}

export class ProductsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProductId, ProductValue> {
    return cs.products;
  }
}

export class OrdersResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<OrderId, OrderValue> {
    return cs.orders;
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyCustomers: Entry<CustomerId, CustomerValue>[] = Array.of();
    const emptyProducts: Entry<ProductId, ProductValue>[] = Array.of();
    const emptyOrders: Entry<OrderId, OrderValue>[] = Array.of();
    this.initialData = { customers: emptyCustomers, products: emptyProducts, orders: emptyOrders };
    this.resources = { "customers": CustomersResource, "products": ProductsResource, "orders": OrdersResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    const orderSummaries = inputs.orders.map(OrderSummaryMapper, inputs.customers);
    return {
      customers: inputs.customers,
      products: inputs.products,
      orders: inputs.orders,
      orderSummaries: orderSummaries
    };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}
