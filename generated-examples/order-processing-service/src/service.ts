import type {
  EagerCollection,
  Json,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values,
  DepSafe
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

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


export type Inputs = {
  customers: InputDefinition<CustomerId, CustomerValue>;
  products: InputDefinition<ProductId, ProductValue>;
  orders: InputDefinition<OrderId, OrderValue>;
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

export type Resources = {
  readonly "customers": ResourceClass<GraphCollections, {}>;
  readonly "products": ResourceClass<GraphCollections, {}>;
  readonly "orders": ResourceClass<GraphCollections, {}>;
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
    for (const order of values) {
      const customerArr = this.customers.getArray(order.customerId);
      let customerName = "Unknown";
      const customerEntry = customerArr[0];
      if (customerEntry !== undefined) {
        customerName = customerEntry.name;
      }
      let itemCount = 0;
      let totalAmount = 0;
      const items = order.items;
      for (const item of items) {
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
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CustomerId, CustomerValue> {
    return cs.customers;
  }
}

export class ProductsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<ProductId, ProductValue> {
    return cs.products;
  }
}

export class OrdersResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<OrderId, OrderValue> {
    return cs.orders;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public readonly inputs: Inputs;
  public readonly resources: Resources;

  constructor() {
                this.inputs = { customers: new InputDefinition<CustomerId, CustomerValue>([]), products: new InputDefinition<ProductId, ProductValue>([]), orders: new InputDefinition<OrderId, OrderValue>([]) };
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

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}
