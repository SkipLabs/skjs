import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetOrderResource } from "./resources/GetOrderResource.js";
import { GetProductResource } from "./resources/GetProductResource.js";
import { ListLineItemsByOrderResource } from "./resources/ListLineItemsByOrderResource.js";
import { ListOrdersResource } from "./resources/ListOrdersResource.js";
import { ListPaymentsByOrderResource } from "./resources/ListPaymentsByOrderResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  OrderLineItemKey,
  OrderLineItemStored,
  Order_skip_id_,
  OrderStored,
  Payment_skip_id_,
  Payment_skip_value_,
  Product_skip_id_,
  Product_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListOrdersParams,
  Order,
  Payment,
  Product,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly orderLineItems: InputDefinition<
    OrderLineItemKey,
    OrderLineItemStored
  >;
  readonly orders: InputDefinition<Order_skip_id_, OrderStored>;
  readonly payments: InputDefinition<Payment_skip_id_, Payment_skip_value_>;
  readonly products: InputDefinition<Product_skip_id_, Product_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getOrderResource: ResourceClass<GraphCollections, Json>;
  readonly getProductResource: ResourceClass<GraphCollections, Json>;
  readonly listLineItemsByOrderResource: ResourceClass<GraphCollections, Json>;
  readonly listOrdersResource: ResourceClass<
    GraphCollections,
    ListOrdersParams
  >;
  readonly listPaymentsByOrderResource: ResourceClass<GraphCollections, Json>;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;

  constructor() {
    this.inputs = {
      orderLineItems: new InputDefinition<
        OrderLineItemKey,
        OrderLineItemStored
      >([]),
      orders: new InputDefinition<Order_skip_id_, OrderStored>([]),
      payments: new InputDefinition<Payment_skip_id_, Payment_skip_value_>([]),
      products: new InputDefinition<Product_skip_id_, Product_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getOrderResource: GetOrderResource,
      getProductResource: GetProductResource,
      listLineItemsByOrderResource: ListLineItemsByOrderResource,
      listOrdersResource: ListOrdersResource,
      listPaymentsByOrderResource: ListPaymentsByOrderResource,
      getMeResource: getMeResource,
    };
  }

  createGraph(inputs: InputCollections, context: Context): GraphCollections {
    return createGraph(inputs, context);
  }
}

export function service(): SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  return new Service();
}
