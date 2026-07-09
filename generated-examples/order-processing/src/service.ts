import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetOrderResource } from "./resources/GetOrderResource.js";
import { GetOrderStoredResource } from "./resources/GetOrderStoredResource.js";
import { GetProductResource } from "./resources/GetProductResource.js";
import { ListOrderLinesResource } from "./resources/ListOrderLinesResource.js";
import { ListOrdersResource } from "./resources/ListOrdersResource.js";
import { ListProductsResource } from "./resources/ListProductsResource.js";
import { OrderLinesByOrderResource } from "./resources/OrderLinesByOrderResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  OrderLineKey,
  OrderLine_skip_value_,
  Order_skip_id_,
  OrderStored,
  Product_skip_id_,
  Product_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetOrderParams,
  ListOrderLinesParams,
  ListOrdersParams,
  ListProductsParams,
  OrderLine,
  Order,
  Product,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  ExternalService,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly orderLines: InputDefinition<OrderLineKey, OrderLine_skip_value_>;
  readonly orders: InputDefinition<Order_skip_id_, OrderStored>;
  readonly products: InputDefinition<Product_skip_id_, Product_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getOrderResource: ResourceClass<GraphCollections, GetOrderParams>;
  readonly getOrderStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getProductResource: ResourceClass<GraphCollections, Json>;
  readonly listOrderLinesResource: ResourceClass<
    GraphCollections,
    ListOrderLinesParams
  >;
  readonly listOrdersResource: ResourceClass<
    GraphCollections,
    ListOrdersParams
  >;
  readonly listProductsResource: ResourceClass<
    GraphCollections,
    ListProductsParams
  >;
  readonly orderLinesByOrderResource: ResourceClass<GraphCollections, Json>;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;
  externalServices: { [name: string]: ExternalService } = {};

  constructor() {
    this.inputs = {
      orderLines: new InputDefinition<OrderLineKey, OrderLine_skip_value_>([]),
      orders: new InputDefinition<Order_skip_id_, OrderStored>([]),
      products: new InputDefinition<Product_skip_id_, Product_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getOrderResource: GetOrderResource,
      getOrderStoredResource: GetOrderStoredResource,
      getProductResource: GetProductResource,
      listOrderLinesResource: ListOrderLinesResource,
      listOrdersResource: ListOrdersResource,
      listProductsResource: ListProductsResource,
      orderLinesByOrderResource: OrderLinesByOrderResource,
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
