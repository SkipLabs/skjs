import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetOrderResource } from "./resources/GetOrderResource.js";
import { GetReceiptResource } from "./resources/GetReceiptResource.js";
import { GetSkuAvailabilityResource } from "./resources/GetSkuAvailabilityResource.js";
import { GetSkuResource } from "./resources/GetSkuResource.js";
import { ListOrdersResource } from "./resources/ListOrdersResource.js";
import { ListReceiptsResource } from "./resources/ListReceiptsResource.js";
import { ListSkusResource } from "./resources/ListSkusResource.js";
import { OrdersBySkuResource } from "./resources/OrdersBySkuResource.js";
import { ReceiptsBySkuResource } from "./resources/ReceiptsBySkuResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Order_skip_id_,
  Order_skip_value_,
  Receipt_skip_id_,
  Receipt_skip_value_,
  Sku_skip_id_,
  Sku_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListOrdersParams,
  ListReceiptsParams,
  ListSkusParams,
  Order,
  Receipt,
  Sku,
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
  readonly orders: InputDefinition<Order_skip_id_, Order_skip_value_>;
  readonly receipts: InputDefinition<Receipt_skip_id_, Receipt_skip_value_>;
  readonly skus: InputDefinition<Sku_skip_id_, Sku_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getOrderResource: ResourceClass<GraphCollections, Json>;
  readonly getReceiptResource: ResourceClass<GraphCollections, Json>;
  readonly getSkuAvailabilityResource: ResourceClass<GraphCollections, Json>;
  readonly getSkuResource: ResourceClass<GraphCollections, Json>;
  readonly listOrdersResource: ResourceClass<
    GraphCollections,
    ListOrdersParams
  >;
  readonly listReceiptsResource: ResourceClass<
    GraphCollections,
    ListReceiptsParams
  >;
  readonly listSkusResource: ResourceClass<GraphCollections, ListSkusParams>;
  readonly ordersBySkuResource: ResourceClass<GraphCollections, Json>;
  readonly receiptsBySkuResource: ResourceClass<GraphCollections, Json>;
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
      orders: new InputDefinition<Order_skip_id_, Order_skip_value_>([]),
      receipts: new InputDefinition<Receipt_skip_id_, Receipt_skip_value_>([]),
      skus: new InputDefinition<Sku_skip_id_, Sku_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getOrderResource: GetOrderResource,
      getReceiptResource: GetReceiptResource,
      getSkuAvailabilityResource: GetSkuAvailabilityResource,
      getSkuResource: GetSkuResource,
      listOrdersResource: ListOrdersResource,
      listReceiptsResource: ListReceiptsResource,
      listSkusResource: ListSkusResource,
      ordersBySkuResource: OrdersBySkuResource,
      receiptsBySkuResource: ReceiptsBySkuResource,
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
