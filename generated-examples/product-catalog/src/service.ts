import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetProductResource } from "./resources/GetProductResource.js";
import { ListCategoriesResource } from "./resources/ListCategoriesResource.js";
import { ListInventoryAdjustmentsByProductResource } from "./resources/ListInventoryAdjustmentsByProductResource.js";
import { ListInventoryAdjustmentsResource } from "./resources/ListInventoryAdjustmentsResource.js";
import { ListProductsResource } from "./resources/ListProductsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Category_skip_id_,
  Category_skip_value_,
  InventoryAdjustment_skip_id_,
  InventoryAdjustment_skip_value_,
  Product_skip_id_,
  ProductStored,
  User_skip_id_,
  User_skip_value_,
  ListInventoryAdjustmentsParams,
  ListProductsParams,
  Category,
  InventoryAdjustment,
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
  readonly categories: InputDefinition<Category_skip_id_, Category_skip_value_>;
  readonly inventoryAdjustments: InputDefinition<
    InventoryAdjustment_skip_id_,
    InventoryAdjustment_skip_value_
  >;
  readonly products: InputDefinition<Product_skip_id_, ProductStored>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getProductResource: ResourceClass<GraphCollections, Json>;
  readonly listCategoriesResource: ResourceClass<GraphCollections, Json>;
  readonly listInventoryAdjustmentsByProductResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listInventoryAdjustmentsResource: ResourceClass<
    GraphCollections,
    ListInventoryAdjustmentsParams
  >;
  readonly listProductsResource: ResourceClass<
    GraphCollections,
    ListProductsParams
  >;
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
      categories: new InputDefinition<Category_skip_id_, Category_skip_value_>(
        [],
      ),
      inventoryAdjustments: new InputDefinition<
        InventoryAdjustment_skip_id_,
        InventoryAdjustment_skip_value_
      >([]),
      products: new InputDefinition<Product_skip_id_, ProductStored>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getProductResource: GetProductResource,
      listCategoriesResource: ListCategoriesResource,
      listInventoryAdjustmentsByProductResource:
        ListInventoryAdjustmentsByProductResource,
      listInventoryAdjustmentsResource: ListInventoryAdjustmentsResource,
      listProductsResource: ListProductsResource,
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
