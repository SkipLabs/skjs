import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { AdjustmentsByInventoryResource } from "./resources/AdjustmentsByInventoryResource.js";
import { GetInventoryItemStoredResource } from "./resources/GetInventoryItemStoredResource.js";
import { ListCategoriesResource } from "./resources/ListCategoriesResource.js";
import { ListInventoryItemsResource } from "./resources/ListInventoryItemsResource.js";
import { ListProductsResource } from "./resources/ListProductsResource.js";
import { ListWarehousesResource } from "./resources/ListWarehousesResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Category_skip_id_,
  Category_skip_value_,
  InventoryAdjustment_skip_id_,
  InventoryAdjustment_skip_value_,
  InventoryItem_skip_id_,
  InventoryItem_skip_value_,
  Product_skip_id_,
  Product_skip_value_,
  User_skip_id_,
  User_skip_value_,
  Warehouse_skip_id_,
  Warehouse_skip_value_,
  Category,
  InventoryAdjustment,
  InventoryItem,
  Product,
  User,
  Warehouse,
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
  readonly categories: InputDefinition<Category_skip_id_, Category_skip_value_>;
  readonly inventoryAdjustments: InputDefinition<
    InventoryAdjustment_skip_id_,
    InventoryAdjustment_skip_value_
  >;
  readonly inventoryItems: InputDefinition<
    InventoryItem_skip_id_,
    InventoryItem_skip_value_
  >;
  readonly products: InputDefinition<Product_skip_id_, Product_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
  readonly warehouses: InputDefinition<
    Warehouse_skip_id_,
    Warehouse_skip_value_
  >;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly adjustmentsByInventoryResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly getInventoryItemStoredResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listCategoriesResource: ResourceClass<GraphCollections, Json>;
  readonly listInventoryItemsResource: ResourceClass<GraphCollections, Json>;
  readonly listProductsResource: ResourceClass<GraphCollections, Json>;
  readonly listWarehousesResource: ResourceClass<GraphCollections, Json>;
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
      categories: new InputDefinition<Category_skip_id_, Category_skip_value_>(
        [],
      ),
      inventoryAdjustments: new InputDefinition<
        InventoryAdjustment_skip_id_,
        InventoryAdjustment_skip_value_
      >([]),
      inventoryItems: new InputDefinition<
        InventoryItem_skip_id_,
        InventoryItem_skip_value_
      >([]),
      products: new InputDefinition<Product_skip_id_, Product_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
      warehouses: new InputDefinition<
        Warehouse_skip_id_,
        Warehouse_skip_value_
      >([]),
    };
    this.resources = {
      adjustmentsByInventoryResource: AdjustmentsByInventoryResource,
      getInventoryItemStoredResource: GetInventoryItemStoredResource,
      listCategoriesResource: ListCategoriesResource,
      listInventoryItemsResource: ListInventoryItemsResource,
      listProductsResource: ListProductsResource,
      listWarehousesResource: ListWarehousesResource,
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
