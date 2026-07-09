import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetMyInteractionResource } from "./resources/GetMyInteractionResource.js";
import { GetProductResource } from "./resources/GetProductResource.js";
import { GetProductStoredResource } from "./resources/GetProductStoredResource.js";
import { ListMyInteractionsResource } from "./resources/ListMyInteractionsResource.js";
import { ListProductsResource } from "./resources/ListProductsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Interaction_skip_id_,
  Interaction_skip_value_,
  Product_skip_id_,
  ProductStored,
  User_skip_id_,
  User_skip_value_,
  GetMyInteractionParams,
  GetProductParams,
  ListMyInteractionsParams,
  ListProductsParams,
  Interaction,
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
  readonly interactions: InputDefinition<
    Interaction_skip_id_,
    Interaction_skip_value_
  >;
  readonly products: InputDefinition<Product_skip_id_, ProductStored>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getMyInteractionResource: ResourceClass<
    GraphCollections,
    GetMyInteractionParams
  >;
  readonly getProductResource: ResourceClass<
    GraphCollections,
    GetProductParams
  >;
  readonly getProductStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listMyInteractionsResource: ResourceClass<
    GraphCollections,
    ListMyInteractionsParams
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
      interactions: new InputDefinition<
        Interaction_skip_id_,
        Interaction_skip_value_
      >([]),
      products: new InputDefinition<Product_skip_id_, ProductStored>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getMyInteractionResource: GetMyInteractionResource,
      getProductResource: GetProductResource,
      getProductStoredResource: GetProductStoredResource,
      listMyInteractionsResource: ListMyInteractionsResource,
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
