import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetInteractionResource } from "./resources/GetInteractionResource.js";
import { GetProductResource } from "./resources/GetProductResource.js";
import { InteractionsByUserResource } from "./resources/InteractionsByUserResource.js";
import { ListCategoriesResource } from "./resources/ListCategoriesResource.js";
import { ListMyInteractionsResource } from "./resources/ListMyInteractionsResource.js";
import { ListProductsResource } from "./resources/ListProductsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Category_skip_id_,
  Category_skip_value_,
  Interaction_skip_id_,
  Interaction_skip_value_,
  Product_skip_id_,
  Product_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListMyInteractionsParams,
  ListProductsParams,
  Category,
  Interaction,
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
  readonly categories: InputDefinition<Category_skip_id_, Category_skip_value_>;
  readonly interactions: InputDefinition<
    Interaction_skip_id_,
    Interaction_skip_value_
  >;
  readonly products: InputDefinition<Product_skip_id_, Product_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getInteractionResource: ResourceClass<GraphCollections, Json>;
  readonly getProductResource: ResourceClass<GraphCollections, Json>;
  readonly interactionsByUserResource: ResourceClass<GraphCollections, Json>;
  readonly listCategoriesResource: ResourceClass<GraphCollections, Json>;
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

  constructor() {
    this.inputs = {
      categories: new InputDefinition<Category_skip_id_, Category_skip_value_>(
        [],
      ),
      interactions: new InputDefinition<
        Interaction_skip_id_,
        Interaction_skip_value_
      >([]),
      products: new InputDefinition<Product_skip_id_, Product_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getInteractionResource: GetInteractionResource,
      getProductResource: GetProductResource,
      interactionsByUserResource: InteractionsByUserResource,
      listCategoriesResource: ListCategoriesResource,
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
