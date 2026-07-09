import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetPromotionResource } from "./resources/GetPromotionResource.js";
import { GetTaxRuleResource } from "./resources/GetTaxRuleResource.js";
import { ListPromotionsResource } from "./resources/ListPromotionsResource.js";
import { ListTaxRulesResource } from "./resources/ListTaxRulesResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Promotion_skip_id_,
  Promotion_skip_value_,
  TaxRule_skip_id_,
  TaxRule_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetPromotionParams,
  GetTaxRuleParams,
  ListPromotionsParams,
  ListTaxRulesParams,
  Promotion,
  TaxRule,
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
  readonly promotions: InputDefinition<
    Promotion_skip_id_,
    Promotion_skip_value_
  >;
  readonly taxRules: InputDefinition<TaxRule_skip_id_, TaxRule_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getPromotionResource: ResourceClass<
    GraphCollections,
    GetPromotionParams
  >;
  readonly getTaxRuleResource: ResourceClass<
    GraphCollections,
    GetTaxRuleParams
  >;
  readonly listPromotionsResource: ResourceClass<
    GraphCollections,
    ListPromotionsParams
  >;
  readonly listTaxRulesResource: ResourceClass<
    GraphCollections,
    ListTaxRulesParams
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
      promotions: new InputDefinition<
        Promotion_skip_id_,
        Promotion_skip_value_
      >([]),
      taxRules: new InputDefinition<TaxRule_skip_id_, TaxRule_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getPromotionResource: GetPromotionResource,
      getTaxRuleResource: GetTaxRuleResource,
      listPromotionsResource: ListPromotionsResource,
      listTaxRulesResource: ListTaxRulesResource,
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
