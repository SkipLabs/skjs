import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { EventsByPolicyResource } from "./resources/EventsByPolicyResource.js";
import { GetPolicyResource } from "./resources/GetPolicyResource.js";
import { ListAllConsumptionEventsResource } from "./resources/ListAllConsumptionEventsResource.js";
import { ListConsumptionEventsResource } from "./resources/ListConsumptionEventsResource.js";
import { ListPoliciesResource } from "./resources/ListPoliciesResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  ConsumptionEvent_skip_id_,
  ConsumptionEvent_skip_value_,
  Policy_skip_id_,
  Policy_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListConsumptionEventsParams,
  ListPoliciesParams,
  ConsumptionEvent,
  Policy,
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
  readonly consumptionEvents: InputDefinition<
    ConsumptionEvent_skip_id_,
    ConsumptionEvent_skip_value_
  >;
  readonly policies: InputDefinition<Policy_skip_id_, Policy_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly eventsByPolicyResource: ResourceClass<GraphCollections, Json>;
  readonly getPolicyResource: ResourceClass<GraphCollections, Json>;
  readonly listAllConsumptionEventsResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listConsumptionEventsResource: ResourceClass<
    GraphCollections,
    ListConsumptionEventsParams
  >;
  readonly listPoliciesResource: ResourceClass<
    GraphCollections,
    ListPoliciesParams
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
      consumptionEvents: new InputDefinition<
        ConsumptionEvent_skip_id_,
        ConsumptionEvent_skip_value_
      >([]),
      policies: new InputDefinition<Policy_skip_id_, Policy_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      eventsByPolicyResource: EventsByPolicyResource,
      getPolicyResource: GetPolicyResource,
      listAllConsumptionEventsResource: ListAllConsumptionEventsResource,
      listConsumptionEventsResource: ListConsumptionEventsResource,
      listPoliciesResource: ListPoliciesResource,
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
