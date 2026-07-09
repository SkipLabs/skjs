import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetEntryResource } from "./resources/GetEntryResource.js";
import { GetEntryStoredResource } from "./resources/GetEntryStoredResource.js";
import { ListEntriesResource } from "./resources/ListEntriesResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetEntryParams,
  KvEntry,
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
  readonly entries: InputDefinition<KvEntry_skip_id_, KvEntry_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getEntryResource: ResourceClass<GraphCollections, GetEntryParams>;
  readonly getEntryStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listEntriesResource: ResourceClass<GraphCollections, Json>;
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
      entries: new InputDefinition<KvEntry_skip_id_, KvEntry_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getEntryResource: GetEntryResource,
      getEntryStoredResource: GetEntryStoredResource,
      listEntriesResource: ListEntriesResource,
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
