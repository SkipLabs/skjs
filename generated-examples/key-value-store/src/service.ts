import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetEntryResource } from "./resources/GetEntryResource.js";
import { ListEntriesResource } from "./resources/ListEntriesResource.js";
import type {
  KvEntry_skip_id_,
  KvEntry_skip_value_,
  ListEntriesParams,
  KvEntry,
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
  readonly entries: InputDefinition<KvEntry_skip_id_, KvEntry_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getEntryResource: ResourceClass<GraphCollections, Json>;
  readonly listEntriesResource: ResourceClass<
    GraphCollections,
    ListEntriesParams
  >;
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
      entries: new InputDefinition<KvEntry_skip_id_, KvEntry_skip_value_>([]),
    };
    this.resources = {
      getEntryResource: GetEntryResource,
      listEntriesResource: ListEntriesResource,
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
