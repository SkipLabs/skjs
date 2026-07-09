import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetNoteResource } from "./resources/GetNoteResource.js";
import { ListNotesByOwnerResource } from "./resources/ListNotesByOwnerResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Note_skip_id_,
  Note_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListNotesParams,
  Note,
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
  readonly notes: InputDefinition<Note_skip_id_, Note_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getNoteResource: ResourceClass<GraphCollections, Json>;
  readonly listNotesByOwnerResource: ResourceClass<
    GraphCollections,
    ListNotesParams
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
      notes: new InputDefinition<Note_skip_id_, Note_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getNoteResource: GetNoteResource,
      listNotesByOwnerResource: ListNotesByOwnerResource,
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
