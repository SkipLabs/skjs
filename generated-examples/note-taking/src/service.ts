import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetNoteResource } from "./resources/GetNoteResource.js";
import { GetNoteStoredResource } from "./resources/GetNoteStoredResource.js";
import { ListNotesByOwnerResource } from "./resources/ListNotesByOwnerResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Note_skip_id_,
  Note_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetNoteParams,
  Note,
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
  readonly notes: InputDefinition<Note_skip_id_, Note_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getNoteResource: ResourceClass<GraphCollections, GetNoteParams>;
  readonly getNoteStoredResource: ResourceClass<GraphCollections, Json>;
  readonly listNotesByOwnerResource: ResourceClass<GraphCollections, Json>;
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
      notes: new InputDefinition<Note_skip_id_, Note_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getNoteResource: GetNoteResource,
      getNoteStoredResource: GetNoteStoredResource,
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
