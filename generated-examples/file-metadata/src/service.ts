import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetFileResource } from "./resources/GetFileResource.js";
import { GetFileStoredResource } from "./resources/GetFileStoredResource.js";
import { GetIndexStatsResource } from "./resources/GetIndexStatsResource.js";
import { ListFilesResource } from "./resources/ListFilesResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  FileRecord_skip_id_,
  FileRecord_skip_value_,
  User_skip_id_,
  User_skip_value_,
  GetFileParams,
  GetIndexStatsParams,
  ListFilesParams,
  FileRecord,
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
  readonly files: InputDefinition<FileRecord_skip_id_, FileRecord_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getFileResource: ResourceClass<GraphCollections, GetFileParams>;
  readonly getFileStoredResource: ResourceClass<GraphCollections, Json>;
  readonly getIndexStatsResource: ResourceClass<
    GraphCollections,
    GetIndexStatsParams
  >;
  readonly listFilesResource: ResourceClass<GraphCollections, ListFilesParams>;
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
      files: new InputDefinition<FileRecord_skip_id_, FileRecord_skip_value_>(
        [],
      ),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getFileResource: GetFileResource,
      getFileStoredResource: GetFileStoredResource,
      getIndexStatsResource: GetIndexStatsResource,
      listFilesResource: ListFilesResource,
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
