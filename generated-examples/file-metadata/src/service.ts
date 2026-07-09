import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetFileByHashResource } from "./resources/GetFileByHashResource.js";
import { GetFileResource } from "./resources/GetFileResource.js";
import { GetIndexStatsResource } from "./resources/GetIndexStatsResource.js";
import { ListFilesByOwnerResource } from "./resources/ListFilesByOwnerResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  IndexedFile_skip_id_,
  IndexedFile_skip_value_,
  User_skip_id_,
  User_skip_value_,
  IndexedFile,
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
  readonly files: InputDefinition<
    IndexedFile_skip_id_,
    IndexedFile_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getFileByHashResource: ResourceClass<GraphCollections, Json>;
  readonly getFileResource: ResourceClass<GraphCollections, Json>;
  readonly getIndexStatsResource: ResourceClass<GraphCollections, Json>;
  readonly listFilesByOwnerResource: ResourceClass<GraphCollections, Json>;
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
      files: new InputDefinition<IndexedFile_skip_id_, IndexedFile_skip_value_>(
        [],
      ),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getFileByHashResource: GetFileByHashResource,
      getFileResource: GetFileResource,
      getIndexStatsResource: GetIndexStatsResource,
      listFilesByOwnerResource: ListFilesByOwnerResource,
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
