import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetDatasetResource } from "./resources/GetDatasetResource.js";
import { GetDatasetRowCountResource } from "./resources/GetDatasetRowCountResource.js";
import { GetDatasetRowResource } from "./resources/GetDatasetRowResource.js";
import { GetImportJobResource } from "./resources/GetImportJobResource.js";
import { ListDatasetRowsResource } from "./resources/ListDatasetRowsResource.js";
import { ListDatasetsByOwnerResource } from "./resources/ListDatasetsByOwnerResource.js";
import { ListImportJobsResource } from "./resources/ListImportJobsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  DatasetRow_skip_id_,
  DatasetRow_skip_value_,
  Dataset_skip_id_,
  DatasetStored,
  ImportJob_skip_id_,
  ImportJob_skip_value_,
  User_skip_id_,
  User_skip_value_,
  DatasetRow,
  Dataset,
  ImportJob,
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
  readonly datasetRows: InputDefinition<
    DatasetRow_skip_id_,
    DatasetRow_skip_value_
  >;
  readonly datasets: InputDefinition<Dataset_skip_id_, DatasetStored>;
  readonly importJobs: InputDefinition<
    ImportJob_skip_id_,
    ImportJob_skip_value_
  >;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getDatasetResource: ResourceClass<GraphCollections, Json>;
  readonly getDatasetRowCountResource: ResourceClass<GraphCollections, Json>;
  readonly getDatasetRowResource: ResourceClass<GraphCollections, Json>;
  readonly getImportJobResource: ResourceClass<GraphCollections, Json>;
  readonly listDatasetRowsResource: ResourceClass<GraphCollections, Json>;
  readonly listDatasetsByOwnerResource: ResourceClass<GraphCollections, Json>;
  readonly listImportJobsResource: ResourceClass<GraphCollections, Json>;
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
      datasetRows: new InputDefinition<
        DatasetRow_skip_id_,
        DatasetRow_skip_value_
      >([]),
      datasets: new InputDefinition<Dataset_skip_id_, DatasetStored>([]),
      importJobs: new InputDefinition<
        ImportJob_skip_id_,
        ImportJob_skip_value_
      >([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getDatasetResource: GetDatasetResource,
      getDatasetRowCountResource: GetDatasetRowCountResource,
      getDatasetRowResource: GetDatasetRowResource,
      getImportJobResource: GetImportJobResource,
      listDatasetRowsResource: ListDatasetRowsResource,
      listDatasetsByOwnerResource: ListDatasetsByOwnerResource,
      listImportJobsResource: ListImportJobsResource,
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
