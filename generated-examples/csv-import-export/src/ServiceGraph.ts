import { DatasetByOwnerMapper } from "./mappers/DatasetByOwnerMapper.js";
import { DatasetRowByDatasetMapper } from "./mappers/DatasetRowByDatasetMapper.js";
import { DatasetRowCountByDatasetMapper } from "./mappers/DatasetRowCountByDatasetMapper.js";
import { ImportJobByDatasetMapper } from "./mappers/ImportJobByDatasetMapper.js";
import { SumReducer } from "./reducers/SumReducer.js";
import type {
  DatasetRow_skip_id_,
  DatasetRow,
  DatasetRow_skip_value_,
  Dataset_skip_id_,
  Dataset,
  DatasetStored,
  ImportJob_skip_id_,
  ImportJob,
  ImportJob_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  DatasetByOwnerValue,
  ImportJobByDatasetValue,
  DatasetRowCountAccum,
  DatasetRowByDatasetValue,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly datasetRows: EagerCollection<
    DatasetRow_skip_id_,
    DatasetRow_skip_value_
  >;
  readonly datasets: EagerCollection<Dataset_skip_id_, DatasetStored>;
  readonly importJobs: EagerCollection<
    ImportJob_skip_id_,
    ImportJob_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly datasetRows: EagerCollection<
    DatasetRow_skip_id_,
    DatasetRow_skip_value_
  >;
  readonly datasets: EagerCollection<Dataset_skip_id_, DatasetStored>;
  readonly datasetsByOwner: EagerCollection<User_skip_id_, DatasetByOwnerValue>;
  readonly importJobs: EagerCollection<
    ImportJob_skip_id_,
    ImportJob_skip_value_
  >;
  readonly jobsByDataset: EagerCollection<
    Dataset_skip_id_,
    ImportJobByDatasetValue
  >;
  readonly rowCountByDataset: EagerCollection<
    Dataset_skip_id_,
    DatasetRowCountAccum
  >;
  readonly rowsByDataset: EagerCollection<
    Dataset_skip_id_,
    DatasetRowByDatasetValue
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const datasetsByOwner = inputs.datasets.map(DatasetByOwnerMapper);
  const jobsByDataset = inputs.importJobs.map(ImportJobByDatasetMapper);
  const output_datasetRows = inputs.datasetRows;
  const output_datasets = inputs.datasets;
  const output_datasetsByOwner = datasetsByOwner;
  const output_importJobs = inputs.importJobs;
  const output_jobsByDataset = jobsByDataset;
  const rowCountEventsByDataset = inputs.datasetRows.map(
    DatasetRowCountByDatasetMapper,
  );
  const rowCountByDataset = rowCountEventsByDataset.reduce(SumReducer);
  const output_rowCountByDataset = rowCountByDataset;
  const rowsByDataset = inputs.datasetRows.map(DatasetRowByDatasetMapper);
  const output_rowsByDataset = rowsByDataset;
  const output_users = inputs.users;
  return {
    datasetRows: output_datasetRows,
    datasets: output_datasets,
    datasetsByOwner: output_datasetsByOwner,
    importJobs: output_importJobs,
    jobsByDataset: output_jobsByDataset,
    rowCountByDataset: output_rowCountByDataset,
    rowsByDataset: output_rowsByDataset,
    users: output_users,
  };
}
