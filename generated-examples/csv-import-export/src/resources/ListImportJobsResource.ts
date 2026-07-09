import type {
  Dataset_skip_id_,
  ImportJobByDatasetValue,
  Dataset,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListImportJobsResourceInputs extends SharedCollections {
  readonly jobsByDataset: EagerCollection<
    Dataset_skip_id_,
    ImportJobByDatasetValue
  >;
}

export class ListImportJobsResource implements Resource<ListImportJobsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListImportJobsResourceInputs,
    _context: Context,
  ): EagerCollection<Dataset_skip_id_, ImportJobByDatasetValue> {
    return inputs.jobsByDataset;
  }
}
