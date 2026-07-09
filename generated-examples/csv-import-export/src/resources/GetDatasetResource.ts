import type { Dataset_skip_id_, DatasetStored, Dataset } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetDatasetResourceInputs extends SharedCollections {
  readonly datasets: EagerCollection<Dataset_skip_id_, DatasetStored>;
}

export class GetDatasetResource implements Resource<GetDatasetResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetDatasetResourceInputs,
    _context: Context,
  ): EagerCollection<Dataset_skip_id_, DatasetStored> {
    return inputs.datasets;
  }
}
