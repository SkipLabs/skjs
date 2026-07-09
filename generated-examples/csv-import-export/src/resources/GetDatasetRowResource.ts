import type {
  DatasetRow_skip_id_,
  DatasetRow_skip_value_,
  DatasetRow,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetDatasetRowResourceInputs extends SharedCollections {
  readonly datasetRows: EagerCollection<
    DatasetRow_skip_id_,
    DatasetRow_skip_value_
  >;
}

export class GetDatasetRowResource implements Resource<GetDatasetRowResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetDatasetRowResourceInputs,
    _context: Context,
  ): EagerCollection<DatasetRow_skip_id_, DatasetRow_skip_value_> {
    return inputs.datasetRows;
  }
}
