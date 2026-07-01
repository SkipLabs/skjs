import type {
  Dataset_skip_id_,
  DatasetRowByDatasetValue,
  Dataset,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListDatasetRowsResourceInputs extends SharedCollections {
  readonly rowsByDataset: EagerCollection<
    Dataset_skip_id_,
    DatasetRowByDatasetValue
  >;
}

export class ListDatasetRowsResource implements Resource<ListDatasetRowsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListDatasetRowsResourceInputs,
    _context: Context,
  ): EagerCollection<Dataset_skip_id_, DatasetRowByDatasetValue> {
    return inputs.rowsByDataset;
  }
}
