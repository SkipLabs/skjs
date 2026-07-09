import type {
  Dataset_skip_id_,
  DatasetRowCountAccum,
  Dataset,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetDatasetRowCountResourceInputs extends SharedCollections {
  readonly rowCountByDataset: EagerCollection<
    Dataset_skip_id_,
    DatasetRowCountAccum
  >;
}

export class GetDatasetRowCountResource implements Resource<GetDatasetRowCountResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetDatasetRowCountResourceInputs,
    _context: Context,
  ): EagerCollection<Dataset_skip_id_, DatasetRowCountAccum> {
    return inputs.rowCountByDataset;
  }
}
