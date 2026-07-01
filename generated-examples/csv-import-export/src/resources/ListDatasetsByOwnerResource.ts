import type { User_skip_id_, DatasetByOwnerValue, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListDatasetsByOwnerResourceInputs extends SharedCollections {
  readonly datasetsByOwner: EagerCollection<User_skip_id_, DatasetByOwnerValue>;
}

export class ListDatasetsByOwnerResource implements Resource<ListDatasetsByOwnerResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListDatasetsByOwnerResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, DatasetByOwnerValue> {
    return inputs.datasetsByOwner;
  }
}
