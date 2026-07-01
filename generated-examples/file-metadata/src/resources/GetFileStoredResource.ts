import type {
  FileRecord_skip_id_,
  FileRecord_skip_value_,
  FileRecord,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetFileStoredResourceInputs extends SharedCollections {
  readonly files: EagerCollection<FileRecord_skip_id_, FileRecord_skip_value_>;
}

export class GetFileStoredResource implements Resource<GetFileStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetFileStoredResourceInputs,
    _context: Context,
  ): EagerCollection<FileRecord_skip_id_, FileRecord_skip_value_> {
    return inputs.files;
  }
}
