import type {
  IndexedFile_skip_id_,
  IndexedFile_skip_value_,
  IndexedFile,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetFileResourceInputs extends SharedCollections {
  readonly files: EagerCollection<
    IndexedFile_skip_id_,
    IndexedFile_skip_value_
  >;
}

export class GetFileResource implements Resource<GetFileResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetFileResourceInputs,
    _context: Context,
  ): EagerCollection<IndexedFile_skip_id_, IndexedFile_skip_value_> {
    return inputs.files;
  }
}
