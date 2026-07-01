import type { OwnerHashKey, IndexedFile } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetFileByHashResourceInputs extends SharedCollections {
  readonly filesByOwnerHash: EagerCollection<OwnerHashKey, IndexedFile>;
}

export class GetFileByHashResource implements Resource<GetFileByHashResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetFileByHashResourceInputs,
    _context: Context,
  ): EagerCollection<OwnerHashKey, IndexedFile> {
    return inputs.filesByOwnerHash;
  }
}
