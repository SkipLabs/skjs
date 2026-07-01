import type { OwnerIdKey, IndexedFile } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListFilesByOwnerResourceInputs extends SharedCollections {
  readonly filesByOwner: EagerCollection<OwnerIdKey, IndexedFile>;
}

export class ListFilesByOwnerResource implements Resource<ListFilesByOwnerResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListFilesByOwnerResourceInputs,
    _context: Context,
  ): EagerCollection<OwnerIdKey, IndexedFile> {
    return inputs.filesByOwner;
  }
}
