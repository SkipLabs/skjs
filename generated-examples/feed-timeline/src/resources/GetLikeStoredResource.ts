import type { LikeKey, LikeStored } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetLikeStoredResourceInputs extends SharedCollections {
  readonly likes: EagerCollection<LikeKey, LikeStored>;
}

export class GetLikeStoredResource implements Resource<GetLikeStoredResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetLikeStoredResourceInputs,
    _context: Context,
  ): EagerCollection<LikeKey, LikeStored> {
    return inputs.likes;
  }
}
