import type { Post_skip_id_, PostStored, Post } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetPostStoredResourceInputs extends SharedCollections {
  readonly postsStored: EagerCollection<Post_skip_id_, PostStored>;
}

export class GetPostStoredResource implements Resource<GetPostStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetPostStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, PostStored> {
    return inputs.postsStored;
  }
}
