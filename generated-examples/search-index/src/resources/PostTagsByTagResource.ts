import type { TagIdKey, PostTag } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface PostTagsByTagResourceInputs extends SharedCollections {
  readonly postTagsByTag: EagerCollection<TagIdKey, PostTag>;
}

export class PostTagsByTagResource implements Resource<PostTagsByTagResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: PostTagsByTagResourceInputs,
    _context: Context,
  ): EagerCollection<TagIdKey, PostTag> {
    return inputs.postTagsByTag;
  }
}
