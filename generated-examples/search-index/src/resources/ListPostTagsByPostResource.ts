import type { PostIdKey, PostTag } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListPostTagsByPostResourceInputs extends SharedCollections {
  readonly postTagsByPost: EagerCollection<PostIdKey, PostTag>;
}

export class ListPostTagsByPostResource implements Resource<ListPostTagsByPostResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListPostTagsByPostResourceInputs,
    _context: Context,
  ): EagerCollection<PostIdKey, PostTag> {
    return inputs.postTagsByPost;
  }
}
