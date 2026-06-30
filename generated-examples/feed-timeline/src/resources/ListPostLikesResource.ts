import type { Post_skip_id_, Like, Post } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListPostLikesResourceInputs extends SharedCollections {
  readonly likesByPost: EagerCollection<Post_skip_id_, Like>;
}

export class ListPostLikesResource implements Resource<ListPostLikesResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListPostLikesResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Like> {
    return inputs.likesByPost;
  }
}
