import type { Post_skip_id_, Comment, Post } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListPostCommentsResourceInputs extends SharedCollections {
  readonly commentsByPost: EagerCollection<Post_skip_id_, Comment>;
}

export class ListPostCommentsResource implements Resource<ListPostCommentsResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListPostCommentsResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Comment> {
    return inputs.commentsByPost;
  }
}
