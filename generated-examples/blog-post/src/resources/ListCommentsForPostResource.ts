import type { Post_skip_id_, Comment, Post } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface ListCommentsForPostResourceInputs extends SharedCollections {
  readonly commentsByPost: EagerCollection<Post_skip_id_, Comment>;
}

export class ListCommentsForPostResource implements Resource<ListCommentsForPostResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: ListCommentsForPostResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, Comment> {
    return inputs.commentsByPost;
  }
}
