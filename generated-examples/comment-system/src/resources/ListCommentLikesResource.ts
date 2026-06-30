import type { Comment_skip_id_, CommentLike, Comment } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListCommentLikesResourceInputs extends SharedCollections {
  readonly commentLikesByCommentId: EagerCollection<
    Comment_skip_id_,
    CommentLike
  >;
}

export class ListCommentLikesResource implements Resource<ListCommentLikesResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListCommentLikesResourceInputs,
    _context: Context,
  ): EagerCollection<Comment_skip_id_, CommentLike> {
    return inputs.commentLikesByCommentId;
  }
}
