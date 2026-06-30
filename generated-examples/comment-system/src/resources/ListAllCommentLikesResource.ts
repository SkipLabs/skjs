import type {
  CommentLike_skip_id_,
  CommentLike_skip_value_,
  CommentLike,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListAllCommentLikesResourceInputs extends SharedCollections {
  readonly commentLikes: EagerCollection<
    CommentLike_skip_id_,
    CommentLike_skip_value_
  >;
}

export class ListAllCommentLikesResource implements Resource<ListAllCommentLikesResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListAllCommentLikesResourceInputs,
    _context: Context,
  ): EagerCollection<CommentLike_skip_id_, CommentLike_skip_value_> {
    return inputs.commentLikes;
  }
}
