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
  Json,
} from "@skipruntime/core";

export interface GetCommentLikeStoredResourceInputs extends SharedCollections {
  readonly commentLikes: EagerCollection<
    CommentLike_skip_id_,
    CommentLike_skip_value_
  >;
}

export class GetCommentLikeStoredResource implements Resource<GetCommentLikeStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetCommentLikeStoredResourceInputs,
    _context: Context,
  ): EagerCollection<CommentLike_skip_id_, CommentLike_skip_value_> {
    return inputs.commentLikes;
  }
}
