import { FilterCommentLikesByCommentMapper } from "../mappers/FilterCommentLikesByCommentMapper.js";
import type {
  Comment_skip_id_,
  CommentLike,
  ListCommentLikesParams,
  Comment,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListCommentLikesResourceInputs extends SharedCollections {
  readonly commentLikesByComment: EagerCollection<
    Comment_skip_id_,
    CommentLike
  >;
}

export class ListCommentLikesResource implements Resource<ListCommentLikesResourceInputs> {
  private readonly commentId: string;

  constructor(params: ListCommentLikesParams) {
    this.commentId = params.commentId;
  }

  instantiate(
    inputs: ListCommentLikesResourceInputs,
    _context: Context,
  ): EagerCollection<Comment_skip_id_, CommentLike> {
    return inputs.commentLikesByComment.map(
      FilterCommentLikesByCommentMapper,
      this.commentId,
    );
  }
}
