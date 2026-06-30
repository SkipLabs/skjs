import { CommentWithLikeCountByIdMapper } from "../mappers/CommentWithLikeCountByIdMapper.js";
import type {
  Comment_skip_id_,
  CommentStored,
  LikeIncrement,
  CommentWithLikeCount,
  Comment,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetCommentResourceInputs extends SharedCollections {
  readonly comments: EagerCollection<Comment_skip_id_, CommentStored>;
  readonly likeCountByComment: EagerCollection<Comment_skip_id_, LikeIncrement>;
}

export class GetCommentResource implements Resource<GetCommentResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetCommentResourceInputs,
    _context: Context,
  ): EagerCollection<Comment_skip_id_, CommentWithLikeCount> {
    return inputs.comments.map(
      CommentWithLikeCountByIdMapper,
      inputs.likeCountByComment,
    );
  }
}
